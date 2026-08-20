/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * AEXT calculus-based array solver.
 *
 * Implements the AEXT decision procedure for the extensional theory of arrays,
 * as described in:
 *   R. Brummayer, A. Biere: "Lemmas on Demand for the Extensional Theory of
 *   Arrays", JSAT 2009.
 *
 * The key idea is to propagate existing reads through store chains guided by
 * the current equality engine state, tracking which reads reach which arrays.
 * Lemmas are only generated when conflicts are detected:
 *   - CongR: two reads reach the same array at the same index with different
 *     values
 *   - AccessStore: a read reaches a store with a matching index but
 *     inconsistent value
 * Lemmas use existing terms only (no new select terms are introduced) and are
 * guarded by path conditions (index disequalities accumulated along the
 * propagation path).
 *
 * Path conditions are reconstructed lazily: during propagation, only
 * lightweight predecessor edges are recorded.  When a conflict is detected,
 * the path is walked backwards to extract the actual conditions.  This avoids
 * O(depth^2) vector copying during propagation (following Bitwuzla's approach).
 *
 * Calculus rules implemented (from the AEXT paper, Figures 1-2):
 *   InitR/InitW  - register reads and virtual writes
 *   RowD/RowU    - propagate reads down/up through stores
 *   CongR        - congruence conflict detection
 *   EqR/EqL      - propagate reads across array equalities (via EE)
 *   DisEq        - extensionality witness for array disequalities
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__AEXT_SOLVER_H
#define CVC5__THEORY__ARRAYS__AEXT_SOLVER_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "theory/arrays/array_solver.h"
#include "theory/arrays/inference_manager.h"
#include "theory/arrays/path_edge.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * Array solver based on the AEXT calculus.
 *
 * This solver is used as a sub-solver within TheoryArrays when the option
 * --arrays-solver=aext is set. It replaces the default eager Row lemma
 * generation with a propagation-based approach that only generates lemmas
 * on conflicts.
 */
class AextArraySolver : public ArraySolver
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  AextArraySolver(Env& env,
                  TheoryState& state,
                  InferenceManager& im,
                  Valuation valuation,
                  eq::EqualityEngine& mayEqualEE,
                  DefValMap& defValues,
                  context::CDO<bool>& sharedTerms);
  ~AextArraySolver() override;

  //--------------------------------- ArraySolver interface
  void finishInit(eq::EqualityEngine* ee) override;
  void preRegisterSelect(TNode node) override;
  void preRegisterStore(TNode node) override;
  void preRegisterStoreAll(TNode node) override;
  void eqNotifyMerge(TNode a, TNode b) override;
  void postCheck(Theory::Effort level) override;
  void notifyArrayDisequality(TNode a, TNode b, TNode fact) override;
  void computeRelevantTerms(std::set<Node>& termSet) override;
  void augmentModelSelects(std::map<Node, std::vector<Node>>& selects,
                           const std::set<Node>& termSet) override;
  void computeCareGraph(AddCarePairFn addCarePair) override;
  std::string identify() const override;
  //--------------------------------- end ArraySolver interface

 private:
  /**
   * A read that has been propagated to a specific array during check().
   * Path conditions are not stored eagerly; they are reconstructed on
   * demand from d_propEdgeMaps when a conflict is detected.
   */
  struct PropagatedRead
  {
    TNode select; /**< the original SELECT term */
    TNode index;  /**< the read index */
  };

  //--------------------------------- propagation (core AEXT calculus)
  /**
   * Main theory check, called from postCheck().
   * For each registered select, propagates it through store chains (RowD/RowU)
   * and checks for conflicts (CongR/AccessStore). Then handles disequalities
   * (DisEq).
   */
  void check(Theory::Effort level);
  /**
   * Propagate a single select through store chains (RowD/RowU).
   */
  void checkAccess(TNode select);
  /**
   * Find a path from a select's starting array to a target array
   * representative through the store graph (RowD/RowU edges), and
   * extract the path conditions.
   *
   * @param linkEntryToTargetRep whether to emit the guard tying the array the
   * path arrives at to targetRep. Callers that go on to add a stronger link
   * for that same array -- AccessStore and AccessConstArray, which add
   * `entryArray = store` -- should pass false: the rep equality is then
   * redundant, unused by the proof reconstruction, and only weakens the
   * lemma. CongR must pass true, because convertCongruence bridges its two
   * path endpoints through exactly these array equalities.
   */
  TNode findPathConditions(TNode select,
                           TNode targetRep,
                           std::vector<Node>& conds,
                           std::vector<PathEdge>* edges = nullptr,
                           bool linkEntryToTargetRep = true);
  /**
   * RIntro2 theory propagation.
   */
  void propagateRIntro2();
  /**
   * Process array disequalities (DisEq rule).
   */
  void checkDisequalities();
  /**
   * Build the parent store map for the current check.
   */
  void buildParentMap();
  /** Compute active array representatives for RowU gating. */
  void computeActiveArrays();
  //--------------------------------- end propagation

  /**
   * Lightweight merge for model construction support.
   * Maintains d_mayEqualEqualityEngine and d_defValues without
   * generating Row lemmas or updating d_infoMap.
   */
  void mergeArraysModelOnly(TNode a, TNode b);

  /** All registered SELECT terms (context-dependent) */
  context::CDList<TNode> d_selects;
  /** All registered STORE terms (context-dependent) */
  context::CDList<TNode> d_stores;
  /** Array disequalities in current context */
  context::CDList<Node> d_arrayDisequalities;
  /** Disequalities for which a witness has already been generated */
  NodeSet d_witnessDiseqs;
  /**
   * Per canonical (rep_a, rep_b) pair, the number of extensionality witness
   * lemmas emitted so far. Once a cap is reached, further facts mapping to
   * the same pair are skipped: they are semantically covered by one of the
   * already-emitted lemmas, and emitting more adds SAT clause bloat without
   * new distinguishing information.
   *
   * This must be context-dependent. The coverage argument is only valid in
   * an equality engine state where the two facts really do share a
   * representative pair, i.e. exactly the scope in which the count was
   * incremented. A non-context-dependent counter keeps counting across
   * backtracking, and would then suppress the witness for a fact in a later
   * branch where no emitted lemma covers it -- an unsound "sat".
   */
  context::CDHashMap<Node, uint32_t> d_witnessRepPairCount;
  /**
   * Lemma deduplication caches (context-dependent). There is one cache per
   * lemma kind: the conclusions of different kinds are not syntactically
   * disjoint, so a single shared cache aliases across kinds. In particular an
   * index split (= i j) where i and j are themselves SELECT terms is
   * indistinguishable from a CongR conclusion, and if the split were cached
   * first then CongR for that read pair would be silently suppressed while
   * checkAccess still stops propagating the read, leaving the read equality
   * unenforced.
   *
   * The CongR cache is keyed on the full lemma (exp => conc), not on conc
   * alone. One conclusion has one guard set per pair of propagation paths, and
   * keying on the conclusion emits only whichever pair was found first. CongR
   * emits a lemma and nothing else, so the conclusion is not made true in the
   * current context: the SAT solver may satisfy that clause by falsifying a
   * literal of the guard -- possibly by unit propagation at the current level,
   * without any backtracking that would clear this cache -- while a second
   * store path still connects the two reads. The next check() re-detects the
   * conflict, hits the cache, emits nothing, and reports a spurious sat.
   * (Keying on the lemma cannot be delegated to
   * TheoryInferenceManager::d_lemmasSent: the arrays inference manager is
   * constructed with cacheLemmas=false.)
   */
  NodeSet d_congruenceLemmaCache;
  /** Deduplication cache for RIntro2 lemmas, keyed on the conclusion. */
  NodeSet d_rintro2LemmaCache;
  /** Deduplication cache for index split lemmas, keyed on the split. */
  NodeSet d_indexSplitCache;

  //--------------------------------- per-check data structures
  std::vector<std::pair<TNode, TNode>> d_pendingCarePairs;
  std::unordered_set<Node> d_pendingCarePairCache;
  std::unordered_set<Node> d_checkAccessCache;
  std::unordered_map<TNode, std::unordered_map<TNode, PropagatedRead>>
      d_arrayModels;
  std::unordered_map<TNode, std::vector<TNode>> d_parentStores;
  /**
   * Representatives from which RowU (upward propagation into parent stores) is
   * allowed. Built by computeActiveArrays: the representative of every STORE
   * term whose equivalence class has more than one member, closed downwards
   * through store bases.
   *
   * WHY GATING HERE IS SOUND. Suppressing upward propagation is where a wrong
   * "sat" would come from, so the argument is spelled out.
   *
   * First, what exclusion means. If rep(a) is absent from this set then every
   * parent store s of rep(a) -- every s in d_stores with rep(s[0]) == rep(a) --
   * is alone in its class. Contrapositive: if some parent store s had
   * |class(rep(s))| > 1 then rep(s) would be in the seed, and processing it in
   * the downward closure would find s (a STORE) in its own class and insert
   * rep(s[0]) == rep(a).
   *
   * Now take a read r = select(x, i) with rep(x) == rep(a), and a parent store
   * s = store(b, j, v) with rep(b) == rep(a). Step 4 of checkAccess would only
   * push s when rep(i) != rep(j). RowU exists to let r meet other terms at
   * class(rep(s)); with that class a singleton {s}, each possibility is
   * covered without it:
   *
   *  1. CongR. Any read at class(rep(s)) is a select whose array lies in
   *     {s}, so it is syntactically select(s, i') -- including the virtual
   *     InitW read select(s, j). CongR against r needs rep(i') == rep(i),
   *     which differs from rep(j); so RowD at class(rep(s)) pushes s[0], and
   *     select(s, i') descends into class(rep(b)) == rep(a), where r is
   *     already recorded. The same pair is compared, one level lower.
   *  2. AccessStore. The only STORE in class(rep(s)) is s, and firing would
   *     need rep(i) == rep(s[1]) == rep(j), which contradicts the condition
   *     under which Step 4 propagates at all.
   *  3. AccessConstArray. class(rep(s)) holds no STORE_ALL: it holds only s,
   *     which is a STORE.
   *  4. Stores above s. If any ancestor store's class is non-trivial, the
   *     downward closure marks every store base beneath it, rep(a) included,
   *     so the gate would not have blocked. If every ancestor is a singleton
   *     too, cases 1-3 apply at each level and the descent in case 1 carries
   *     the partner read all the way down to rep(a).
   *
   * Note findPathConditions deliberately does NOT apply this gate to its BFS.
   * That asymmetry is safe in this direction only: the BFS just has to find
   * some valid RowD/RowU path justifying a conflict that forward propagation
   * already found, and RowU is sound with or without the gate. Gating there
   * could only make the search fail to find a path, never make it return an
   * invalid one.
   *
   * HISTORY. 7288daf85d replaced this with a gate on read-presence at the
   * parent and mirrored it into findPathConditions; e52a6d4934 reverted it.
   * That gate is not implied by the structure above -- absence of a read at
   * the parent right now says nothing about case 1's descent -- and it broke
   * ext27.btor.smt2, whose only reads are the virtual InitW ones. Counting
   * those reads instead made the gate vacuous. Prefer this structural
   * condition over any read-presence test.
   */
  std::unordered_set<TNode> d_activeArrays;
  //--------------------------------- end per-check data structures

  //--------------------------------- statistics
  IntStat d_numCongruenceLemmas;
  IntStat d_numAccessStoreLemmas;
  IntStat d_numDisequalityLemmas;
  IntStat d_numConstArrayLemmas;
  IntStat d_numCheckCalls;
  IntStat d_numPropagationsDown;
  IntStat d_numPropagationsUp;
  IntStat d_numRIntro2Propagations;
  //--------------------------------- end statistics
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__AEXT_SOLVER_H */

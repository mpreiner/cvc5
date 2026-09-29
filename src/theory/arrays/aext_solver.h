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
  void eqNotifyMergeNonArray(TNode a, TNode b) override;
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
   *
   * The propagation state persists between checks. A check rebuilds it from
   * scratch only when a pop has undone part of what it records; otherwise it
   * applies what changed since the last check (see applyDelta).
   */
  void check(Theory::Effort level);
  /**
   * Bring the propagation state up to date with everything registered and
   * merged since the last completed check, which must not have been undone by
   * a pop. See the invariants on the propagation state below for what each
   * kind of change requires.
   *
   * @param wasActive d_activeArrays as of the last completed check
   */
  void applyDelta(const std::unordered_set<TNode>& wasActive);
  /**
   * Propagate a single select through store chains (RowD/RowU), starting at
   * its own array. Does nothing for a select already propagated since
   * d_checkAccessCache was last cleared.
   */
  void checkAccess(TNode select);
  /**
   * Propagate select from the array start through store chains (RowD/RowU),
   * recording it in d_arrayModels at every array representative it reaches
   * and checking CongR, AccessStore and AccessConstArray there. The walk stops
   * at a representative where a read with the same index representative is
   * already recorded, after checking CongR against it.
   *
   * @param recordedAtStart whether select is already the read recorded at
   * start for its index class. It is then not recorded again, and everything
   * else is re-checked there: this resumes a read whose class changed.
   */
  void propagateFrom(TNode select, TNode start, bool recordedAtStart = false);
  /**
   * CongR: arriving has reached arrayRep, where existing is recorded for the
   * same index class. Unless the two are already equal, send the lemma that
   * they are, guarded by the paths that brought both there.
   */
  void checkCongruence(const PropagatedRead& arriving,
                       const PropagatedRead& existing,
                       TNode arrayRep);
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
   *
   * @return the array the path arrives at, or a null TNode if no path was
   * found. A null return should not happen -- the BFS explores a superset of
   * what forward propagation reached -- and asserts in a debug build, but it
   * is reported rather than walked off the end of, so a production build
   * degrades to dropping the lemma. On failure `conds` and `edges` are left
   * exactly as they were passed in, which matters for CongR: it fills one
   * `conds` from two calls.
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

  //--------------------------------- checking incrementality
  /**
   * Under --arrays-aext-check-incremental, record that a lemma guard => t1 =
   * t2 was derived on the current path. checkIncrementalState counts on
   * these to tell whether two terms the incremental state never compared
   * directly are nonetheless forced equal.
   */
  void recordJoin(TNode t1, TNode t2, TNode guard);
  /**
   * Whether some literal of guard (a conjunction, or a single literal) is
   * false in the current equality engine state.
   */
  bool isGuardFalsified(TNode guard) const;
  /**
   * Under --arrays-aext-check-incremental, after every incremental check:
   * rebuild the propagation state from scratch, without sending anything, and
   * fail hard unless the incremental state agrees with it -- it records the
   * same (array, index) slots, every pair of terms the rebuild would have to
   * equate (two reads meeting at a slot, a read and a store value or constant
   * array default it matches) is joined by equality or by a recorded lemma
   * whose guard nothing has falsified, and every undecided index pair the
   * rebuild requests is pending. Occupants may legitimately differ: which of
   * several reads reaching a slot records itself there depends on the order
   * they arrive in.
   */
  void checkIncrementalState();
  /** The lemmas recorded by recordJoin, as (SEXPR t1 t2 guard). */
  context::CDList<Node> d_incrementalJoins;
  /** Whether checkIncrementalState is rebuilding; suppresses all lemmas. */
  bool d_inShadowRebuild = false;
  /** Pairs of terms the rebuild of checkIncrementalState would equate. */
  std::vector<std::pair<Node, Node>> d_shadowObligations;
  //--------------------------------- end checking incrementality

  /**
   * Lightweight merge for model construction support.
   * Maintains d_mayEqualEqualityEngine and d_defValues without
   * generating Row lemmas or updating d_infoMap.
   */
  void mergeArraysModelOnly(TNode a, TNode b);

  /**
   * A fingerprint of everything check() reads: the number of (dis)equalities
   * asserted to the equality engine, and the number of registered reads and
   * writes. See the comment in check() for why two runs with the same
   * fingerprint derive the same thing.
   *
   * WHY COUNTS IDENTIFY CONTENTS. They do not, in general: registering a read
   * at one decision level, popping, and registering a different read leaves
   * d_selects the same size with different elements. They do along a single
   * context path, which is all this is ever compared over: the stored
   * fingerprint is only consulted while d_stateGen says the current state
   * extends the one it was taken in. d_selects and d_stores are CDLists, whose
   * only mutations are push_back and a restore that truncates from the end,
   * and the equality engine truncates its asserted-equality trail to
   * getNumAssertedEqualities() on backtrack. So all three only grow as the
   * path deepens, and a pop restores an earlier prefix exactly: two points on
   * one path with equal counts hold the same elements and the same
   * equivalence classes. In the example above, if the first read was
   * registered above the level of the fingerprinted check, the pop takes the
   * count back down and the second read raises it past the fingerprint again;
   * if it was registered below, the pop discards the fingerprinted check
   * itself and d_stateGen no longer matches.
   */
  struct CheckState
  {
    size_t d_assertions = 0;
    size_t d_selects = 0;
    size_t d_stores = 0;
    bool operator==(const CheckState& other) const
    {
      return d_assertions == other.d_assertions && d_selects == other.d_selects
             && d_stores == other.d_stores;
    }
  };
  /**
   * Generation of the last check() that ran to completion, as seen from the
   * current context. Each completed check stores the value it drew into
   * d_builtGen here.
   *
   * d_stateGen.get() == d_builtGen holds exactly when there has been no pop
   * below the context level that check completed at: a pop reverts this CDO
   * to the generation of an earlier check (or to 0), and since generations are
   * never reused, pushing again cannot make it match. It is therefore the test
   * for whether the plain structures in the per-check block below, which a pop
   * does not touch, still describe a state on the current context path.
   */
  context::CDO<uint64_t> d_stateGen;

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
  /**
   * For each unordered pair of reads a CongR lemma was derived for on the
   * current path, keyed on their equality, the guard of the latest one. See
   * checkCongruence for why a pair with a live guard need not be compared
   * again. This does not undo the reasoning above for keying
   * d_congruenceLemmaCache on the whole lemma: the pair is compared again,
   * and the new guard sent, as soon as the SAT solver falsifies a literal of
   * the old one.
   */
  context::CDHashMap<Node, Node> d_congruenceGuards;
  /** Deduplication cache for RIntro2 lemmas, keyed on the conclusion. */
  NodeSet d_rintro2LemmaCache;
  /**
   * Deduplication cache for index split lemmas, keyed on the split.
   *
   * This one is on the USER context, unlike the two caches above. An index
   * split is the tautology (or e (not e)); it is valid in every context, and
   * it is sent with LemmaProperty::NONE, so the clause is neither REMOVABLE
   * nor LOCAL and outlives any SAT-level backtracking. Its whole purpose is
   * to get the atom registered with the SAT solver so the index equality gets
   * decided, and a registered atom stays registered. Re-sending it after a
   * pop therefore adds nothing and costs a duplicate clause.
   *
   * It cost a lot. On regress0/aufbv/fifo32bc06k08, with this cache on the
   * SAT context, a 20 second budget emitted 19,452 index splits against
   * 36,793 CaDiCaL clauses total -- roughly half the clause database was the
   * same tautologies over and over, and CnfStep was 24,034. On the user
   * context the same budget emits 2,287 splits, 18,764 clauses and 6,729
   * CnfStep. ArraySolverDefault already scopes its d_RowAlreadyAdded this way.
   *
   * Do not "fix" this back by analogy with d_congruenceLemmaCache: that one
   * must be SAT-context-dependent because a CongR conclusion is not a
   * tautology and its guard can be falsified under the very context that
   * cached it. A tautology has no guard to falsify.
   */
  NodeSet d_indexSplitCache;

  //--------------------------------- propagation state
  /**
   * The structures in this block are plain, not context-dependent, and
   * persist from one check to the next. check() either rebuilds them from
   * scratch or, when d_stateGen says no pop has undone the state they
   * describe, has applyDelta bring them up to date. Between checks they are
   * only read by computeCareGraph(), which runs after a check at the same
   * state.
   *
   * Edges. A RowD edge leads from an array class X through a STORE s in X to
   * the class of s[0]; a RowU edge leads from the class of s[0] through s to
   * the class of s, and is only taken out of classes in d_activeArrays. Either
   * edge is open for a read whose index representative differs from that of
   * s[1].
   *
   * After every completed check:
   *
   * - VALIDITY. Every entry (X, k) -> r in d_arrayModels is keyed on current
   *   representatives, k is that of r's index, and r has a path of open edges
   *   from its own array to X. findPathConditions re-derives such a path for
   *   every lemma, so a break here trips its assertion.
   * - CLOSURE. Every entry at X has been pushed along every edge currently
   *   open out of X, and checked for AccessStore and AccessConstArray against
   *   the STOREs and STORE_ALLs X currently holds. A push that lands on a
   *   slot taken by another read counts once CongR has been checked between
   *   the two. The stop rule in propagateFrom relies on
   *   this: a read that stops at a taken slot leaves the rest of the walk to
   *   the occupant.
   * - CARE. Every edge an entry crossed has its index pair in
   *   d_pendingCarePairs, unless the pair is decided.
   *
   * What each change since the last check does to them, and how applyDelta
   * restores them:
   *
   * - A new read has no entries yet: walk it from its own array.
   * - A new store is a new edge out of two classes and a new AccessStore
   *   target in one: resume every read recorded at either.
   * - An array merge puts two classes' slots, stores, constant arrays and
   *   parents together: move the loser's slots to the winner, check CongR
   *   wherever both had one, and resume every read recorded at the winner.
   * - The RowU gate opening at a class opens RowU edges out of it: resume
   *   every read recorded there. The gate only ever opens along a path, since
   *   it grows with class sizes.
   * - An index merge is the only change that can break VALIDITY: an edge a
   *   read crossed closes when its store index joins the read's index class.
   *   It affects exactly the reads whose index is in the merged class, so drop
   *   all of their entries and walk them again.
   * - Element merges and new disequalities invalidate nothing; at most they
   *   make a lemma or a split unnecessary, which is filtered where it is used.
   * - A pop can undo any of the above, and is handled by rebuilding.
   *
   * d_pendingCarePairs is only ever appended to between rebuilds, so it may
   * hold pairs for edges no read crosses any more. That is harmless: a pair
   * only leads to a split lemma, which is a tautology, or to a care pair.
   */
  /**
   * Generation of the check that built the structures in this block; see
   * d_stateGen. A check draws it on entry, before touching anything, so a
   * check that a conflict aborts halfway leaves a generation that d_stateGen
   * never received, and the next check rebuilds.
   */
  uint64_t d_builtGen = 0;
  /** The source of fresh generations. */
  uint64_t d_genCounter = 0;
  /**
   * Fingerprint on entry to the check that built the structures in this
   * block. The default value is reached only before anything is registered or
   * asserted, where check() has nothing to do anyway, so it needs no separate
   * "unset" marker.
   */
  CheckState d_builtState;
  /**
   * The losing representative of every equality engine merge since the last
   * completed check, of any type. Nodes rather than TNodes: after a partial
   * pop this may name terms that the equality engine has since dropped.
   */
  std::vector<Node> d_mergeQueue;
  /** How many of d_selects the propagation state has walked. */
  size_t d_numSelectsDone = 0;
  /** How many of d_stores the propagation state accounts for. */
  size_t d_numStoresDone = 0;
  /** How many of d_pendingCarePairs the index split loop has looked at. */
  size_t d_numSplitsDone = 0;
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
   * WHAT IT BUYS. A lot, and do not delete it on the grounds that answers are
   * unchanged without it -- they are not. Measured over 2,505 SMT-LIB
   * benchmarks (QF_AX 551, QF_ALIA 176, QF_AUFLIA 1303, QF_AUFBV 75, QF_ABV
   * 400 sampled) at 30s each, removing the gate entirely:
   *
   *   solved      2383 -> 2369
   *   total cpu   5494.6s -> 6162.9s
   *
   * and on the 1,854 of those that nothing times out on, where the timing is
   * not swamped, 1850 -> 1837 solved and 1470.3s -> 2062.2s, i.e. 40% slower.
   * The loss is concentrated in QF_AUFLIA (1299 -> 1286) and in QF_AX
   * storecomm instances, the worst of which goes from under a second to 22.
   *
   * Blocking RowU also suppresses the RowD that would have followed out of
   * the classes it would have reached, which is why it prunes more than
   * "upward propagation" suggests.
   *
   * An earlier measurement over ~360 array files from test/regress put the
   * cost at 2%, and 20b8aa0c6 reported no answer changes at all. Both were
   * artefacts of a set too small and too timeout-dominated to measure this;
   * do not re-derive the conclusion from it. The assertion at the end of
   * computeActiveArrays pins the structural fact argued above, which is the
   * part a future change could break silently.
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
  //--------------------------------- end propagation state

  //--------------------------------- statistics
  IntStat d_numCongruenceLemmas;
  IntStat d_numAccessStoreLemmas;
  IntStat d_numDisequalityLemmas;
  IntStat d_numConstArrayLemmas;
  IntStat d_numCheckCalls;
  IntStat d_numCheckSkips;
  IntStat d_numCheckRebuilds;
  /** Reads resumed at a class whose contents changed (see applyDelta). */
  IntStat d_numDeltaResumes;
  /** Reads walked again because their index class merged. */
  IntStat d_numDeltaRedoReads;
  IntStat d_numPropagationsDown;
  IntStat d_numPropagationsUp;
  IntStat d_numRIntro2Propagations;
  //--------------------------------- end statistics
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__AEXT_SOLVER_H */

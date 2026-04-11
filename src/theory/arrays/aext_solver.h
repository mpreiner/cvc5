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

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/arrays/inference_manager.h"
#include "theory/arrays/path_edge.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
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
class AextArraySolver : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  AextArraySolver(Env& env, TheoryState& state, InferenceManager& im);
  ~AextArraySolver();

  //--------------------------------- initialization
  /**
   * Complete initialization, called from TheoryArrays::finishInit().
   * @param ee pointer to the official equality engine
   */
  void finishInit(eq::EqualityEngine* ee);
  //--------------------------------- end initialization

  //--------------------------------- term registration
  /**
   * Register a SELECT (array read) term (InitR rule).
   * @param node a term of the form select(a, i)
   */
  void preRegisterSelect(TNode node);
  /**
   * Register a STORE (array write) term (InitW rule).
   * Creates the virtual read select(store(a, i, v), i) and asserts RIntro1.
   * @param node a term of the form store(a, i, v)
   */
  void preRegisterStore(TNode node);
  //--------------------------------- end term registration

  //--------------------------------- notifications
  /** Notify that arrays a and b have been merged in the equality engine. */
  void notifyMerge(TNode a, TNode b);
  /**
   * Notify that arrays a and b are disequal.
   * @param reason the fact representing the disequality (not (= a b))
   */
  void notifyDisequality(TNode a, TNode b, TNode reason);
  //--------------------------------- end notifications

  //--------------------------------- main solving
  /**
   * Main theory check, called from TheoryArrays::postCheck().
   * For each registered select, propagates it through store chains (RowD/RowU)
   * and checks for conflicts (CongR/AccessStore). Then handles disequalities
   * (DisEq).
   */
  void check(Theory::Effort level);
  //--------------------------------- end main solving

  //--------------------------------- care graph support
  /**
   * Return the index pairs whose equality is undecided, collected during
   * the most recent check() call.  Used by TheoryArrays::computeCareGraph()
   * to emit care pairs instead of sending explicit split lemmas.
   */
  const std::vector<std::pair<TNode, TNode>>& getPendingCarePairs() const
  {
    return d_pendingCarePairs;
  }
  //--------------------------------- end care graph support

  //--------------------------------- model
  /** Collect model values for array terms. */
  bool collectModelValues(TheoryModel* m, const std::set<Node>& termSet);
  //--------------------------------- end model

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
   * Propagate a single select through store chains (RowD/RowU).
   *
   * Traverses the store chain from the select's array, passing through
   * stores when the read index is known disequal from the store index.
   * At each array reached, records the read in d_arrayModels and checks
   * for congruence conflicts.
   *
   * - CongR: two reads at the same (array, index) with different values
   *   generates: (pathConds1 /\ pathConds2 /\ i1=i2) => sel1 = sel2
   * - AccessStore: a read reaches a store with matching index but wrong value
   *   generates: (pathConds /\ i=j) => sel = storeValue
   *
   * No new terms are introduced; only existing select terms and store
   * values are related.
   *
   * @param select the select term to propagate
   */
  void checkAccess(TNode select);
  /**
   * Find a path from a select's starting array to a target array
   * representative through the store graph (RowD/RowU edges), and
   * extract the path conditions.  Uses BFS for shortest path.
   *
   * This is called on-demand when a conflict is detected (CongR,
   * AccessStore, or AccessConstArray), avoiding the need to pre-record
   * predecessor edges during propagation.
   *
   * @param select the select term whose path to reconstruct
   * @param targetRep the target array representative
   * @param conds output vector for path conditions
   * @return the entry array at targetRep (the specific node reached)
   */
  TNode findPathConditions(TNode select,
                           TNode targetRep,
                           std::vector<Node>& conds,
                           std::vector<PathEdge>* edges = nullptr);
  /**
   * RIntro2 theory propagation.
   *
   * For each STORE term `n = store(c, k, v)`, scan existing SELECT terms
   * for pairs (r1, r2) with rep(r1[0]) = rep(n), rep(r2[0]) = rep(c), and
   * rep(r1[1]) = rep(r2[1]), where the read index is currently entailed
   * disequal from `k`.  Asserts r1 = r2 as an internal fact, justified by
   * the array equalities, the index equality, and the index disequality.
   *
   * Uses only existing SELECT terms (no new reads introduced).
   */
  void propagateRIntro2();
  /**
   * Process array disequalities (DisEq rule).
   * For each disequality a != b, creates a witness index k and generates:
   *   (a != b) => select(a, k) != select(b, k)
   */
  void checkDisequalities();
  /**
   * Build the parent store map for the current check.
   * Maps each array representative to the list of STORE terms whose base
   * (child[0]) is in that equivalence class. Used for RowU propagation.
   */
  void buildParentMap();
  /** Compute active array representatives for RowU gating. */
  void computeActiveArrays();
  //--------------------------------- end propagation

  /** Reference to the theory state */
  TheoryState& d_state;
  /** Reference to the inference manager */
  InferenceManager& d_im;
  /** Pointer to the equality engine (set in finishInit) */
  eq::EqualityEngine* d_ee;

  /** All registered SELECT terms (context-dependent) */
  context::CDList<TNode> d_selects;
  /** All registered STORE terms (context-dependent) */
  context::CDList<TNode> d_stores;
  /** Array disequalities in current context */
  context::CDList<Node> d_arrayDisequalities;
  /** Disequalities for which a witness has already been generated */
  NodeSet d_witnessDiseqs;
  /** Lemma deduplication cache (context-dependent) */
  NodeSet d_lemmaCache;

  //--------------------------------- per-check data structures
  /**
   * Index pairs whose equality is undecided, collected during checkAccess().
   * Used by TheoryArrays::computeCareGraph() to emit care pairs.
   * Per-check (not context-dependent) so that pairs are recomputed on
   * each check() call.
   */
  std::vector<std::pair<TNode, TNode>> d_pendingCarePairs;
  /** Deduplication set for d_pendingCarePairs within a single check() */
  std::unordered_set<Node> d_pendingCarePairCache;
  /** Cache of selects already processed in current check() call */
  std::unordered_set<Node> d_checkAccessCache;
  /**
   * Array models (rebuilt each check() call).
   * For each array representative, maps index representative to the
   * PropagatedRead that reached it. Used for congruence detection:
   * if a second read arrives at the same (array, index) with a different
   * value, a CongR lemma is generated.
   */
  std::unordered_map<TNode, std::unordered_map<TNode, PropagatedRead>>
      d_arrayModels;
  /**
   * Parent store map (rebuilt each check() call).
   * Maps array representative -> STORE terms whose base is in that
   * equivalence class. Used for RowU propagation.
   */
  std::unordered_map<TNode, std::vector<TNode>> d_parentStores;
  /**
   * Active array representatives for RowU gating (rebuilt each check()).
   * An array rep is active if its EQ class has size > 1 (meaning an
   * equality merged it with another term), or if it is transitively
   * reachable downward through store[0] edges from an active rep.
   * RowU propagation is only performed from active array reps.
   */
  std::unordered_set<TNode> d_activeArrays;
  //--------------------------------- end per-check data structures

  //--------------------------------- statistics
  /** Number of congruence lemmas (CongR) */
  IntStat d_numCongruenceLemmas;
  /** Number of access-store lemmas */
  IntStat d_numAccessStoreLemmas;
  /** Number of disequality witness lemmas (DisEq) */
  IntStat d_numDisequalityLemmas;
  /** Number of constant array lemmas (Roc) */
  IntStat d_numConstArrayLemmas;
  /** Number of check() calls */
  IntStat d_numCheckCalls;
  /** Number of downward propagation steps (RowD) */
  IntStat d_numPropagationsDown;
  /** Number of upward propagation steps (RowU) */
  IntStat d_numPropagationsUp;
  /** Number of RIntro2 theory propagations */
  IntStat d_numRIntro2Propagations;
  //--------------------------------- end statistics
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__AEXT_SOLVER_H */

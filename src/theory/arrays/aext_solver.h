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
   */
  TNode findPathConditions(TNode select,
                           TNode targetRep,
                           std::vector<Node>& conds,
                           std::vector<PathEdge>* edges = nullptr);
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
   * the same pair are skipped: they are covered via EE congruence by one
   * of the already-emitted lemmas, and emitting more adds SAT clause bloat
   * without new distinguishing information.
   */
  std::unordered_map<Node, uint32_t> d_witnessRepPairCount;
  /** Lemma deduplication cache (context-dependent) */
  NodeSet d_lemmaCache;

  //--------------------------------- per-check data structures
  std::vector<std::pair<TNode, TNode>> d_pendingCarePairs;
  /**
   * Cached read-read care pair list (trigger-term rep pairs), built lazily
   * by computeCareGraph(). Reused across combination rounds as long as
   * d_arrayModelsHash still matches the current d_arrayModels content.
   */
  std::vector<std::pair<TNode, TNode>> d_readReadIndexPairs;
  /** Whether d_readReadIndexPairs is populated and matches d_arrayModels. */
  bool d_readReadIndexPairsValid;
  /** Hash of d_arrayModels for which d_readReadIndexPairs was built. */
  size_t d_arrayModelsHash;
  std::unordered_set<Node> d_pendingCarePairCache;
  std::unordered_set<Node> d_checkAccessCache;
  std::unordered_map<TNode, std::unordered_map<TNode, PropagatedRead>>
      d_arrayModels;
  std::unordered_map<TNode, std::vector<TNode>> d_parentStores;
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

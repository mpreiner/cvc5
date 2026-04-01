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
 * The key idea is to lazily propagate read information through store chains
 * guided by the current interpretation (equality engine state), generating
 * lemmas only when conflicts are detected. This contrasts with the default
 * cvc5 array solver which eagerly generates Row lemmas during term
 * registration and array merges.
 *
 * Calculus rules implemented (from the AEXT paper):
 *   InitR/InitW  - initialize propagation for reads and virtual writes
 *   RowD/RowU    - propagate down/up through stores (read-over-write)
 *   CongR        - congruence conflict detection (handled by EE)
 *   EqR/EqL      - propagate reads across array equalities (handled by EE)
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
 * --arrays-solver=aext is set. It replaces the default eager lemma generation
 * with a lazy, model-guided propagation approach.
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
   * Register a SELECT (array read) term.
   * Implements the InitR rule of the AEXT calculus.
   * @param node a term of the form select(a, i)
   */
  void preRegisterSelect(TNode node);
  /**
   * Register a STORE (array write) term.
   * Implements the InitW rule and asserts the RIntro1 axiom:
   *   select(store(a, i, v), i) = v
   * @param node a term of the form store(a, i, v)
   */
  void preRegisterStore(TNode node);
  //--------------------------------- end term registration

  //--------------------------------- notifications
  /**
   * Notify that arrays a and b have been merged in the equality engine.
   * @param a first array term
   * @param b second array term
   */
  void notifyMerge(TNode a, TNode b);
  /**
   * Notify that arrays a and b are disequal.
   * Records the disequality for later witness generation (DisEq rule).
   * @param a first array term
   * @param b second array term
   * @param reason the fact representing the disequality
   */
  void notifyDisequality(TNode a, TNode b, TNode reason);
  //--------------------------------- end notifications

  //--------------------------------- main solving
  /**
   * Main theory check, called from TheoryArrays::postCheck().
   * Propagates selects through store chains (RowD/RowU) and handles
   * disequalities (DisEq). Congruence (CongR) and equality propagation
   * (EqR/EqL) are handled by the equality engine.
   * @param level the current checking effort level
   */
  void check(Theory::Effort level);
  //--------------------------------- end main solving

  //--------------------------------- model
  /**
   * Collect model values for array terms.
   * @param m the theory model to populate
   * @param termSet the set of relevant terms
   * @return true if model construction succeeded
   */
  bool collectModelValues(TheoryModel* m, const std::set<Node>& termSet);
  //--------------------------------- end model

 private:
  //--------------------------------- propagation (core AEXT calculus)
  /**
   * Propagate a single select through store chains.
   * Implements RowD (downward) and RowU (upward) propagation.
   *
   * RowD: For select(a, i), if a's equivalence class contains store(b, j, v)
   *   and i != j (known in EE), generate: i != j => select(store(b,j,v),i) =
   *   select(b,i)
   *
   * RowU: For select(a, i), if store(a, j, v) exists as a registered store
   *   term (a is the base) and i != j, generate the same lemma connecting the
   *   read on a to the read on the store term.
   *
   * @param select the select term to propagate
   * @return true if any new lemmas were generated
   */
  bool propagateSelect(TNode select);
  /**
   * Generate a row-ne (read-over-write) lemma for the given store and index,
   * if not already generated.
   *
   * The lemma is: index != store[1] => select(store, index) = select(store[0],
   *   index)
   *
   * @param store a STORE term store(base, storeIndex, storeValue)
   * @param index the read index
   * @return true if a new lemma was generated
   */
  bool generateRowLemma(TNode store, TNode index);
  /**
   * Process array disequalities (DisEq rule).
   * For each disequality a != b, creates a witness index k and generates:
   *   (a != b) => select(a, k) != select(b, k)
   * @return true if any lemmas were generated
   */
  bool checkDisequalities();
  /**
   * Build the parent store map for the current check.
   * Maps each array representative to the list of STORE terms whose base
   * (child[0]) is in that equivalence class.
   */
  void buildParentMap();
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
  /** Lemma deduplication cache (user-context-dependent) */
  NodeSet d_lemmaCache;

  /** Cache of already-propagated selects in current check() call */
  std::unordered_set<Node> d_checkCache;
  /**
   * Parent store map (rebuilt each check() call).
   * Maps array representative -> list of STORE terms whose base is in that
   * equivalence class. Used for RowU propagation.
   */
  std::unordered_map<TNode, std::vector<TNode>> d_parentStores;

  //--------------------------------- statistics
  /** Number of row lemmas (RowD/RowU) */
  IntStat d_numRowLemmas;
  /** Number of disequality witness lemmas (DisEq) */
  IntStat d_numDisequality;
  /** Number of check() calls */
  IntStat d_numCheckCalls;
  //--------------------------------- end statistics
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__AEXT_SOLVER_H */

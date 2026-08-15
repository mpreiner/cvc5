/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Array solver interface.
 *
 * Describes the abstract interface for the internal array solver of
 * TheoryArrays.  Concrete implementations are ArraySolverDefault (Row/Ext
 * eager lemma generation) and AextArraySolver (AEXT calculus, lazy
 * propagation).
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__ARRAY_SOLVER_H
#define CVC5__THEORY__ARRAYS__ARRAY_SOLVER_H

#include <functional>
#include <map>
#include <set>

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

namespace arrays {

class InferenceManager;

/** Map from node to node, used for tracking default values per mayEqual EC. */
typedef context::CDHashMap<Node, Node> DefValMap;

/**
 * Abstract base class for array solvers.
 *
 * Follows the BVSolver pattern: extends EnvObj, holds references to shared
 * state (TheoryState, InferenceManager, equality engines), and provides
 * a virtual interface that mirrors the key Theory methods.
 *
 * TheoryArrays creates either an ArraySolverDefault or an AextArraySolver
 * and delegates solver-specific work through this interface.
 */
class ArraySolver : protected EnvObj
{
 public:
  /** Callback for registering internally-created terms. */
  using PreRegCallback = std::function<void(TNode)>;
  /** Callback for adding care pairs to the care graph. */
  using AddCarePairFn = std::function<void(TNode, TNode)>;

  ArraySolver(Env& env,
              TheoryState& state,
              InferenceManager& im,
              Valuation valuation,
              eq::EqualityEngine& mayEqualEE,
              DefValMap& defValues,
              context::CDO<bool>& sharedTerms);

  virtual ~ArraySolver() {}

  /**
   * Complete initialization, called from TheoryArrays::finishInit().
   * @param ee pointer to the official equality engine
   */
  virtual void finishInit(eq::EqualityEngine* ee) = 0;

  //--------------------------------- term registration
  /**
   * Solver-specific registration for a SELECT term.
   * Called after the shared prefix in TheoryArrays::preRegisterTermInternal.
   */
  virtual void preRegisterSelect(TNode node) = 0;
  /**
   * Solver-specific registration for a STORE term.
   * Called after the shared prefix in TheoryArrays::preRegisterTermInternal.
   */
  virtual void preRegisterStore(TNode node) = 0;
  /**
   * Solver-specific registration for a STORE_ALL (constant array) term.
   * Called after the shared prefix in TheoryArrays::preRegisterTermInternal.
   */
  virtual void preRegisterStoreAll(TNode node) = 0;
  //--------------------------------- end term registration

  //--------------------------------- equality engine callbacks
  /**
   * Callback for when two array terms are merged in the equality engine.
   * Called from TheoryArrays::NotifyClass::eqNotifyMerge.
   */
  virtual void eqNotifyMerge(TNode a, TNode b) = 0;
  //--------------------------------- end equality engine callbacks

  //--------------------------------- standard check
  /** Post-check, called from TheoryArrays::postCheck(). */
  virtual void postCheck(Theory::Effort level) = 0;
  /**
   * Handle an array disequality notification.
   * Called from TheoryArrays::notifyFact() when a disequality between
   * array-typed terms is asserted.
   * @param a first array term
   * @param b second array term
   * @param fact the disequality fact (not (= a b))
   */
  virtual void notifyArrayDisequality(TNode a, TNode b, TNode fact) = 0;
  //--------------------------------- end standard check

  //--------------------------------- model
  /**
   * Compute additional relevant terms for model construction.
   * Called from TheoryArrays::computeRelevantTerms() after the shared
   * RIntro1 pass.
   */
  virtual void computeRelevantTerms(std::set<Node>& termSet) = 0;
  /**
   * Augment the selects map for model construction.
   * Called from TheoryArrays::collectModelValues() after the initial
   * selects map is built from the term set.  The solver may add
   * additional (array rep -> read) entries to ensure consistent models.
   * @param selects map from array EE representative to select nodes
   * @param termSet the set of relevant terms
   */
  virtual void augmentModelSelects(std::map<Node, std::vector<Node>>& selects,
                                   const std::set<Node>& termSet) = 0;
  //--------------------------------- end model

  //--------------------------------- care graph
  /**
   * Compute solver-specific care graph entries.
   * @param addCarePair callback to add a care pair
   */
  virtual void computeCareGraph(AddCarePairFn addCarePair) = 0;
  //--------------------------------- end care graph

  /** Called before solving. */
  virtual void presolve() {}
  /** Identify this solver. */
  virtual std::string identify() const = 0;

 protected:
  /**
   * Check a pair of read terms r1, r2 for the care graph, and add the care
   * pair for their indices if their equality is still undecided and their
   * arrays may be equal.
   *
   * This is shared infrastructure: both solvers need the same per-pair test,
   * they only differ in how they enumerate the candidate pairs (see the
   * respective computeCareGraph implementations). The index of r1 must be a
   * trigger term for THEORY_ARRAYS; callers are responsible for filtering
   * that before calling.
   */
  void checkPair(TNode r1, TNode r2, AddCarePairFn& addCarePair);

  /** Reference to the theory state */
  TheoryState& d_state;
  /** Reference to the inference manager */
  InferenceManager& d_im;
  /** Valuation for SAT-level queries */
  Valuation d_valuation;
  /** Pointer to the equality engine (set in finishInit) */
  eq::EqualityEngine* d_ee;
  /** Reference to the may-equal equality engine (shared, owned by TheoryArrays)
   */
  eq::EqualityEngine& d_mayEqualEqualityEngine;
  /** Reference to the default values map (shared, owned by TheoryArrays) */
  DefValMap& d_defValues;
  /**
   * Whether any non-array shared term has been notified (shared, owned by
   * TheoryArrays). If false, no index can be a trigger term, so the care
   * graph read sweeps can be skipped entirely.
   */
  context::CDO<bool>& d_sharedTerms;
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__ARRAY_SOLVER_H */

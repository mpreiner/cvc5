/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of arrays.
 *
 * Thin wrapper around ArraySolver implementations (ArraySolverDefault for
 * the Row/Ext eager decision procedure, AextArraySolver for the AEXT
 * calculus).  Provides the Theory interface, shared infrastructure
 * (preprocessing, equality engine setup, model construction skeleton),
 * and delegates solver-specific work through the ArraySolver interface.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__THEORY_ARRAYS_H
#define CVC5__THEORY__ARRAYS__THEORY_ARRAYS_H

#include <memory>
#include <unordered_map>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "theory/arrays/array_solver.h"
#include "theory/arrays/inference_manager.h"
#include "theory/arrays/proof_checker.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * Theory of arrays.
 *
 * Serves as the Theory interface and delegates solver-specific work to
 * an internal ArraySolver (either ArraySolverDefault or AextArraySolver).
 */
class TheoryArrays : public Theory
{
  /////////////////////////////////////////////////////////////////////////////
  // MISC
  /////////////////////////////////////////////////////////////////////////////

 private:
  /** True node for predicates = true */
  Node d_true;
  /** True node for predicates = false */
  Node d_false;

  // Statistics
  /** splits on array variables */
  IntStat d_numSharedArrayVarSplits;

 public:
  TheoryArrays(Env& env,
               OutputChannel& out,
               Valuation valuation,
               std::string name = "theory::arrays::");
  ~TheoryArrays();

  //--------------------------------- initialization
  TheoryRewriter* getTheoryRewriter() override;
  ProofRuleChecker* getProofChecker() override;
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  void finishInit() override;
  //--------------------------------- end initialization

  std::string identify() const override { return std::string("TheoryArrays"); }

  /////////////////////////////////////////////////////////////////////////////
  // PREPROCESSING
  /////////////////////////////////////////////////////////////////////////////

 private:
  // PPNotifyClass: dummy template class for d_ppEqualityEngine
  class PPNotifyClass
  {
   public:
    bool notify(CVC5_UNUSED TNode propagation) { return true; }
    void notify(CVC5_UNUSED TNode t1, CVC5_UNUSED TNode t2) {}
  };

  PPNotifyClass d_ppNotify;
  eq::EqualityEngine d_ppEqualityEngine;
  context::CDList<Node> d_ppFacts;

  Node preprocessTerm(TNode term);
  Node recursivePreprocessTerm(TNode term);
  bool ppDisequal(TNode a, TNode b);
  Node solveWrite(TNode term, bool solve1, bool solve2, bool ppCheck);

  /** The theory rewriter for this theory. */
  TheoryArraysRewriter d_rewriter;
  /** A (default) theory state object */
  TheoryState d_state;
  /** The arrays inference manager */
  InferenceManager d_im;

 public:
  bool ppAssert(TrustNode tin, TrustSubstitutionMap& outSubstitutions) override;
  TrustNode ppRewrite(TNode atom, std::vector<SkolemLemma>& lems) override;

  /////////////////////////////////////////////////////////////////////////////
  // T-PROPAGATION / REGISTRATION
  /////////////////////////////////////////////////////////////////////////////

 private:
  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;
  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /** Should be called to propagate the literal. */
  bool propagateLit(TNode literal);

  /** For debugging only */
  context::CDHashSet<Node> d_isPreRegistered;

  /** Helper for preRegisterTerm, also used internally */
  void preRegisterTermInternal(TNode n);

 public:
  void preRegisterTerm(TNode n) override;
  TrustNode explain(TNode n) override;

  /////////////////////////////////////////////////////////////////////////////
  // SHARING
  /////////////////////////////////////////////////////////////////////////////

 private:
  class MayEqualNotifyClass
  {
   public:
    bool notify(CVC5_UNUSED TNode propagation) { return true; }
    void notify(CVC5_UNUSED TNode t1, CVC5_UNUSED TNode t2) {}
  };

  MayEqualNotifyClass d_mayEqualNotify;
  eq::EqualityEngine d_mayEqualEqualityEngine;

  // Helper for computeCareGraph
  void checkPair(TNode r1, TNode r2);

 public:
  void notifySharedTerm(TNode t) override;
  void computeCareGraph() override;
  bool isShared(TNode t)
  {
    return (d_sharedArrays.find(t) != d_sharedArrays.end());
  }

  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////

 public:
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////

  void presolve() override;

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////

  //--------------------------------- standard check
  void postCheck(Effort level) override;
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check

 private:
  // NotifyClass: handles call-back from congruence closure module
  class NotifyClass : public eq::EqualityEngineNotify
  {
    TheoryArrays& d_arrays;

   public:
    NotifyClass(TheoryArrays& arrays) : d_arrays(arrays) {}

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      if (value)
      {
        return d_arrays.propagateLit(predicate);
      }
      return d_arrays.propagateLit(predicate.notNode());
    }

    bool eqNotifyTriggerTermEquality(CVC5_UNUSED TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      if (value)
      {
        return d_arrays.propagateLit(t1.eqNode(t2));
      }
      return d_arrays.propagateLit(t1.eqNode(t2).notNode());
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      d_arrays.d_im.conflictEqConstantMerge(t1, t2);
    }

    void eqNotifyNewClass(TNode t) override
    {
      d_arrays.preRegisterTermInternal(t);
    }
    void eqNotifyMerge(TNode t1, TNode t2) override
    {
      if (t1.getType().isArray())
      {
        d_arrays.d_internal->eqNotifyMerge(t1, t2);
      }
    }
    void eqNotifyDisequal(CVC5_UNUSED TNode t1,
                          CVC5_UNUSED TNode t2,
                          CVC5_UNUSED TNode reason) override
    {
    }
  };

  NotifyClass d_notify;
  ArraysProofRuleChecker d_checker;

  typedef context::CDHashSet<Node> CDNodeSet;

  CDNodeSet d_sharedArrays;
  CDNodeSet d_sharedOther;
  context::CDO<bool> d_sharedTerms;

  // Map from constant values to read terms (care graph)
  context::CDList<TNode> d_reads;

  context::CDList<Node> d_modelConstraints;
  context::CDHashSet<Node> d_lemmasSaved;
  std::vector<Node> d_lemmas;

  // Default values for each mayEqual equivalence class
  DefValMap d_defValues;

  /**
   * Compute relevant terms. This includes select nodes for the RIntro1 rule,
   * plus solver-specific terms via d_internal->computeRelevantTerms.
   */
  void computeRelevantTerms(std::set<Node>& termSet) override;

  /** The internal array solver (either ArraySolverDefault or AextArraySolver)
   */
  std::unique_ptr<ArraySolver> d_internal;
}; /* class TheoryArrays */

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__THEORY_ARRAYS_H */

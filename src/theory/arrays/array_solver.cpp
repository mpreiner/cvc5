/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Shared implementation for array solvers.
 */

#include "theory/arrays/array_solver.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

ArraySolver::ArraySolver(Env& env,
                         TheoryState& state,
                         InferenceManager& im,
                         Valuation valuation,
                         eq::EqualityEngine& mayEqualEE,
                         DefValMap& defValues,
                         context::CDO<bool>& sharedTerms)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_valuation(valuation),
      d_ee(nullptr),
      d_mayEqualEqualityEngine(mayEqualEE),
      d_defValues(defValues),
      d_sharedTerms(sharedTerms)
{
}

void ArraySolver::checkPair(TNode r1, TNode r2, AddCarePairFn& addCarePair)
{
  Trace("arrays::sharing") << "arrays::computeCareGraph(): checking reads "
                           << r1 << " and " << r2 << std::endl;

  TNode x = r1[1];
  TNode y = r2[1];
  Assert(d_ee->isTriggerTerm(x, THEORY_ARRAYS));

  if (d_ee->hasTerm(x) && d_ee->hasTerm(y)
      && (d_ee->areEqual(x, y) || d_ee->areDisequal(x, y, false)))
  {
    Trace("arrays::sharing")
        << "arrays::computeCareGraph(): equality known, skipping" << std::endl;
    return;
  }

  // If the terms are already known to be equal, we are also in good shape
  if (d_ee->areEqual(r1, r2))
  {
    Trace("arrays::sharing")
        << "arrays::computeCareGraph(): equal, skipping" << std::endl;
    return;
  }

  if (r1[0] != r2[0])
  {
    Assert(d_mayEqualEqualityEngine.hasTerm(r1[0])
           && d_mayEqualEqualityEngine.hasTerm(r2[0]));
    if (r1[0].getType() != r2[0].getType()
        || d_ee->areDisequal(r1[0], r2[0], false))
    {
      Trace("arrays::sharing")
          << "arrays::computeCareGraph(): arrays can't be equal, skipping"
          << std::endl;
      return;
    }
    else if (!d_mayEqualEqualityEngine.areEqual(r1[0], r2[0]))
    {
      return;
    }
  }

  if (!d_ee->isTriggerTerm(y, THEORY_ARRAYS))
  {
    Trace("arrays::sharing")
        << "arrays::computeCareGraph(): not connected to shared terms, skipping"
        << std::endl;
    return;
  }

  // Get representative trigger terms
  TNode x_shared = d_ee->getTriggerTermRepresentative(x, THEORY_ARRAYS);
  TNode y_shared = d_ee->getTriggerTermRepresentative(y, THEORY_ARRAYS);
  EqualityStatus eqStatusDomain =
      d_valuation.getEqualityStatus(x_shared, y_shared);
  switch (eqStatusDomain)
  {
    case EQUALITY_TRUE_AND_PROPAGATED:
      // Should have been propagated to us
      DebugUnhandled();
      break;
    case EQUALITY_TRUE:
      // Missed propagation - need to add the pair so that theory engine can
      // force propagation
      Trace("arrays::sharing")
          << "arrays::computeCareGraph(): missed propagation" << std::endl;
      break;
    case EQUALITY_FALSE_AND_PROPAGATED:
      Trace("arrays::sharing")
          << "arrays::computeCareGraph(): checkPair called when false in model"
          << std::endl;
      // Should have been propagated to us
      DebugUnhandled();
      break;
    case EQUALITY_FALSE: CVC5_FALLTHROUGH;
    case EQUALITY_FALSE_IN_MODEL:
      Trace("arrays::sharing")
          << "arrays::computeCareGraph(): checkPair called when false in model"
          << std::endl;
      return;
    default:
      // Covers EQUALITY_TRUE_IN_MODEL (common case) and EQUALITY_UNKNOWN
      break;
  }

  // Add this pair
  Trace("arrays::sharing")
      << "arrays::computeCareGraph(): adding to care-graph" << std::endl;
  addCarePair(x_shared, y_shared);
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

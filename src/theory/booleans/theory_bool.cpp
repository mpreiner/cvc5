/*********************                                                        */
/*! \file theory_bool.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory of booleans.
 **
 ** The theory of booleans.
 **/

#include "theory/theory.h"
#include "theory/booleans/theory_bool.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/valuation.h"
#include "util/boolean_simplification.h"
#include "theory/substitutions.h"

#include <vector>
#include <stack>
#include "util/hash.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace booleans {

/** Utility to make a conjunction */
static Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}

/**
 * Notification class for receiving notifications from the equality engine.
 */
class EqualityNotifyClass : public eq::EqualityEngineNotify {

  TheoryBool& d_theoryBool;

public:

  EqualityNotifyClass(TheoryBool& theoryBool)
  : d_theoryBool(theoryBool)
  {}

  bool eqNotifyTriggerEquality(TNode equality, bool value) {
    Debug("theory::bool") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
    if (value) {
      return d_theoryBool.propagate(equality);
    } else {
      return d_theoryBool.propagate(equality.notNode());
    }
  }

  bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
    Debug("theory::bool") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
    if (value) {
      return d_theoryBool.propagate(predicate);
    } else {
      return d_theoryBool.propagate(predicate.notNode());
    }
  }

  bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
    Debug("theory::bool") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
    if (value) {
      return d_theoryBool.propagate(t1.eqNode(t2));
    } else {
      return d_theoryBool.propagate(t1.eqNode(t2).notNode());
    }
  }

  void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
    Debug("theory:bool") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
    d_theoryBool.conflict(t1, t2);
  }


  // UNUSED STUFF

  void eqNotifyNewClass(TNode t) {};
  void eqNotifyPreMerge(TNode t1, TNode t2) {};
  void eqNotifyPostMerge(TNode t1, TNode t2) {};
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {}
};

TheoryBool::TheoryBool(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo)
: Theory(THEORY_BOOL, c, u, out, valuation, logicInfo)
, d_equalityNotify(new EqualityNotifyClass(*this))
, d_equalityEngine(*d_equalityNotify, c, "theory::TheoryBool", false)
, d_conflict(c, false)
{
}

TheoryBool::~TheoryBool() {
  delete d_equalityNotify;
}

Theory::PPAssertStatus TheoryBool::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {

  if (in.getKind() == kind::CONST_BOOLEAN && !in.getConst<bool>()) {
    // If we get a false literal, we're in conflict
    return PP_ASSERT_STATUS_CONFLICT;
  }

  // Add the substitution from the variable to its value
  if (in.getKind() == kind::NOT) {
    if (in[0].getKind() == kind::VARIABLE) {
      outSubstitutions.addSubstitution(in[0], NodeManager::currentNM()->mkConst<bool>(false));
    } else {
      return PP_ASSERT_STATUS_UNSOLVED;
    }
  } else {
    if (in.getKind() == kind::VARIABLE) {
      outSubstitutions.addSubstitution(in, NodeManager::currentNM()->mkConst<bool>(true));
    } else {
      return PP_ASSERT_STATUS_UNSOLVED;
    }
  }

  return PP_ASSERT_STATUS_SOLVED;
}

void TheoryBool::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryBool::propagate(Effort effort) {
  Debug("theory::bool") << "TheoryBool::propagate(" << effort << ")" << std::endl;
  // Nothing to do, all in check
}

void TheoryBool::check(Effort effort) {
  Debug("theory::bool") << "TheoryBool::check(" << effort << ")" << std::endl;

  if (done() && !fullEffort(effort)) {
    return;
  }

  while (!done() && !d_conflict)
  {
    // Get the next assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("theroy::bool") << "TheoryBool::check(): processing " << fact << std::endl;

    // Do the work
    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];
    if (atom.getKind() == kind::EQUAL) {
      d_equalityEngine.assertEquality(atom, polarity, fact);
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, fact);
    }
  }

  // If in full effort, check the number of classes (max 2)
  if (!d_conflict && fullEffort(effort)) {
  }
}

Node TheoryBool::explain(TNode literal) {
  Debug("theory::bool") << "TheoryBool::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  return mkAnd(assumptions);
}

void TheoryBool::explain(TNode literal, std::vector<TNode>& assumptions) {
  Debug("theory::bool") << "TheoryBool::explain(" << literal << ")" << std::endl;

  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  eq::EqProof* eqProof = d_proofEnabled ? new eq::EqProof : NULL;
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions, eqProof);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions, eqProof);
  }
}

void TheoryBool::preRegisterTerm(TNode term) {
  Debug("theory::bool") << "TheoryBool::preRegisterTerm(" << term << ")" << std::endl;
  switch (term.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(term);
    break;
  default:
    // Variables etc
    d_equalityEngine.addTerm(term);
    break;
  }
}

void TheoryBool::addSharedTerm(TNode term) {
  Debug("theory::bool") << "TheoryBool::addSharedTerm(" << term << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(term, THEORY_BOOL);
}

void TheoryBool::collectModelInfo(TheoryModel* m, bool fullModel) {
  Debug("theory::bool") << "TheoryBool::collectModelInfo()" << std::endl;
}

EqualityStatus TheoryBool::getEqualityStatus(TNode t1, TNode t2) {
  Debug("theory::bool") << "TheoryBool::propagate(" << t1 << ", " << t2 << ")" << std::endl;

  // Check for equality (simplest)
  if (d_equalityEngine.areEqual(t1, t2)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }

  // Check for disequality
  if (d_equalityEngine.areDisequal(t1, t2, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }

  return EQUALITY_UNKNOWN;
}

bool TheoryBool::propagate(TNode literal) {
  Debug("theory::bool") << "TheoryBool::propagate(" << literal << ")" << std::endl;
  if (d_conflict) {
    // If already in conflict, no more propagation
    return false;
  }
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

void TheoryBool::conflict(TNode t1, TNode t2) {
  Debug("theory::bool") << "TheoryBool::conflict(" << t1 << ", " << t2 << ")" << std::endl;
  d_conflictTerm = explain(t1.eqNode(t2));
  d_out->conflict(d_conflictTerm);
  d_conflict = true;
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

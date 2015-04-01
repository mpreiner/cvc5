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

/**
 * Notification class for receiving notifications from the equality engine.
 */
class EqualityNotifyClass : public eq::EqualityEngineNotify {

  TheoryBool& d_theoryBool;

public:

  EqualityNotifyClass(TheoryBool& theoryBool): d_theoryBool(theoryBool) {}

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

  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
    Debug("theory:bool") << "NotifyClass::eqNotifyDisequal(" << t1 << ", " << t2 << ", " << reason << std::endl;
    d_theoryBool.eqNotifyDisequal(t1, t2, reason);
  }

  // UNUSED STUFF

  void eqNotifyNewClass(TNode t) {};
  void eqNotifyPreMerge(TNode t1, TNode t2) {};
  void eqNotifyPostMerge(TNode t1, TNode t2) {};
};

TheoryBool::TheoryBool(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo)
: Theory(THEORY_BOOL, c, u, out, valuation, logicInfo)
, d_equalityNotify(new EqualityNotifyClass(*this))
, d_equalityEngine(*d_equalityNotify, c, "theory::TheoryBool", false)
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

}

void TheoryBool::propagate(Effort effort) {

}

void TheoryBool::check(Effort) {

}

Node TheoryBool::explain(TNode n) {
  return n;
}

void TheoryBool::preRegisterTerm(TNode term) {

}

void TheoryBool::addSharedTerm(TNode n) {

}

void TheoryBool::collectModelInfo(TheoryModel* m, bool fullModel) {

}

EqualityStatus TheoryBool::getEqualityStatus(TNode a, TNode b) {
  return EQUALITY_UNKNOWN;
}

bool TheoryBool::propagate(TNode literal) {
  return true;
}

void TheoryBool::conflict(TNode a, TNode b) {

}

void TheoryBool::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {

}


}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

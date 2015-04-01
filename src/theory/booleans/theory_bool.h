/*********************                                                        */
/*! \file theory_bool.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory of booleans
 **
 ** The theory of booleans.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H
#define __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {
namespace booleans {

/** The class we use for equality engine notifications */
class EqualityNotifyClass;

class TheoryBool : public Theory {

  /** Notify for the equality engine */
  eq::EqualityEngineNotify* d_equalityNotify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

  /** Called to propagate a literal. */
  bool propagate(TNode literal);

  /** Called on conflict when merging two constants */
  void conflict(TNode a, TNode b);

  /** Called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

  friend class EqualityNotifyClass;

public:

  TheoryBool(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);
  ~TheoryBool();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);
  void propagate(Effort effort);
  void check(Effort);
  Node explain(TNode n);
  void preRegisterTerm(TNode term);
  void addSharedTerm(TNode n);
  void collectModelInfo(TheoryModel* m, bool fullModel);
  EqualityStatus getEqualityStatus(TNode a, TNode b);

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);

  std::string identify() const { return std::string("TheoryBool"); }
};/* class TheoryBool */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H */

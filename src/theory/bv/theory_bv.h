/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__THEORY_BV_H
#define CVC4__THEORY__BV__THEORY_BV_H

#include <unordered_map>
#include <unordered_set>

#include "context/context.h"
#include "smt/logic_request.h"
#include "theory/logic_info.h"
#include "theory/output_channel.h"
#include "theory/theory.h"
#include "theory/valuation.h"

namespace CVC4 {

// Forward declarations, needed because the BV theory and the BV Proof classes
// are cyclically dependent
namespace proof {
class BitVectorProof;
}

namespace theory {

class TheoryModel;

namespace bv {

class TheoryBVSolver;

class TheoryBV : public Theory
{
 public:
  TheoryBV(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo,
           std::string name = "");

  ~TheoryBV();

  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;

  void finishInit() override;

  Node expandDefinition(LogicRequest& logicRequest, Node node) override;

  void preRegisterTerm(TNode n) override;

  void check(Effort e) override;

  bool needsCheckLastEffort() override;

  void propagate(Effort e) override;

  Node explain(TNode n) override;

  bool collectModelInfo(TheoryModel* m) override;

  std::string identify() const override { return std::string("TheoryBV"); }

  /** equality engine */
  eq::EqualityEngine* getEqualityEngine() override;

  bool getCurrentSubstitution(int effort,
                              std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp) override;

  int getReduction(int effort, Node n, Node& nr) override;

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;

  void enableCoreTheorySlicer();

  Node ppRewrite(TNode t) override;

  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;

  void presolve() override;

  bool applyAbstraction(const std::vector<Node>& assertions,
                        std::vector<Node>& new_assertions);

  void setProofLog(proof::BitVectorProof* bvp);

 private:
  friend class TheoryBVSolver;

  std::unique_ptr<TheoryBVSolver> d_internal;

  /**
   * Maps from bit-vector width to division-by-zero uninterpreted
   * function symbols.
   */
  std::unordered_map<unsigned, Node> d_ufDivByZero;
  std::unordered_map<unsigned, Node> d_ufRemByZero;

  /**
   * Return the uninterpreted function symbol corresponding to division-by-zero
   * for this particular bit-width
   * @param k should be UREM or UDIV
   * @param width
   *
   * @return
   */
  Node getUFDivByZero(Kind k, unsigned width);

  /** Add shared term to the theory. */
  void addSharedTerm(TNode t) override;

}; /* class TheoryBV */

class TheoryBVSolver
{
 public:
  TheoryBVSolver(TheoryBV& bv) : d_bv(bv){};

  virtual ~TheoryBVSolver(){};

  // Theory-specific methods
  virtual void setMasterEqualityEngine(eq::EqualityEngine* eq){};

  virtual void finishInit(){};

  virtual void preRegisterTerm(TNode n) = 0;

  virtual void check(theory::Theory::Effort e) = 0;

  virtual bool needsCheckLastEffort() = 0;

  virtual void propagate(theory::Theory::Effort e){};

  virtual Node explain(TNode n)
  {
    Unimplemented("TheoryBVSolver::explain interface not implemented");
  };

  virtual bool collectModelInfo(TheoryModel* m) = 0;

  virtual std::string identify() const = 0;

  /** equality engine */
  virtual eq::EqualityEngine* getEqualityEngine() { return nullptr; };

  virtual bool getCurrentSubstitution(int effort,
                                      std::vector<Node>& vars,
                                      std::vector<Node>& subs,
                                      std::map<Node, std::vector<Node>>& exp)
  {
    return false;
  };

  virtual theory::Theory::PPAssertStatus ppAssert(
      TNode in, SubstitutionMap& outSubstitutions) = 0;

  virtual Node ppRewrite(TNode t) { return t; };

  virtual void ppStaticLearn(TNode in, NodeBuilder<>& learned){};

  virtual void presolve() = 0;

  // BV-specific methods
  virtual void enableCoreTheorySlicer() = 0;

  virtual bool applyAbstraction(const std::vector<Node>& assertions,
                                std::vector<Node>& new_assertions) = 0;

  virtual void setProofLog(proof::BitVectorProof* bvp) = 0;

  virtual void addSharedTerm(TNode t) = 0;

 protected:
  TheoryBV& d_bv;

  // Export TheoryBV functionality used in subsolvers.

  ExtTheory* getExtTheory() { return d_bv.getExtTheory(); }

  void computeRelevantTerms(std::set<Node>& termSet)
  {
    return d_bv.computeRelevantTerms(termSet);
  };

  bool isLeaf(TNode node) { return d_bv.isLeaf(node); }

  size_t numAssertions() { return d_bv.numAssertions(); }

  theory::Assertion get() { return d_bv.get(); }

  bool done() { return d_bv.done(); }

  OutputChannel* getOutputChannel() { return d_bv.d_out; }

  Valuation& getValuation() { return d_bv.d_valuation; }
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BV__THEORY_BV_H */

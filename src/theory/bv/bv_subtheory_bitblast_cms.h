/*********************                                                        */
/*! \file bv_subtheory_bitblast_cms.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_SUBTHEORY_BITBLAST_CMS_H
#define __CVC4__THEORY__BV__BV_SUBTHEORY_BITBLAST_CMS_H

#include <unordered_map>

#include "theory/bv/bitblast/eager_bitblaster.h"
#include "theory/bv/bv_subtheory.h"
#include "theory/bv/bv_quick_check.h"

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * BitblastSolverCms
 */
class BitblastSolverCms : public SubtheorySolver
{
 public:
  BitblastSolverCms(context::Context* c, TheoryBV* bv);
  ~BitblastSolverCms();

  void preRegister(TNode node) override;
  bool check(Theory::Effort e) override;
  void explain(TNode literal, std::vector<TNode>& assumptions) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  bool collectModelInfo(TheoryModel* m, bool fullModel) override;
  Node getModelValue(TNode node) override;
  bool isComplete() override { return true; }
  void setProofLog(BitVectorProof* bvp) override;

 private:
  std::unique_ptr<EagerBitblaster> d_bitblaster;

  context::Context* d_context;
  context::CDList<Node> d_assumptions;
  context::CDHashSet<Node, NodeHashFunction> d_assertions;
  context::CDList<Node> d_assertionsAdded;
  context::CDQueue<TNode> d_bitblastQueue;
  std::unique_ptr<BVQuickCheck> d_quickCheck;
  std::unique_ptr<QuickXPlain> d_quickXplain;

  void setConflict();

  struct Statistics
  {
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif

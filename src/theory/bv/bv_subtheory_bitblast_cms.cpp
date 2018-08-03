/*********************                                                        */
/*! \file bv_subtheory_bitblast_cms.cpp
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

#include "theory/bv/bv_subtheory_bitblast_cms.h"
#include "options/bv_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

BitblastSolverCms::BitblastSolverCms(context::Context* c, TheoryBV* bv)
    : SubtheorySolver(c, bv),
      d_bitblaster(new EagerBitblaster(bv, c, SAT_SOLVER_CRYPTOMINISAT)),
      d_assumptions(c),
      d_assertions(c),
      d_assertionsAdded(c),
      d_bitblastQueue(c),
      d_quickCheck(options::bitvectorQuickXplain() ? new BVQuickCheck("bb", bv) : NULL),
      d_quickXplain(options::bitvectorQuickXplain() ? new QuickXPlain("bb", d_quickCheck) :  NULL),
      d_statistics()
{
}

BitblastSolverCms::~BitblastSolverCms() {}

BitblastSolverCms::Statistics::Statistics() {}

BitblastSolverCms::Statistics::~Statistics() {}

void BitblastSolverCms::preRegister(TNode node)
{
  if ((node.getKind() == kind::EQUAL || node.getKind() == kind::BITVECTOR_ULT
       || node.getKind() == kind::BITVECTOR_ULE
       || node.getKind() == kind::BITVECTOR_SLT
       || node.getKind() == kind::BITVECTOR_SLE)
      && !d_bitblaster->hasBBAtom(node))
  {
    //std::cout << "***** preregister[" << d_context->getLevel() << "]: " << node << std::endl;
    d_bitblastQueue.push_back(node);
    if (d_context->getLevel() == 1)
    {
      //d_bitblaster->bbFormula(node, true);
      d_assertions.insert(node);
    }
  }
}

void BitblastSolverCms::explain(TNode literal, std::vector<TNode>& assumptions)
{
}

bool BitblastSolverCms::check(Theory::Effort e)
{
  if (e != Theory::EFFORT_FULL)
  {
    return true;
  }

  //  std::cout << "check" << std::endl;

  while (!d_bitblastQueue.empty())
  {
    TNode n = d_bitblastQueue.front();
    d_bitblastQueue.pop();
    d_bitblaster->bbAtom(n);
  }

  while (!done())
  {
    TNode fact = get();

    // skip facts involving integer equalities (from bv2nat)
    if (!utils::isBitblastAtom(fact))
    {
      continue;
    }

    //    std::cout << "  fact: " << fact << std::endl;
    if (d_assertions.find(fact) == d_assertions.end())
    {
      //std::cout << "add assumption: " << fact << std::endl;
      d_bitblaster->bbFormula(fact, false);
      d_assumptions.push_back(fact);
    }
    else
    {
      //std::cout << "add assertion: " << fact << std::endl;
      d_bitblaster->bbFormula(fact, true);
      d_assertionsAdded.push_back(fact);
    }
  }

  std::vector<Node> assumptions = {d_assumptions.begin(), d_assumptions.end()};

  bool ok = d_bitblaster->solve(assumptions);
  if (!ok)
  {
    setConflict();
    return false;
  }

  //  std::cout << "result: " << (ok ? "sat" : "unsat") << std::endl;
  return true;
}

EqualityStatus BitblastSolverCms::getEqualityStatus(TNode a, TNode b)
{
  return EQUALITY_UNKNOWN;
}

bool BitblastSolverCms::collectModelInfo(TheoryModel* m, bool fullModel)
{
  return d_bitblaster->collectModelInfo(m, fullModel);
}

Node BitblastSolverCms::getModelValue(TNode node)
{
  if (d_bv->d_invalidateModelCache.get())
  {
    d_bitblaster->invalidateModelCache();
  }
  d_bv->d_invalidateModelCache.set(false);
  Node value = d_bitblaster->getTermModel(node, true);
  return value;
}

void BitblastSolverCms::setConflict()
{
  Node conflict;
  std::vector<Node> ucore = d_bitblaster->getUnsatAssumptions();
  std::vector<Node> conflictAtoms;
  if (ucore.size() > 0)
  {
    for (const Node& n : ucore)
    {
      //      std::cout << "  ucore: " << n << std::endl;
      if (n.getKind() == kind::NOT)
        conflictAtoms.push_back(n[0]);
      else
        conflictAtoms.push_back(n.notNode());
    }
    conflict = utils::mkAnd(conflictAtoms);
  }
  else
  {
    std::vector<TNode> ucore = {d_assertionsAdded.begin(), d_assertionsAdded.end()};
    conflict = utils::mkAnd(ucore);
  }

  Node final_conflict = conflict;
  if (options::bitvectorQuickXplain() && conflict.getKind() == kind::AND)
  {
    final_conflict = d_quickXplain->minimizeConflict(conflict);
//    if (conflict != final_conflict)
//    {
//      std::cout << "original conflict: " << conflict << std::endl;
//      std::cout << "final conflict: " << final_conflict << std::endl;
//    }
  }
  d_bv->setConflict(final_conflict);
}

void BitblastSolverCms::setProofLog(BitVectorProof* bvp) {}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

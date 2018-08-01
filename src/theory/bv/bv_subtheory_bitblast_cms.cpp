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
      d_statistics()
{
}

BitblastSolverCms::~BitblastSolverCms() {}

BitblastSolverCms::Statistics::Statistics() {}

BitblastSolverCms::Statistics::~Statistics() {}

void BitblastSolverCms::preRegister(TNode node)
{
  //  std::cout << "pre-register: " << node << std::endl;
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

  while (!done())
  {
    TNode fact = get();

    // skip facts involving integer equalities (from bv2nat)
    if (!utils::isBitblastAtom(fact))
    {
      continue;
    }

    //    std::cout << "  fact: " << fact << std::endl;
    d_bitblaster->bbFormula(fact, false);
    d_assumptions.push_back(fact);
  }

  std::vector<Node> assumptions = {d_assumptions.begin(), d_assumptions.end()};

  bool ok = d_bitblaster->solve(assumptions);
  if (!ok)
  {
    std::vector<Node> ucore = d_bitblaster->getUnsatAssumptions();
    std::vector<Node> conflict;
    for (const Node& n : ucore)
    {
      //      std::cout << "  ucore: " << n << std::endl;
      if (n.getKind() == kind::NOT)
        conflict.push_back(n[0]);
      else
        conflict.push_back(n.notNode());
    }
    d_bv->setConflict(utils::mkAnd(conflict));
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

void BitblastSolverCms::setProofLog(BitVectorProof* bvp) {}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

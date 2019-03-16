/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andrew Reynolds, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv.h"

#include "options/bv_options.h"
#include "theory/bv/theory_bv_lazy.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_utils.h"

using namespace CVC4::context;
using namespace CVC4::theory::bv::utils;
using namespace std;

namespace CVC4 {
namespace theory {
namespace bv {

TheoryBV::TheoryBV(context::Context* c,
                   context::UserContext* u,
                   OutputChannel& out,
                   Valuation valuation,
                   const LogicInfo& logicInfo,
                   std::string name)
    : Theory(THEORY_BV, c, u, out, valuation, logicInfo, name),
      d_internal(new TheoryBVLazy(*this, c, u, out, valuation)),
      d_ufDivByZero(),
      d_ufRemByZero()
{
}

TheoryBV::~TheoryBV() {}

void TheoryBV::setMasterEqualityEngine(eq::EqualityEngine* eq)
{
  d_internal->setMasterEqualityEngine(eq);
}

void TheoryBV::finishInit() { d_internal->finishInit(); }

Node TheoryBV::getUFDivByZero(Kind k, unsigned width)
{
  NodeManager* nm = NodeManager::currentNM();
  if (k == kind::BITVECTOR_UDIV)
  {
    if (d_ufDivByZero.find(width) == d_ufDivByZero.end())
    {
      // lazily create the function symbols
      ostringstream os;
      os << "BVUDivByZero_" << width;
      Node divByZero =
          nm->mkSkolem(os.str(),
                       nm->mkFunctionType(nm->mkBitVectorType(width),
                                          nm->mkBitVectorType(width)),
                       "partial bvudiv",
                       NodeManager::SKOLEM_EXACT_NAME);
      d_ufDivByZero[width] = divByZero;
    }
    return d_ufDivByZero[width];
  }
  else if (k == kind::BITVECTOR_UREM)
  {
    if (d_ufRemByZero.find(width) == d_ufRemByZero.end())
    {
      ostringstream os;
      os << "BVURemByZero_" << width;
      Node divByZero =
          nm->mkSkolem(os.str(),
                       nm->mkFunctionType(nm->mkBitVectorType(width),
                                          nm->mkBitVectorType(width)),
                       "partial bvurem",
                       NodeManager::SKOLEM_EXACT_NAME);
      d_ufRemByZero[width] = divByZero;
    }
    return d_ufRemByZero[width];
  }

  Unreachable();
}

Node TheoryBV::expandDefinition(LogicRequest& logicRequest, Node node)
{
  Debug("bv-expand") << "TheoryBVLazy::expandDefinition(" << node << ")"
                     << std::endl;

  switch (node.getKind())
  {
    case kind::BITVECTOR_SDIV:
    case kind::BITVECTOR_SREM:
    case kind::BITVECTOR_SMOD:
      return TheoryBVRewriter::eliminateBVSDiv(node);
      break;

    case kind::BITVECTOR_UDIV:
    case kind::BITVECTOR_UREM:
    {
      NodeManager* nm = NodeManager::currentNM();
      unsigned width = node.getType().getBitVectorSize();

      if (options::bitvectorDivByZeroConst())
      {
        Kind kind = node.getKind() == kind::BITVECTOR_UDIV
                        ? kind::BITVECTOR_UDIV_TOTAL
                        : kind::BITVECTOR_UREM_TOTAL;
        return nm->mkNode(kind, node[0], node[1]);
      }

      TNode num = node[0], den = node[1];
      Node den_eq_0 = nm->mkNode(kind::EQUAL, den, utils::mkZero(width));
      Node divTotalNumDen = nm->mkNode(node.getKind() == kind::BITVECTOR_UDIV
                                           ? kind::BITVECTOR_UDIV_TOTAL
                                           : kind::BITVECTOR_UREM_TOTAL,
                                       num,
                                       den);
      Node divByZero = getUFDivByZero(node.getKind(), width);
      Node divByZeroNum = nm->mkNode(kind::APPLY_UF, divByZero, num);
      node = nm->mkNode(kind::ITE, den_eq_0, divByZeroNum, divTotalNumDen);
      logicRequest.widenLogic(THEORY_UF);
      return node;
    }
    break;

    default: return node; break;
  }

  Unreachable();
}

void TheoryBV::preRegisterTerm(TNode node)
{
  d_internal->preRegisterTerm(node);
}

void TheoryBV::check(Effort e)
{
  TimerStat::CodeTimer checkTimer(d_checkTime);
  d_internal->check(e);
}

bool TheoryBV::needsCheckLastEffort()
{
  return d_internal->needsCheckLastEffort();
}

bool TheoryBV::collectModelInfo(TheoryModel* m)
{
  return d_internal->collectModelInfo(m);
}

void TheoryBV::propagate(Effort e) { return d_internal->propagate(e); }

eq::EqualityEngine* TheoryBV::getEqualityEngine()
{
  return d_internal->getEqualityEngine();
}

bool TheoryBV::getCurrentSubstitution(int effort,
                                      std::vector<Node>& vars,
                                      std::vector<Node>& subs,
                                      std::map<Node, std::vector<Node> >& exp)
{
  return d_internal->getCurrentSubstitution(effort, vars, subs, exp);
}

int TheoryBV::getReduction(int effort, Node n, Node& nr)
{
  Trace("bv-ext") << "TheoryBVLazy::checkExt : non-reduced : " << n
                  << std::endl;
  NodeManager* const nm = NodeManager::currentNM();
  if (n.getKind() == kind::BITVECTOR_TO_NAT)
  {
    // taken from rewrite code
    const unsigned size = utils::getSize(n[0]);
    const Node z = nm->mkConst(Rational(0));
    const Node bvone = utils::mkOne(1);
    NodeBuilder<> result(kind::PLUS);
    Integer i = 1;
    for (unsigned bit = 0; bit < size; ++bit, i *= 2)
    {
      Node cond =
          nm->mkNode(kind::EQUAL,
                     nm->mkNode(nm->mkConst(BitVectorExtract(bit, bit)), n[0]),
                     bvone);
      result << nm->mkNode(kind::ITE, cond, nm->mkConst(Rational(i)), z);
    }
    nr = Node(result);
    return -1;
  }
  else if (n.getKind() == kind::INT_TO_BITVECTOR)
  {
    // taken from rewrite code
    const unsigned size = n.getOperator().getConst<IntToBitVector>().size;
    const Node bvzero = utils::mkZero(1);
    const Node bvone = utils::mkOne(1);
    std::vector<Node> v;
    Integer i = 2;
    while (v.size() < size)
    {
      Node cond = nm->mkNode(
          kind::GEQ,
          nm->mkNode(kind::INTS_MODULUS_TOTAL, n[0], nm->mkConst(Rational(i))),
          nm->mkConst(Rational(i, 2)));
      cond = Rewriter::rewrite(cond);
      v.push_back(nm->mkNode(kind::ITE, cond, bvone, bvzero));
      i *= 2;
    }
    NodeBuilder<> result(kind::BITVECTOR_CONCAT);
    result.append(v.rbegin(), v.rend());
    nr = Node(result);
    return -1;
  }
  return 0;
}

Theory::PPAssertStatus TheoryBV::ppAssert(TNode in,
                                          SubstitutionMap& outSubstitutions)
{
  return d_internal->ppAssert(in, outSubstitutions);
}

void TheoryBV::enableCoreTheorySlicer()
{
  d_internal->enableCoreTheorySlicer();
}

Node TheoryBV::ppRewrite(TNode t) { return d_internal->ppRewrite(t); }

void TheoryBV::presolve() { d_internal->presolve(); }

Node TheoryBV::explain(TNode node) { return d_internal->explain(node); }

void TheoryBV::addSharedTerm(TNode node)
{
  return d_internal->addSharedTerm(node);
}

void TheoryBV::ppStaticLearn(TNode in, NodeBuilder<>& learned)
{
  d_internal->ppStaticLearn(in, learned);
}

bool TheoryBV::applyAbstraction(const std::vector<Node>& assertions,
                                std::vector<Node>& new_assertions)
{
  return d_internal->applyAbstraction(assertions, new_assertions);
}

void TheoryBV::setProofLog(proof::BitVectorProof* bvp)
{
  d_internal->setProofLog(bvp);
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

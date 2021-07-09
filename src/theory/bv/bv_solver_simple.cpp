/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Gereon Kremer, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple bit-blast solver that sends bitblast lemmas directly to MiniSat.
 */

#include "theory/bv/bv_solver_simple.h"

#include "proof/conv_proof_generator.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

namespace {

bool isBVAtom(TNode n)
{
  return (n.getKind() == kind::EQUAL && n[0].getType().isBitVector())
         || n.getKind() == kind::BITVECTOR_ULT
         || n.getKind() == kind::BITVECTOR_ULE
         || n.getKind() == kind::BITVECTOR_SLT
         || n.getKind() == kind::BITVECTOR_SLE;
}

/* Traverse Boolean nodes and collect BV atoms. */
void collectBVAtoms(TNode n, std::unordered_set<Node>& atoms)
{
  std::vector<TNode> visit;
  std::unordered_set<TNode> visited;

  visit.push_back(n);

  do
  {
    TNode cur = visit.back();
    visit.pop_back();

    if (visited.find(cur) != visited.end() || !cur.getType().isBoolean())
      continue;

    visited.insert(cur);
    if (isBVAtom(cur))
    {
      atoms.insert(cur);
      continue;
    }

    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
}

}  // namespace

BVSolverSimple::BVSolverSimple(TheoryState* s,
                               TheoryInferenceManager& inferMgr,
                               ProofNodeManager* pnm)
    : BVSolver(*s, inferMgr),
      d_tcpg(pnm ? new TConvProofGenerator(
                 pnm,
                 nullptr,
                 /* ONCE to visit each term only once, post-order.  FIXPOINT
                  * could lead to infinite loops due to terms being rewritten
                  * to terms that contain themselves */
                 TConvPolicy::ONCE,
                 /* STATIC to get the same ProofNode for a shared subterm. */
                 TConvCachePolicy::STATIC,
                 "BVSolverSimple::TConvProofGenerator",
                 nullptr,
                 false)
                 : nullptr),
      d_bitblaster(new BBProof(s, pnm, d_tcpg.get()))
{
}

void BVSolverSimple::addBBLemma(TNode fact)
{
  if (!d_bitblaster->hasBBAtom(fact))
  {
    d_bitblaster->bbAtom(fact);
  }
  NodeManager* nm = NodeManager::currentNM();

  Node atom_bb = d_bitblaster->getStoredBBAtom(fact);
  Node lemma = nm->mkNode(kind::EQUAL, fact, atom_bb);

  if (d_tcpg == nullptr)
  {
    d_im.lemma(lemma, InferenceId::BV_SIMPLE_BITBLAST_LEMMA);
  }
  else
  {
    TrustNode tlem = TrustNode::mkTrustLemma(lemma, d_tcpg.get());
    d_im.trustedLemma(tlem, InferenceId::BV_SIMPLE_BITBLAST_LEMMA);
  }
}

bool BVSolverSimple::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (fact.getKind() == kind::NOT)
  {
    fact = fact[0];
  }

  if (isBVAtom(fact))
  {
    addBBLemma(fact);
  }
  else if (fact.getKind() == kind::BITVECTOR_EAGER_ATOM)
  {
    TNode n = fact[0];

    NodeManager* nm = NodeManager::currentNM();
    Node lemma = nm->mkNode(kind::EQUAL, fact, n);

    if (d_tcpg == nullptr)
    {
      d_im.lemma(lemma, InferenceId::BV_SIMPLE_LEMMA);
    }
    else
    {
      TrustNode tlem = TrustNode::mkTrustLemma(lemma, d_tcpg.get());
      d_im.trustedLemma(tlem, InferenceId::BV_SIMPLE_LEMMA);
    }

    std::unordered_set<Node> bv_atoms;
    collectBVAtoms(n, bv_atoms);
    for (const Node& nn : bv_atoms)
    {
      addBBLemma(nn);
    }
  }

  return true;
}

Node BVSolverSimple::getValueFromSatSolver(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }

  if (!d_bitblaster->hasBBTerm(node))
  {
    return initialize ? utils::mkConst(utils::getSize(node), 0u) : Node();
  }

  Valuation& val = d_state.getValuation();

  std::vector<Node> bits;
  d_bitblaster->getBBTerm(node, bits);
  Integer value(0), one(1), zero(0), bit;
  for (size_t i = 0, size = bits.size(), j = size - 1; i < size; ++i, --j)
  {
    bool satValue;
    if (val.hasSatValue(bits[j], satValue))
    {
      bit = satValue ? one : zero;
    }
    else
    {
      if (!initialize) return Node();
      bit = zero;
    }
    value = value * 2 + bit;
  }
  return utils::mkConst(bits.size(), value);
}

Node BVSolverSimple::getValue(TNode node)
{
  std::vector<TNode> visit;
  std::unordered_map<Node, Node> modelCache;

  TNode cur;
  visit.push_back(node);
  do
  {
    cur = visit.back();
    visit.pop_back();

    auto it = modelCache.find(cur);
    if (it != modelCache.end() && !it->second.isNull())
    {
      continue;
    }

    if (d_bitblaster->hasBBTerm(cur))
    {
      Node value = getValueFromSatSolver(cur, false);
      if (value.isConst())
      {
        modelCache[cur] = value;
        continue;
      }
    }
    if (Theory::isLeafOf(cur, theory::THEORY_BV))
    {
      Node value = getValueFromSatSolver(cur, true);
      modelCache[cur] = value;
      continue;
    }

    if (it == modelCache.end())
    {
      visit.push_back(cur);
      modelCache.emplace(cur, Node());
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      NodeBuilder nb(cur.getKind());
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        nb << cur.getOperator();
      }

      std::unordered_map<Node, Node>::iterator iit;
      for (const TNode& child : cur)
      {
        iit = modelCache.find(child);
        Assert(iit != modelCache.end());
        Assert(iit->second.isConst());
        nb << iit->second;
      }
      it->second = Rewriter::rewrite(nb.constructNode());
    }
  } while (!visit.empty());

  auto it = modelCache.find(node);
  Assert(it != modelCache.end());
  return it->second;
}

EqualityStatus BVSolverSimple::getEqualityStatus(TNode a, TNode b)
{
  Debug("bv-simple") << "getEqualityStatus on " << a << " and " << b
                     << std::endl;
  Node value_a = getValue(a);
  Node value_b = getValue(b);

  if (value_a.isNull() || value_b.isNull())
  {
    return EQUALITY_UNKNOWN;
  }

  if (value_a == value_b)
  {
    Debug("bv-simple") << EQUALITY_TRUE_IN_MODEL << std::endl;
    return EQUALITY_TRUE_IN_MODEL;
  }
  Debug("bv-simple") << EQUALITY_FALSE_IN_MODEL << std::endl;
  return EQUALITY_FALSE_IN_MODEL;
}

bool BVSolverSimple::collectModelValues(TheoryModel* m,
                                        const std::set<Node>& termSet)
{
  return d_bitblaster->collectModelValues(m, termSet);
}

BVProofRuleChecker* BVSolverSimple::getProofChecker() { return &d_checker; }

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arrays inference manager.
 */

#include "theory/arrays/inference_manager.h"

#include "options/smt_options.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_id.h"
#include "theory/arrays/infer_proof_cons.h"
#include "theory/builtin/proof_checker.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arrays {

InferenceManager::~InferenceManager() {}

InferenceManager::InferenceManager(Env& env, Theory& t, TheoryState& state)
    : TheoryInferenceManager(env, t, state, "theory::arrays::", false),
      d_lemmaPg(isProofEnabled() ? new EagerProofGenerator(
                    env, userContext(), "ArrayLemmaProofGenerator")
                                 : nullptr),
      d_ipc(isProofEnabled()
                ? new ArraysInferProofCons(env, context())
                : nullptr)
{
}

bool InferenceManager::isAextInference(InferenceId id)
{
  switch (id)
  {
    case InferenceId::ARRAYS_AEXT_CONGRUENCE:
    case InferenceId::ARRAYS_AEXT_ROW:
    case InferenceId::ARRAYS_AEXT_DISEQUALITY:
    case InferenceId::ARRAYS_AEXT_INDEX_SPLIT:
    case InferenceId::ARRAYS_CONST_ARRAY_DEFAULT:
      return true;
    default: return false;
  }
}

bool InferenceManager::assertInference(
    TNode atom, bool polarity, InferenceId id, TNode reason, ProofRule pfr)
{
  Trace("arrays-infer") << "TheoryArrays::assertInference: "
                        << (polarity ? Node(atom) : atom.notNode()) << " by "
                        << reason << "; " << id << std::endl;
  Assert(atom.getKind() == Kind::EQUAL);
  if (isProofEnabled())
  {
    Node fact = polarity ? Node(atom) : atom.notNode();
    // For AEXT inferences (and RIntro2 which uses ARRAYS_READ_OVER_WRITE),
    // use the lazy proof constructor.
    if (isAextInference(id) || id == InferenceId::ARRAYS_READ_OVER_WRITE)
    {
      // Flatten reason into a vector of individual literals.
      std::vector<Node> expVec;
      if (reason.getKind() == Kind::AND)
      {
        for (const Node& c : reason)
        {
          expVec.push_back(c);
        }
      }
      else if (!reason.isConst())
      {
        expVec.push_back(reason);
      }
      d_ipc->notifyFact(fact, reason, id);
      return assertInternalFact(atom, polarity, id, expVec, d_ipc.get());
    }
    // Default solver path: use the old convert() method.
    std::vector<Node> children;
    std::vector<Node> args;
    convert(pfr, fact, reason, children, args);
    return assertInternalFact(atom, polarity, id, pfr, children, args);
  }
  return assertInternalFact(atom, polarity, id, reason);
}

bool InferenceManager::arrayLemma(
    Node conc, InferenceId id, Node exp, ProofRule pfr, LemmaProperty p)
{
  // Delegate to the overload with empty paths.
  return arrayLemma(conc, id, exp, pfr, {}, p);
}

bool InferenceManager::arrayLemma(
    Node conc,
    InferenceId id,
    Node exp,
    ProofRule pfr,
    std::vector<std::vector<PathEdge>>&& paths,
    LemmaProperty p)
{
  Trace("arrays-infer") << "TheoryArrays::arrayLemma: " << conc << " by " << exp
                        << "; " << id << std::endl;
  NodeManager* nm = nodeManager();
  if (isProofEnabled())
  {
    // For AEXT inferences (and RIntro2), build proof eagerly via the
    // proof constructor, following the datatypes processDtLemma pattern.
    if (isAextInference(id) || id == InferenceId::ARRAYS_READ_OVER_WRITE)
    {
      // Create a local (non-context-dependent) proof constructor.
      // We must build the proof eagerly while EE state is still valid.
      ArraysInferProofCons ipcLocal(d_env, nullptr);
      if (paths.empty())
      {
        ipcLocal.notifyFact(conc, exp, id);
      }
      else
      {
        ipcLocal.notifyFact(conc, exp, id, std::move(paths));
      }
      std::shared_ptr<ProofNode> pbody = ipcLocal.getProofFor(conc);
      std::shared_ptr<ProofNode> pn = pbody;
      // Wrap with SCOPE over the flattened explanation.
      if (!exp.isNull() && !exp.isConst())
      {
        std::vector<Node> expv;
        if (exp.getKind() == Kind::AND)
        {
          for (const Node& c : exp)
          {
            expv.push_back(c);
          }
        }
        else
        {
          expv.push_back(exp);
        }
        pn = d_env.getProofNodeManager()->mkScope(pbody, expv);
      }
      // Use the scoped proof's result as the lemma (mkScope may have
      // deduplicated or reordered the explanation literals).
      Node lem = pn->getResult();
      d_lemmaPg->setProofFor(lem, pn);
      return trustedLemma(
          TrustNode::mkTrustLemma(lem, d_lemmaPg.get()), id, p);
    }
    // Default solver path: use convert().
    std::vector<Node> children;
    std::vector<Node> args;
    convert(pfr, conc, exp, children, args);
    TrustNode tlem = d_lemmaPg->mkTrustNode(conc, pfr, children, args);
    return trustedLemma(tlem, id, p);
  }
  // No proofs: send lemma directly.
  Node lem = nm->mkNode(Kind::IMPLIES, exp, conc);
  return lemma(lem, id, p);
}

void InferenceManager::convert(ProofRule& id,
                               Node conc,
                               Node exp,
                               std::vector<Node>& children,
                               std::vector<Node>& args)
{
  // note that children must contain something equivalent to exp,
  // regardless of the ProofRule.
  switch (id)
  {
    case ProofRule::MACRO_SR_PRED_INTRO:
      Assert(exp.isConst());
      args.push_back(conc);
      break;
    case ProofRule::ARRAYS_READ_OVER_WRITE:
      if (exp.isConst())
      {
        // Premise can be shown by rewriting, use standard predicate intro rule.
        // This is the case where we have 2 constant indices.
        id = ProofRule::MACRO_SR_PRED_INTRO;
        args.push_back(conc);
      }
      else
      {
        children.push_back(exp);
        args.push_back(conc[0]);
      }
      break;
    case ProofRule::ARRAYS_READ_OVER_WRITE_CONTRA:
      children.push_back(exp);
      break;
    case ProofRule::ARRAYS_READ_OVER_WRITE_1:
      Assert(exp.isConst());
      args.push_back(conc[0]);
      break;
    case ProofRule::ARRAYS_EXT:
      // since this rule depends on the ARRAY_DEQ_DIFF skolem which sorts
      // indices, we assert that the equality is ordered here, which it should
      // be based on the standard order for equality.
      Assert(exp.getKind() == Kind::NOT && exp[0].getKind() == Kind::EQUAL
             && exp[0][0] < exp[0][1]);
      children.push_back(exp);
      break;
    default:
      if (id != ProofRule::TRUST)
      {
        DebugUnhandled() << "Unknown rule " << id << "\n";
      }
      children.push_back(exp);
      args.push_back(mkTrustId(nodeManager(), TrustId::THEORY_INFERENCE_ARRAYS));
      args.push_back(conc);
      id = ProofRule::TRUST;
      break;
  }
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

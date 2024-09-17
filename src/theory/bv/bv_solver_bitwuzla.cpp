/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blasting solver that supports multiple SAT backends.
 */

#include "theory/bv/bv_solver_bitwuzla.h"

#include "options/bv_options.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Notifies the BV solver when assertions were reset.
 *
 * This class is notified after every user-context pop and maintains a flag
 * that indicates whether assertions have been reset. If the user-context level
 * reaches level 0 it means that the assertions were reset.
 */
class NotifyResetAssertions : public context::ContextNotifyObj
{
 public:
  NotifyResetAssertions(context::Context* c)
      : context::ContextNotifyObj(c, false),
        d_context(c),
        d_doneResetAssertions(false)
  {
  }

  bool doneResetAssertions() { return d_doneResetAssertions; }

  void reset() { d_doneResetAssertions = false; }

 protected:
  void contextNotifyPop() override
  {
    // If the user-context level reaches 0 it means that reset-assertions was
    // called.
    if (d_context->getLevel() == 0)
    {
      d_doneResetAssertions = true;
    }
  }

 private:
  /** The user-context. */
  context::Context* d_context;

  /** Flag to notify whether reset assertions was called. */
  bool d_doneResetAssertions;
};

BVSolverBitwuzla::BVSolverBitwuzla(Env& env,
                                   TheoryState* s,
                                   TheoryInferenceManager& inferMgr)
    : BVSolver(env, *s, inferMgr),
      d_bbFacts(context()),
      d_bbInputFacts(context()),
      d_assumptions(context()),
      d_assertions(context()),
      d_factLiteralCache(context()),
      d_literalFactCache(context()),
      d_propagate(options().bv.bitvectorPropagate),
      d_resetNotify(new NotifyResetAssertions(userContext()))
{
  initSatSolver();
}

bool BVSolverBitwuzla::needsEqualityEngine(EeSetupInfo& esi)
{
  // we always need the equality engine if sharing is enabled for processing
  // equality engine and shared terms
  return logicInfo().isSharingEnabled() || options().bv.bvEqEngine;
}

void BVSolverBitwuzla::postCheck(Theory::Effort level)
{
  if (level != Theory::Effort::EFFORT_FULL)
  {
    /* Do bit-level propagation only if the SAT solver supports it. */
    /*if (!d_propagate || !d_satSolver->setPropagateOnly())*/
    /*{*/
    /*  return;*/
    /*}*/
  }

  // If we permanently added assertions to the SAT solver and the assertions
  // were reset, we have to reset the SAT solver and the CNF stream.
  if (options().bv.bvAssertInput && d_resetNotify->doneResetAssertions())
  {
    // d_satSolver.reset(nullptr);
    // d_cnfStream.reset(nullptr);
    d_bitwuzla.reset(nullptr);
    initSatSolver();
    d_resetNotify->reset();
  }

  /* Process input assertions bit-blast queue. */
  while (!d_bbInputFacts.empty())
  {
    Node fact = d_bbInputFacts.front();
    d_bbInputFacts.pop();
    /* Bit-blast fact and cache literal. */
    auto translated = translate(fact);
    d_assertions.push_back(fact);
    d_literalFactCache[translated] = fact;
    d_factLiteralCache[fact] = translated;
  }

  /* Process bit-blast queue and store SAT literals. */
  while (!d_bbFacts.empty())
  {
    Node fact = d_bbFacts.front();
    d_bbFacts.pop();
    auto translated = translate(fact);
    d_assumptions.push_back(translated);
    d_literalFactCache[translated] = fact;
    d_factLiteralCache[fact] = translated;
  }

  std::vector<bitwuzla::Term> assumptions(d_assumptions.begin(),
                                          d_assumptions.end());
  bitwuzla::Result res = d_bitwuzla->check_sat(assumptions);

  if (res == bitwuzla::Result::UNSAT)
  {
    auto nm = d_env.getNodeManager();
    auto unsat_assumptions = d_bitwuzla->get_unsat_assumptions();

    Node conflict;
    // Unsat assumptions produce conflict.
    if (unsat_assumptions.size() > 0)
    {
      std::vector<Node> conf;
      for (const auto& a : unsat_assumptions)
      {
        conf.push_back(d_literalFactCache[a]);
        // Trace("bv-bitblast")
        //     << "unsat assumption (" << lit << "): " << conf.back() <<
        //     std::endl;
      }
      conflict = nm->mkAnd(conf);
    }
    else  // Input assertions produce conflict.
    {
      std::vector<Node> assertions(d_assertions.begin(), d_assertions.end());
      conflict = nm->mkAnd(assertions);
    }
    d_im.conflict(conflict, InferenceId::BV_BITBLAST_CONFLICT);
  }
}

bool BVSolverBitwuzla::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Valuation& val = d_state.getValuation();

  /**
   * Check whether `fact` is an input assertion on user-level 0.
   *
   * If this is the case we can assert `fact` to the SAT solver instead of
   * using assumptions.
   */
  if (options().bv.bvAssertInput && val.isFixed(fact))
  {
    Assert(!val.isDecision(fact));
    d_bbInputFacts.push_back(fact);
  }
  else
  {
    d_bbFacts.push_back(fact);
  }

  // Return false to enable equality engine reasoning in Theory, which is
  // available if we are using the equality engine.
  return !logicInfo().isSharingEnabled() && !options().bv.bvEqEngine;
}

TrustNode BVSolverBitwuzla::explain(TNode n)
{
  Trace("bv-bitblast") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
}

void BVSolverBitwuzla::computeRelevantTerms(std::set<Node>& termSet)
{
  /* BITVECTOR_EAGER_ATOM wraps input assertions that may also contain
   * equalities. As a result, these equalities are not handled by the equality
   * engine and terms below these equalities do not appear in `termSet`.
   * We need to make sure that we compute model values for all relevant terms
   * in BitblastMode::EAGER and therefore add all variables from the
   * bit-blaster to `termSet`.
   */
  // if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  //{
  //   d_bitblaster->computeRelevantTerms(termSet);
  // }
  //  TODO:
  Assert(false);
}

bool BVSolverBitwuzla::collectModelValues(TheoryModel* m,
                                          const std::set<Node>& termSet)
{
  Assert(false);
  /*for (const auto& term : termSet)*/
  /*{*/
  /*  if (!d_bitblaster->isVariable(term))*/
  /*  {*/
  /*    continue;*/
  /*  }*/
  /**/
  /*  Node value = getValue(term, true);*/
  /*  Assert(value.isConst());*/
  /*  if (!m->assertEquality(term, value, true))*/
  /*  {*/
  /*    return false;*/
  /*  }*/
  /*}*/
  /**/
  /*// In eager bitblast mode we also have to collect the model values for*/
  /*// Boolean variables in the CNF stream.*/
  /*if (options().bv.bitblastMode == options::BitblastMode::EAGER)*/
  /*{*/
  /*  NodeManager* nm = nodeManager();*/
  /*  std::vector<TNode> vars;*/
  /*  d_cnfStream->getBooleanVariables(vars);*/
  /*  for (TNode var : vars)*/
  /*  {*/
  /*    Assert(d_cnfStream->hasLiteral(var));*/
  /*    prop::SatLiteral bit = d_cnfStream->getLiteral(var);*/
  /*    prop::SatValue value = d_satSolver->modelValue(bit);*/
  /*    Assert(value != prop::SAT_VALUE_UNKNOWN);*/
  /*    if (!m->assertEquality(*/
  /*            var, nm->mkConst(value == prop::SAT_VALUE_TRUE), true))*/
  /*    {*/
  /*      return false;*/
  /*    }*/
  /*  }*/
  /*}*/
  /**/
  return true;
}

void BVSolverBitwuzla::initSatSolver()
{
  bitwuzla::Options opts;
  opts.set(bitwuzla::Option::PRODUCE_UNSAT_ASSUMPTIONS, true);
  d_bitwuzla.reset(new bitwuzla::Bitwuzla(d_bitwuzla_tm, opts));
}

namespace {
std::unordered_map<Kind, bitwuzla::Kind> kindmap = {
    {Kind::NOT, bitwuzla::Kind::NOT},
    {Kind::AND, bitwuzla::Kind::AND},
    {Kind::OR, bitwuzla::Kind::OR},
    {Kind::XOR, bitwuzla::Kind::XOR},
    {Kind::IMPLIES, bitwuzla::Kind::IMPLIES},
    {Kind::EQUAL, bitwuzla::Kind::EQUAL},
    {Kind::ITE, bitwuzla::Kind::ITE},
    {Kind::BITVECTOR_ULT, bitwuzla::Kind::BV_ULT},
    {Kind::BITVECTOR_ULE, bitwuzla::Kind::BV_ULE},
    {Kind::BITVECTOR_UGT, bitwuzla::Kind::BV_UGT},
    {Kind::BITVECTOR_UGE, bitwuzla::Kind::BV_UGE},
    {Kind::BITVECTOR_SLT, bitwuzla::Kind::BV_SLT},
    {Kind::BITVECTOR_SLE, bitwuzla::Kind::BV_SLE},
    {Kind::BITVECTOR_SGT, bitwuzla::Kind::BV_SGT},
    {Kind::BITVECTOR_SGE, bitwuzla::Kind::BV_SGE},
    {Kind::BITVECTOR_NOT, bitwuzla::Kind::BV_NOT},
    {Kind::BITVECTOR_CONCAT, bitwuzla::Kind::BV_CONCAT},
    {Kind::BITVECTOR_AND, bitwuzla::Kind::BV_AND},
    {Kind::BITVECTOR_OR, bitwuzla::Kind::BV_OR},
    {Kind::BITVECTOR_XOR, bitwuzla::Kind::BV_XOR},
    {Kind::BITVECTOR_XNOR, bitwuzla::Kind::BV_XNOR},
    {Kind::BITVECTOR_NAND, bitwuzla::Kind::BV_NAND},
    {Kind::BITVECTOR_NOR, bitwuzla::Kind::BV_NOR},
    {Kind::BITVECTOR_COMP, bitwuzla::Kind::BV_COMP},
    {Kind::BITVECTOR_MULT, bitwuzla::Kind::BV_MUL},
    {Kind::BITVECTOR_ADD, bitwuzla::Kind::BV_ADD},
    {Kind::BITVECTOR_SUB, bitwuzla::Kind::BV_SUB},
    {Kind::BITVECTOR_NEG, bitwuzla::Kind::BV_NEG},
    {Kind::BITVECTOR_UDIV, bitwuzla::Kind::BV_UDIV},
    {Kind::BITVECTOR_UREM, bitwuzla::Kind::BV_UREM},
    {Kind::BITVECTOR_SHL, bitwuzla::Kind::BV_SHL},
    {Kind::BITVECTOR_LSHR, bitwuzla::Kind::BV_SHR},
    {Kind::BITVECTOR_ASHR, bitwuzla::Kind::BV_ASHR},
    {Kind::BITVECTOR_EXTRACT, bitwuzla::Kind::BV_EXTRACT},
    {Kind::BITVECTOR_REPEAT, bitwuzla::Kind::BV_REPEAT},
    {Kind::BITVECTOR_ZERO_EXTEND, bitwuzla::Kind::BV_ZERO_EXTEND},
    {Kind::BITVECTOR_SIGN_EXTEND, bitwuzla::Kind::BV_SIGN_EXTEND},
    {Kind::BITVECTOR_ROTATE_RIGHT, bitwuzla::Kind::BV_ROR},
    {Kind::BITVECTOR_ROTATE_LEFT, bitwuzla::Kind::BV_ROL}};
}

const bitwuzla::Term& BVSolverBitwuzla::translate(const Node& n)
{
  std::vector<TNode> visit;
  if (n.getKind() == Kind::BITVECTOR_EAGER_ATOM)
  {
    visit.push_back(n[0]);
  }
  else
  {
    visit.push_back(n);
  }
  do
  {
    TNode cur = visit.back();

    auto [it, inserted] = d_translation_cache.emplace(cur, bitwuzla::Term());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      auto k = cur.getKind();

      bitwuzla::Term translated;
      if (k == Kind::CONST_BITVECTOR)
      {
        uint64_t size = utils::getSize(cur);
        bitwuzla::Sort bvsort = d_bitwuzla_tm.mk_bv_sort(size);
        const BitVector& bv = cur.getConst<BitVector>();
        std::string value = bv.toString(2);
        translated = d_bitwuzla_tm.mk_bv_value(bvsort, value, 2);
      }
      else if (kindmap.find(k) != kindmap.end())
      {
        std::vector<bitwuzla::Term> children;
        for (const auto& c : cur)
        {
          auto iit = d_translation_cache.find(c);
          Assert(iit != d_translation_cache.end());
          children.push_back(iit->second);
        }

        std::vector<uint64_t> indices;
        if (cur.getKind() == Kind::BITVECTOR_EXTRACT)
        {
          indices.push_back(utils::getExtractHigh(cur));
          indices.push_back(utils::getExtractLow(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_SIGN_EXTEND)
        {
          indices.push_back(utils::getSignExtendAmount(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_ZERO_EXTEND)
        {
          indices.push_back(utils::getZeroExtendAmount(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_ROTATE_LEFT)
        {
          indices.push_back(utils::getRotateLeftAmount(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_ROTATE_RIGHT)
        {
          indices.push_back(utils::getRotateRightAmount(cur));
        }

        translated = d_bitwuzla_tm.mk_term(kindmap[k], children, indices);
      }
      else
      {
        bitwuzla::Sort sort;
        if (cur.getType().isBoolean())
        {
          sort = d_bitwuzla_tm.mk_bool_sort();
        }
        else
        {
          uint64_t size = utils::getSize(cur);
          sort = d_bitwuzla_tm.mk_bv_sort(size);
        }
        translated = d_bitwuzla_tm.mk_const(sort);
      }
      it->second = translated;
    }
    visit.pop_back();
  } while (!visit.empty());

  if (n.getKind() == Kind::BITVECTOR_EAGER_ATOM)
  {
    auto it = d_translation_cache.find(n[0]);
    Assert(it != d_translation_cache.end());
    return it->second;
  }
  auto it = d_translation_cache.find(n);
  Assert(it != d_translation_cache.end());
  return it->second;
}

Node BVSolverBitwuzla::getValue(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }
  Assert(false);
  return Node();
  /**/
  /*if (!d_bitblaster->hasBBTerm(node))*/
  /*{*/
  /*  return initialize ? utils::mkConst(utils::getSize(node), 0u) : Node();*/
  /*}*/
  /**/
  /*std::vector<Node> bits;*/
  /*d_bitblaster->getBBTerm(node, bits);*/
  /*Integer value(0), one(1), zero(0), bit;*/
  /*for (size_t i = 0, size = bits.size(), j = size - 1; i < size; ++i, --j)*/
  /*{*/
  /*  if (d_cnfStream->hasLiteral(bits[j]))*/
  /*  {*/
  /*    prop::SatLiteral lit = d_cnfStream->getLiteral(bits[j]);*/
  /*    prop::SatValue val = d_satSolver->modelValue(lit);*/
  /*    bit = val == prop::SatValue::SAT_VALUE_TRUE ? one : zero;*/
  /*  }*/
  /*  else*/
  /*  {*/
  /*    if (!initialize) return Node();*/
  /*    bit = zero;*/
  /*  }*/
  /*  value = value * 2 + bit;*/
  /*}*/
  /*return utils::mkConst(bits.size(), value);*/
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

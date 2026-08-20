/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of arrays.
 *
 * Thin wrapper that delegates solver-specific work to ArraySolver.
 */

#include "theory/arrays/theory_arrays.h"

#include <map>
#include <memory>

#include "expr/array_store_all.h"
#include "expr/kind.h"
#include "expr/node_algorithm.h"
#include "options/arrays_options.h"
#include "options/smt_options.h"
#include "proof/proof_checker.h"
#include "smt/logic_exception.h"
#include "theory/arrays/aext_solver.h"
#include "theory/arrays/array_solver_default.h"
#include "theory/arrays/skolem_cache.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/decision_manager.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "theory/valuation.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arrays {

// These are the options that produce the best empirical results on QF_AX
// benchmarks.
const bool d_ccStore = false;
const bool d_preprocess = true;
const bool d_solveWrite = true;
const bool d_solveWrite2 = false;

static inline std::string spaces(int level)
{
  std::string indentStr(level, ' ');
  return indentStr;
}

TheoryArrays::TheoryArrays(Env& env,
                           OutputChannel& out,
                           Valuation valuation,
                           std::string name)
    : Theory(THEORY_ARRAYS, env, out, valuation, name),
      d_numSharedArrayVarSplits(statisticsRegistry().registerInt(
          name + "number of shared array var splits")),
      d_ppEqualityEngine(env, userContext(), name + "pp", true),
      d_ppFacts(userContext()),
      d_rewriter(env.getNodeManager(), env.getRewriter()),
      d_state(env, valuation),
      d_im(env, *this, d_state),
      d_isPreRegistered(context()),
      d_mayEqualEqualityEngine(env, context(), name + "mayEqual", true),
      d_notify(*this),
      d_checker(nodeManager()),
      d_sharedArrays(context()),
      d_sharedOther(context()),
      d_sharedTerms(context(), false),
      d_modelConstraints(context()),
      d_defValues(context())
{
  d_true = nodeManager()->mkConst<bool>(true);
  d_false = nodeManager()->mkConst<bool>(false);

  // The preprocessing congruence kinds
  d_ppEqualityEngine.addFunctionKind(Kind::SELECT);
  d_ppEqualityEngine.addFunctionKind(Kind::STORE);

  // indicate we are using the default theory state object, and the arrays
  // inference manager
  d_theoryState = &d_state;
  d_inferManager = &d_im;

  // Construct the internal solver based on the option
  if (options().arrays.arraysSolver == options::ArraysSolverMode::AEXT)
  {
    d_internal.reset(new AextArraySolver(env,
                                         d_state,
                                         d_im,
                                         d_valuation,
                                         d_mayEqualEqualityEngine,
                                         d_defValues,
                                         d_sharedTerms));
  }
  else
  {
    d_internal.reset(new ArraySolverDefault(
        env,
        d_state,
        d_im,
        d_valuation,
        d_mayEqualEqualityEngine,
        d_defValues,
        d_sharedTerms,
        out,
        [this](TNode n) { preRegisterTermInternal(n); }));
  }
}

TheoryArrays::~TheoryArrays() {}

TheoryRewriter* TheoryArrays::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryArrays::getProofChecker() { return &d_checker; }

bool TheoryArrays::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = d_instanceName + "ee";
  esi.d_notifyNewClass = true;
  esi.d_notifyMerge = true;
  return true;
}

void TheoryArrays::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(Kind::SELECT);
  if (d_ccStore)
  {
    d_equalityEngine->addFunctionKind(Kind::STORE);
  }

  d_internal->finishInit(d_equalityEngine);
}

/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////

bool TheoryArrays::ppDisequal(TNode a, TNode b)
{
  bool termsExist =
      d_ppEqualityEngine.hasTerm(a) && d_ppEqualityEngine.hasTerm(b);
  Assert(!termsExist || !a.isConst() || !b.isConst() || a == b
         || d_ppEqualityEngine.areDisequal(a, b, false));
  return ((termsExist && d_ppEqualityEngine.areDisequal(a, b, false))
          || rewrite(a.eqNode(b)) == d_false);
}

Node TheoryArrays::solveWrite(TNode term,
                              bool solve1,
                              bool solve2,
                              bool ppCheck)
{
  if (!solve1)
  {
    return term;
  }
  if (term[0].getKind() != Kind::STORE && term[1].getKind() != Kind::STORE)
  {
    return term;
  }
  TNode left = term[0];
  TNode right = term[1];
  int leftWrites = 0, rightWrites = 0;

  TNode e1 = left;
  while (e1.getKind() == Kind::STORE)
  {
    ++leftWrites;
    e1 = e1[0];
  }

  TNode e2 = right;
  while (e2.getKind() == Kind::STORE)
  {
    ++rightWrites;
    e2 = e2[0];
  }

  if (rightWrites > leftWrites)
  {
    TNode tmp = left;
    left = right;
    right = tmp;
    int tmpWrites = leftWrites;
    leftWrites = rightWrites;
    rightWrites = tmpWrites;
  }

  NodeManager* nm = nodeManager();
  if (rightWrites == 0)
  {
    if (e1 != e2)
    {
      return term;
    }
    TNode write_i, write_j, index_i, index_j;
    Node conc;
    NodeBuilder result(nm, Kind::AND);
    int i, j;
    write_i = left;
    for (i = leftWrites - 1; i >= 0; --i)
    {
      index_i = write_i[1];
      write_j = left;
      {
        NodeBuilder hyp(nm, Kind::AND);
        for (j = leftWrites - 1; j > i; --j)
        {
          index_j = write_j[1];
          if (!ppCheck || !ppDisequal(index_i, index_j))
          {
            Node hyp2(index_i.eqNode(index_j));
            hyp << hyp2.notNode();
          }
          write_j = write_j[0];
        }

        Node r1 = nm->mkNode(Kind::SELECT, e1, index_i);
        conc = r1.eqNode(write_i[2]);
        if (hyp.getNumChildren() != 0)
        {
          if (hyp.getNumChildren() == 1)
          {
            conc = hyp.getChild(0).impNode(conc);
          }
          else
          {
            r1 = hyp;
            conc = r1.impNode(conc);
          }
        }
        result << conc;
        write_i = write_i[0];
      }
    }
    Assert(result.getNumChildren() > 0);
    if (result.getNumChildren() == 1)
    {
      return result.getChild(0);
    }
    return result;
  }
  else
  {
    if (!solve2)
    {
      return term;
    }
    Node l = left;
    Node tmp;
    NodeBuilder nb(nm, Kind::AND);
    while (right.getKind() == Kind::STORE)
    {
      tmp = nm->mkNode(Kind::SELECT, l, right[1]);
      nb << tmp.eqNode(right[2]);
      tmp = nm->mkNode(Kind::SELECT, right[0], right[1]);
      l = nm->mkNode(Kind::STORE, l, right[1], tmp);
      right = right[0];
    }
    nb << solveWrite(l.eqNode(right), solve1, solve2, ppCheck);
    return nb;
  }
  Unreachable();
  return term;
}

TrustNode TheoryArrays::ppRewrite(TNode term,
                                  CVC5_UNUSED std::vector<SkolemLemma>& lems)
{
  Kind k = term.getKind();
  if (!options().arrays.arraysExp)
  {
    if (k == Kind::EQ_RANGE
        || (k == Kind::STORE_ALL
            && options().arrays.arraysSolver
                   != options::ArraysSolverMode::AEXT))
    {
      std::stringstream ss;
      ss << "Term of kind `" << k
         << "` not supported in default mode, try `--arrays-exp`.";
      throw LogicException(ss.str());
    }
  }
  Node texp = d_rewriter.expandDefinition(term);
  if (!texp.isNull())
  {
    return TrustNode::mkTrustRewrite(term, texp, nullptr);
  }
  if (!d_preprocess)
  {
    return TrustNode::null();
  }
  d_ppEqualityEngine.addTerm(term);
  NodeManager* nm = nodeManager();
  Node ret;
  switch (k)
  {
    case Kind::SELECT:
    {
      if (term[0].getKind() == Kind::STORE && ppDisequal(term[0][1], term[1]))
      {
        ret = nm->mkNode(Kind::SELECT, term[0][0], term[1]);
      }
      break;
    }
    case Kind::STORE:
    {
      if (term[0].getKind() == Kind::STORE && (term[1] < term[0][1])
          && ppDisequal(term[1], term[0][1]))
      {
        Node inner = nm->mkNode(Kind::STORE, term[0][0], term[1], term[2]);
        Node outer = nm->mkNode(Kind::STORE, inner, term[0][1], term[0][2]);
        ret = outer;
      }
      break;
    }
    case Kind::EQUAL:
    {
      ret = solveWrite(term, d_solveWrite, d_solveWrite2, true);
      break;
    }
    default: break;
  }
  if (!ret.isNull() && ret != term)
  {
    return TrustNode::mkTrustRewrite(term, ret, nullptr);
  }
  return TrustNode::null();
}

bool TheoryArrays::ppAssert(TrustNode tin,
                            TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  switch (in.getKind())
  {
    case Kind::EQUAL:
    {
      d_ppFacts.push_back(in);
      d_ppEqualityEngine.assertEquality(in, true, in);
      if (in[0].isVar() && d_valuation.isLegalElimination(in[0], in[1]))
      {
        outSubstitutions.addSubstitutionSolved(in[0], in[1], tin);
        return true;
      }
      if (in[1].isVar() && d_valuation.isLegalElimination(in[1], in[0]))
      {
        outSubstitutions.addSubstitutionSolved(in[1], in[0], tin);
        return true;
      }
      break;
    }
    case Kind::NOT:
    {
      d_ppFacts.push_back(in);
      if (in[0].getKind() == Kind::EQUAL)
      {
        Node a = in[0][0];
        Node b = in[0][1];
        d_ppEqualityEngine.assertEquality(in[0], false, in);
      }
      break;
    }
    default: break;
  }
  return false;
}

/////////////////////////////////////////////////////////////////////////////
// T-PROPAGATION / REGISTRATION
/////////////////////////////////////////////////////////////////////////////

bool TheoryArrays::propagateLit(TNode literal)
{
  Trace("arrays") << spaces(context()->getLevel())
                  << "TheoryArrays::propagateLit(" << literal << ")"
                  << std::endl;

  if (d_state.isInConflict())
  {
    Trace("arrays") << spaces(context()->getLevel())
                    << "TheoryArrays::propagateLit(" << literal
                    << "): already in conflict" << std::endl;
    return false;
  }

  bool ok = d_out->propagate(literal);
  if (!ok)
  {
    d_state.notifyInConflict();
  }
  return ok;
}

void TheoryArrays::preRegisterTermInternal(TNode node)
{
  if (d_state.isInConflict())
  {
    return;
  }
  Trace("arrays") << spaces(context()->getLevel())
                  << "TheoryArrays::preRegisterTerm(" << node << ")"
                  << std::endl;
  Kind nk = node.getKind();
  if (nk == Kind::EQUAL)
  {
    d_state.addEqualityEngineTriggerPredicate(node);
    return;
  }
  // add to equality engine and the may equality engine
  TypeNode nodeType = node.getType();
  if (nodeType.isArray())
  {
    if (nodeType.getArrayIndexType().isArray())
    {
      std::stringstream ss;
      ss << "Arrays cannot be indexed by array types, offending array type is "
         << nodeType;
      throw LogicException(ss.str());
    }
    d_mayEqualEqualityEngine.addTerm(node);
  }
  if (d_equalityEngine->hasTerm(node))
  {
    return;
  }
  d_equalityEngine->addTerm(node);

  switch (node.getKind())
  {
    case Kind::SELECT:
    {
      // Reads
      TNode store = d_equalityEngine->getRepresentative(node[0]);

      // The may equal needs the store
      d_mayEqualEqualityEngine.addTerm(store);

      Assert((d_isPreRegistered.insert(node), true));

      // Delegate to solver
      d_internal->preRegisterSelect(node);
      break;
    }
    case Kind::STORE:
    {
      TNode a = d_equalityEngine->getRepresentative(node[0]);

      // Shared: mayEqual merge / const handling
      if (node.isConst())
      {
        Assert(a == node[0]);
        d_mayEqualEqualityEngine.addTerm(node);
        Assert(d_mayEqualEqualityEngine.getRepresentative(node) == node);
        Assert(d_mayEqualEqualityEngine.getRepresentative(a) == a);
        DefValMap::iterator it = d_defValues.find(a);
        Assert(it != d_defValues.end());
        d_defValues[node] = (*it).second;
      }
      else
      {
        d_mayEqualEqualityEngine.assertEquality(node.eqNode(a), true, d_true);
        Assert(d_mayEqualEqualityEngine.consistent());
      }

      // Delegate to solver
      d_internal->preRegisterStore(node);
      break;
    }
    case Kind::STORE_ALL:
    {
      ArrayStoreAll storeAll = node.getConst<ArrayStoreAll>();
      Node defaultValue = storeAll.getValue();
      if (!defaultValue.isConst())
      {
        throw LogicException(
            "Array theory solver does not yet support non-constant default "
            "values for arrays");
      }
      // Shared: set default value
      Assert(d_mayEqualEqualityEngine.getRepresentative(node) == node);
      d_defValues[node] = defaultValue;

      // Delegate to solver
      d_internal->preRegisterStoreAll(node);
      break;
    }
    default:
      // Variables etc, already processed above
      break;
  }
}

void TheoryArrays::preRegisterTerm(TNode node)
{
  preRegisterTermInternal(node);
  if (node.getKind() == Kind::SELECT && node.getType().isBoolean())
  {
    d_state.addEqualityEngineTriggerPredicate(node);
  }
}

TrustNode TheoryArrays::explain(TNode literal)
{
  return d_im.explainLit(literal);
}

/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////

void TheoryArrays::notifySharedTerm(TNode t)
{
  Trace("arrays::sharing") << spaces(context()->getLevel())
                           << "TheoryArrays::notifySharedTerm(" << t << ")"
                           << std::endl;
  if (t.getType().isArray())
  {
    d_sharedArrays.insert(t);
  }
  else
  {
#ifdef CVC5_ASSERTIONS
    d_sharedOther.insert(t);
#endif
    d_sharedTerms = true;
  }
}

void TheoryArrays::computeCareGraph()
{
  // Shared array variable care pairs (always runs)
  if (d_sharedArrays.size() > 0)
  {
    CDNodeSet::key_iterator it1 = d_sharedArrays.key_begin(), it2,
                            iend = d_sharedArrays.key_end();
    for (; it1 != iend; ++it1)
    {
      for (it2 = it1, ++it2; it2 != iend; ++it2)
      {
        if ((*it1).getType() != (*it2).getType())
        {
          continue;
        }
        EqualityStatus eqStatusArr = getEqualityStatus((*it1), (*it2));
        if (eqStatusArr != EQUALITY_UNKNOWN)
        {
          continue;
        }
        Assert(d_valuation.getEqualityStatus((*it1), (*it2))
               == EQUALITY_UNKNOWN);
        addCarePair((*it1), (*it2));
        ++d_numSharedArrayVarSplits;
        return;
      }
    }
  }

  // Read-pair care graph. This is solver-specific: the two solvers keep
  // their read lists in different shapes and enumerate candidate pairs
  // differently (ArraySolverDefault buckets reads by the candidate model
  // value of the index, AextArraySolver sweeps all registered selects).
  // Both drive the shared ArraySolver::checkPair for the per-pair test.
  d_internal->computeCareGraph(
      [this](TNode t1, TNode t2) { addCarePair(t1, t2); });
}

/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

bool TheoryArrays::collectModelValues(TheoryModel* m,
                                      const std::set<Node>& termSet)
{
  NodeManager* nm = nodeManager();
  // Compute arrays that need representatives
  std::vector<Node> arrays;

  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i)
  {
    Node eqc = (*eqcs_i);
    if (!eqc.getType().isArray())
    {
      continue;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      Node n = *eqc_i;
      if (termSet.find(n) != termSet.end())
      {
        if (n.getKind() != Kind::STORE)
        {
          arrays.push_back(n);
          break;
        }
      }
    }
  }

  // Build a list of all the relevant reads, indexed by store representative
  std::map<Node, std::vector<Node>> selects;
  set<Node>::iterator set_it = termSet.begin(), set_it_end = termSet.end();
  for (; set_it != set_it_end; ++set_it)
  {
    Node n = *set_it;
    if (n.getKind() == Kind::SELECT)
    {
      selects[d_equalityEngine->getRepresentative(n[0])].push_back(n);
    }
  }

  // Let the solver augment the selects map (AEXT propagates reads through
  // store chains; default solver is a no-op here).
  d_internal->augmentModelSelects(selects, termSet);

  Node rep;
  DefValMap::iterator it;
  TypeSet defaultValuesSet;

  // Compute all default values already in use
  for (size_t i = 0; i < arrays.size(); ++i)
  {
    TNode nrep = d_equalityEngine->getRepresentative(arrays[i]);
    d_mayEqualEqualityEngine.addTerm(nrep);
    TNode mayRep = d_mayEqualEqualityEngine.getRepresentative(nrep);
    it = d_defValues.find(mayRep);
    if (it != d_defValues.end())
    {
      defaultValuesSet.add(nrep.getType().getArrayConstituentType(),
                           (*it).second);
    }
  }

  // Loop through all array equivalence classes that need a representative
  std::map<Node, Node> defMap;
  std::map<Node, Node>::iterator itd;
  for (size_t i = 0; i < arrays.size(); ++i)
  {
    TNode n = arrays[i];
    TNode nrep = d_equalityEngine->getRepresentative(n);

    TNode mayRep = d_mayEqualEqualityEngine.getRepresentative(nrep);
    it = d_defValues.find(mayRep);
    if (it == d_defValues.end())
    {
      itd = defMap.find(mayRep);
      if (itd == defMap.end())
      {
        TypeNode valueType = nrep.getType().getArrayConstituentType();
        rep = defaultValuesSet.nextTypeEnum(valueType);
        if (rep.isNull())
        {
          Assert(defaultValuesSet.getSet(valueType)->begin()
                 != defaultValuesSet.getSet(valueType)->end());
          rep = *(defaultValuesSet.getSet(valueType)->begin());
        }
        Trace("arrays-models") << "New default value = " << rep << endl;
        defMap[mayRep] = rep;
      }
      else
      {
        rep = itd->second;
      }
    }
    else
    {
      rep = (*it).second;
    }

    // Build the STORE_ALL term with the default value
    rep = nm->mkConst(ArrayStoreAll(nrep.getType(), rep));

    // For each read, require that the rep stores the right value
    vector<Node>& reads = selects[nrep];
    for (unsigned j = 0; j < reads.size(); ++j)
    {
      rep = nm->mkNode(Kind::STORE, rep, reads[j][1], reads[j]);
    }
    if (!m->assertEquality(n, rep, true))
    {
      return false;
    }
    if (!n.isConst())
    {
      m->assertSkeleton(rep);
    }
  }
  return true;
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////

void TheoryArrays::presolve()
{
  Trace("arrays") << "Presolving \n";
  d_internal->presolve();
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

void TheoryArrays::postCheck(Effort level) { d_internal->postCheck(level); }

bool TheoryArrays::preNotifyFact(TNode atom,
                                 CVC5_UNUSED bool pol,
                                 CVC5_UNUSED TNode fact,
                                 bool isPrereg,
                                 bool isInternal)
{
  if (!isInternal && !isPrereg)
  {
    if (atom.getKind() == Kind::EQUAL)
    {
      if (!d_equalityEngine->hasTerm(atom[0]))
      {
        Assert(atom[0].isConst());
        d_equalityEngine->addTerm(atom[0]);
      }
      if (!d_equalityEngine->hasTerm(atom[1]))
      {
        Assert(atom[1].isConst());
        d_equalityEngine->addTerm(atom[1]);
      }
    }
  }
  return false;
}

void TheoryArrays::notifyFact(TNode atom, bool pol, TNode fact, bool isInternal)
{
  // if a disequality
  if (atom.getKind() == Kind::EQUAL && !pol && !isInternal)
  {
    if (fact[0][0].getType().isArray() && !d_state.isInConflict())
    {
      // Delegate to solver for array disequality handling
      d_internal->notifyArrayDisequality(fact[0][0], fact[0][1], fact);
    }
    else
    {
      Trace("pf::array") << "Check: Kind::NOT: array theory NOT making a skolem"
                         << std::endl;
      d_modelConstraints.push_back(fact);
    }
  }
}

void TheoryArrays::computeRelevantTerms(std::set<Node>& termSet)
{
  NodeManager* nm = nodeManager();
  // Shared: make sure RIntro1 reads are included in the relevant set
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i)
  {
    Node eqc = (*eqcs_i);
    if (!eqc.getType().isArray())
    {
      // not an array, skip
      continue;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      Node n = *eqc_i;
      if (termSet.find(n) != termSet.end())
      {
        if (n.getKind() == Kind::STORE)
        {
          // Make sure RIntro1 reads are included
          Node r = nm->mkNode(Kind::SELECT, n, n[1]);
          Trace("arrays::collectModelInfo")
              << "TheoryArrays::collectModelInfo, adding RIntro1 read: " << r
              << endl;
          termSet.insert(r);
        }
      }
    }
  }

  // Solver-specific relevant terms (RIntro2 for default solver, no-op for AEXT)
  d_internal->computeRelevantTerms(termSet);
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

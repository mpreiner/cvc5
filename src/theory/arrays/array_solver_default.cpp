/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the default array solver (Row/Ext).
 */

#include "theory/arrays/array_solver_default.h"

#include <map>

#include "expr/array_store_all.h"
#include "expr/kind.h"
#include "expr/node_algorithm.h"
#include "options/arrays_options.h"
#include "smt/logic_exception.h"
#include "theory/arrays/inference_manager.h"
#include "theory/arrays/skolem_cache.h"
#include "theory/decision_manager.h"
#include "theory/theory_model.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arrays {

static inline std::string spaces(int level)
{
  std::string indentStr(level, ' ');
  return indentStr;
}

ArraySolverDefault::ArraySolverDefault(Env& env,
                                       TheoryState& state,
                                       InferenceManager& im,
                                       Valuation valuation,
                                       eq::EqualityEngine& mayEqualEE,
                                       DefValMap& defValues,
                                       context::CDO<bool>& sharedTerms,
                                       OutputChannel& out,
                                       PreRegCallback preRegCb)
    : ArraySolver(
        env, state, im, valuation, mayEqualEE, defValues, sharedTerms),
      d_out(out),
      d_preRegCb(preRegCb),
      d_numRow(statisticsRegistry().registerInt(
          "theory::arrays::default::number of Row lemmas")),
      d_numExt(statisticsRegistry().registerInt(
          "theory::arrays::default::number of Ext lemmas")),
      d_numProp(statisticsRegistry().registerInt(
          "theory::arrays::default::number of propagations")),
      d_numExplain(statisticsRegistry().registerInt(
          "theory::arrays::default::number of explanations")),
      d_numNonLinear(statisticsRegistry().registerInt(
          "theory::arrays::default::number of calls to setNonLinear")),
      d_numGetModelValSplits(statisticsRegistry().registerInt(
          "theory::arrays::default::number of getModelVal splits")),
      d_numGetModelValConflicts(statisticsRegistry().registerInt(
          "theory::arrays::default::number of getModelVal conflicts")),
      d_numSetModelValSplits(statisticsRegistry().registerInt(
          "theory::arrays::default::number of setModelVal splits")),
      d_numSetModelValConflicts(statisticsRegistry().registerInt(
          "theory::arrays::default::number of setModelVal conflicts")),
      d_infoMap(statisticsRegistry(), context(), "theory::arrays::default::"),
      d_mergeQueue(context()),
      d_mergeInProgress(false),
      d_RowQueue(context()),
      d_RowAlreadyAdded(userContext()),
      d_reads(context()),
      d_constReadsList(context()),
      d_constReadsContext(new context::Context()),
      d_contextPopper(context(), d_constReadsContext),
      d_decisionRequests(context()),
      d_permRef(context()),
      d_readTableContext(new context::Context()),
      d_arrayMerges(context()),
      d_dstrat(new ArraySolverDefaultDecisionStrategy(this)),
      d_dstratInit(false)
{
  d_true = nodeManager()->mkConst<bool>(true);
  d_false = nodeManager()->mkConst<bool>(false);
}

ArraySolverDefault::~ArraySolverDefault()
{
  vector<CTNodeList*>::iterator it = d_readBucketAllocations.begin(),
                                iend = d_readBucketAllocations.end();
  for (; it != iend; ++it)
  {
    (*it)->deleteSelf();
  }
  delete d_readTableContext;
  CNodeNListMap::iterator it2 = d_constReads.begin();
  for (; it2 != d_constReads.end(); ++it2)
  {
    it2->second->deleteSelf();
  }
  delete d_constReadsContext;
}

void ArraySolverDefault::finishInit(eq::EqualityEngine* ee)
{
  Assert(ee != nullptr);
  d_ee = ee;
}

std::string ArraySolverDefault::identify() const
{
  return "ArraySolverDefault";
}

/////////////////////////////////////////////////////////////////////////////
// TERM REGISTRATION
/////////////////////////////////////////////////////////////////////////////

void ArraySolverDefault::preRegisterSelect(TNode node)
{
  Assert(node.getKind() == Kind::SELECT);
  TNode store = d_ee->getRepresentative(node[0]);

  Assert(d_ee->getRepresentative(store) == store);
  d_infoMap.addIndex(store, node[1]);

  // Synchronize d_constReadsContext with SAT context
  Assert(d_constReadsContext->getLevel() <= context()->getLevel());
  while (d_constReadsContext->getLevel() < context()->getLevel())
  {
    d_constReadsContext->push();
  }

  // Record read in sharing data structure
  TNode index = d_ee->getRepresentative(node[1]);
  if (!options().arrays.arraysWeakEquivalence && index.isConst())
  {
    CTNodeList* temp;
    CNodeNListMap::iterator it = d_constReads.find(index);
    if (it == d_constReads.end())
    {
      temp = new (true) CTNodeList(d_constReadsContext);
      d_constReads[index] = temp;
    }
    else
    {
      temp = (*it).second;
    }
    temp->push_back(node);
    d_constReadsList.push_back(node);
  }
  else
  {
    d_reads.push_back(node);
  }

  checkRowForIndex(node[1], store);
}

void ArraySolverDefault::preRegisterStore(TNode node)
{
  Assert(node.getKind() == Kind::STORE);
  TNode a = d_ee->getRepresentative(node[0]);

  TNode i = node[1];
  TNode v = node[2];
  NodeManager* nm = nodeManager();
  Node ni = nm->mkNode(Kind::SELECT, node, i);
  if (!d_ee->hasTerm(ni))
  {
    d_preRegCb(ni);
  }
  // Apply RIntro1 Rule
  d_im.assertInference(ni.eqNode(v),
                       true,
                       InferenceId::ARRAYS_READ_OVER_WRITE_1,
                       d_true,
                       ProofRule::ARRAYS_READ_OVER_WRITE_1);

  d_infoMap.addStore(node, node);
  d_infoMap.addInStore(a, node);
  d_infoMap.setModelRep(node, node);

  // Add-Store for Weak Equivalence
  if (options().arrays.arraysWeakEquivalence)
  {
    Assert(weakEquivGetRep(node[0]) == weakEquivGetRep(a));
    Assert(weakEquivGetRep(node) == node);
    d_infoMap.setWeakEquivPointer(node, node[0]);
    d_infoMap.setWeakEquivIndex(node, node[1]);
#ifdef CVC5_ASSERTIONS
    checkWeakEquiv(false);
#endif
  }

  checkStore(node);
}

void ArraySolverDefault::preRegisterStoreAll(TNode node)
{
  Assert(node.getKind() == Kind::STORE_ALL);
  d_infoMap.setConstArr(node, node);
  setNonLinear(node);
}

/////////////////////////////////////////////////////////////////////////////
// EQUALITY ENGINE CALLBACKS
/////////////////////////////////////////////////////////////////////////////

void ArraySolverDefault::eqNotifyMerge(TNode a, TNode b) { mergeArrays(a, b); }

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

void ArraySolverDefault::postCheck(Theory::Effort level)
{
  bool eagerLemmas = options().arrays.arraysEagerLemmas;
  bool weakEquiv = options().arrays.arraysWeakEquivalence;

  if ((eagerLemmas || Theory::fullEffort(level)) && !d_state.isInConflict()
      && weakEquiv)
  {
    // Replay all array merges to update weak equivalence data structures
    context::CDList<Node>::iterator it = d_arrayMerges.begin(),
                                    iend = d_arrayMerges.end();
    TNode a, b, eq;
    for (; it != iend; ++it)
    {
      eq = *it;
      a = eq[0];
      b = eq[1];
      weakEquivMakeRep(b);
      if (weakEquivGetRep(a) == b)
      {
        weakEquivAddSecondary(TNode(), a, b, eq);
      }
      else
      {
        d_infoMap.setWeakEquivPointer(b, a);
        d_infoMap.setWeakEquivIndex(b, TNode());
      }
#ifdef CVC5_ASSERTIONS
      checkWeakEquiv(false);
#endif
    }
#ifdef CVC5_ASSERTIONS
    checkWeakEquiv(true);
#endif

    d_readTableContext->push();
    TNode mayRep, iRep;
    CTNodeList* bucketList = nullptr;
    CTNodeList::const_iterator i = d_reads.begin(), readsEnd = d_reads.end();
    for (; i != readsEnd; ++i)
    {
      const TNode& r = *i;

      Trace("arrays::weak")
          << "TheoryArrays::check(): checking read " << r << std::endl;

      // Find the bucket for this read.
      mayRep = d_mayEqualEqualityEngine.getRepresentative(r[0]);
      iRep = d_ee->getRepresentative(r[1]);
      std::pair<TNode, TNode> key(mayRep, iRep);
      ReadBucketMap::iterator rbm_it = d_readBucketTable.find(key);
      if (rbm_it == d_readBucketTable.end())
      {
        bucketList = new (true) CTNodeList(d_readTableContext);
        d_readBucketAllocations.push_back(bucketList);
        d_readBucketTable[key] = bucketList;
      }
      else
      {
        bucketList = rbm_it->second;
      }
      CTNodeList::const_iterator ctnl_it = bucketList->begin(),
                                 ctnl_iend = bucketList->end();
      for (; ctnl_it != ctnl_iend; ++ctnl_it)
      {
        const TNode& r2 = *ctnl_it;
        Assert(r2.getKind() == Kind::SELECT);
        Assert(mayRep == d_mayEqualEqualityEngine.getRepresentative(r2[0]));
        Assert(iRep == d_ee->getRepresentative(r2[1]));
        if (d_ee->areEqual(r, r2))
        {
          continue;
        }
        if (weakEquivGetRepIndex(r[0], r[1])
            == weakEquivGetRepIndex(r2[0], r[1]))
        {
          // add lemma: r[1] = r2[1] /\ cond(r[0],r2[0]) => r = r2
          vector<TNode> conjunctions;
          Assert(d_ee->areEqual(r, rewrite(r)));
          Assert(d_ee->areEqual(r2, rewrite(r2)));
          Node lemma = rewrite(r).eqNode(rewrite(r2)).negate();
          d_permRef.push_back(lemma);
          conjunctions.push_back(lemma);
          if (r[1] != r2[1])
          {
            d_ee->explainEquality(r[1], r2[1], true, conjunctions);
          }
          // TODO: get smaller lemmas by eliminating shared parts of path
          weakEquivBuildCond(r[0], r[1], conjunctions);
          weakEquivBuildCond(r2[0], r[1], conjunctions);
          lemma = mkAnd(conjunctions, true);
          // LSH FIXME: which kind of arrays lemma is this
          Trace("arrays-lem")
              << "Arrays::addExtLemma (weak-eq) " << lemma << "\n";
          d_out.lemma(lemma, InferenceId::NONE, LemmaProperty::SEND_ATOMS);
          d_readTableContext->pop();
          Trace("arrays") << spaces(context()->getLevel())
                          << "Arrays::check(): done" << endl;
          return;
        }
      }
      bucketList->push_back(r);
    }
    d_readTableContext->pop();
  }

  if (!eagerLemmas && Theory::fullEffort(level) && !d_state.isInConflict()
      && !weakEquiv)
  {
    // generate the lemmas on the worklist
    Trace("arrays-lem") << "Arrays::discharging lemmas. Number of queued "
                           "lemmas: "
                        << d_RowQueue.size() << "\n";
    while (d_RowQueue.size() > 0 && !d_state.isInConflict())
    {
      if (dischargeLemmas())
      {
        break;
      }
    }
  }

  Trace("arrays") << spaces(context()->getLevel()) << "Arrays::check(): done"
                  << endl;
}

void ArraySolverDefault::notifyArrayDisequality(TNode a, TNode b, TNode fact)
{
  NodeManager* nm = nodeManager();

  TNode k;
  // k is the skolem for this disequality.
  Trace("pf::array") << "Check: Kind::NOT: array theory making a skolem"
                     << std::endl;
  k = getSkolem(fact);

  Node ak = nm->mkNode(Kind::SELECT, a, k);
  Node bk = nm->mkNode(Kind::SELECT, b, k);
  Node eq = ak.eqNode(bk);
  Node lemma = fact[0].orNode(eq.notNode());

  if (options().arrays.arraysPropagate > 0 && d_ee->hasTerm(ak)
      && d_ee->hasTerm(bk))
  {
    // Propagate witness disequality - might produce a conflict
    Trace("pf::array") << "Asserting to the equality engine:" << std::endl
                       << "\teq = " << eq << std::endl
                       << "\treason = " << fact << std::endl;
    d_im.assertInference(
        eq, false, InferenceId::ARRAYS_EXT, fact, ProofRule::ARRAYS_EXT);
    ++d_numProp;
  }

  Trace("arrays-lem") << "Arrays::addExtLemma " << lemma << "\n";
  d_im.arrayLemma(
      eq.notNode(), InferenceId::ARRAYS_EXT, fact, ProofRule::ARRAYS_EXT);
  ++d_numExt;
}

/////////////////////////////////////////////////////////////////////////////
// HELPER METHODS
/////////////////////////////////////////////////////////////////////////////

void ArraySolverDefault::conflict(TNode a, TNode b)
{
  Trace("pf::array") << "ArraySolverDefault::Conflict called" << std::endl;
  d_im.conflictEqConstantMerge(a, b);
}

Node ArraySolverDefault::getSkolem(TNode ref)
{
  Node skolem = SkolemCache::getExtIndexSkolem(nodeManager(), ref);
  Trace("pf::array") << "Pregistering a Skolem" << std::endl;
  d_preRegCb(skolem);
  Trace("pf::array") << "Pregistering a Skolem DONE" << std::endl;
  Trace("pf::array") << "getSkolem DONE" << std::endl;
  return skolem;
}

Node ArraySolverDefault::mkAnd(std::vector<TNode>& conjunctions,
                               bool invert,
                               unsigned startIndex)
{
  if (conjunctions.empty())
  {
    return invert ? d_false : d_true;
  }

  std::set<TNode> all;

  unsigned i = startIndex;
  TNode t;
  for (; i < conjunctions.size(); ++i)
  {
    t = conjunctions[i];
    if (t == d_true)
    {
      continue;
    }
    else if (t.getKind() == Kind::AND)
    {
      for (TNode::iterator child_it = t.begin(); child_it != t.end();
           ++child_it)
      {
        if (*child_it == d_true)
        {
          continue;
        }
        all.insert(*child_it);
      }
    }
    else
    {
      all.insert(t);
    }
  }

  if (all.size() == 0)
  {
    return invert ? d_false : d_true;
  }
  if (all.size() == 1)
  {
    // All the same, or just one
    if (invert)
    {
      return (*(all.begin())).negate();
    }
    return *(all.begin());
  }

  NodeManager* nm = nodeManager();
  NodeBuilder conjunction(nm, invert ? Kind::OR : Kind::AND);
  std::set<TNode>::const_iterator ci = all.begin();
  std::set<TNode>::const_iterator ci_end = all.end();
  while (ci != ci_end)
  {
    if (invert)
    {
      conjunction << (*ci).negate();
    }
    else
    {
      conjunction << *ci;
    }
    ++ci;
  }

  return conjunction;
}

void ArraySolverDefault::setNonLinear(TNode a)
{
  if (options().arrays.arraysWeakEquivalence) return;
  if (d_infoMap.isNonLinear(a)) return;

  Trace("arrays") << spaces(context()->getLevel()) << "Arrays::setNonLinear ("
                  << a << ")\n";
  d_infoMap.setNonLinear(a);
  ++d_numNonLinear;

  const CTNodeList* i_a = d_infoMap.getIndices(a);
  const CTNodeList* st_a = d_infoMap.getStores(a);
  const CTNodeList* inst_a = d_infoMap.getInStores(a);

  size_t it = 0;

  // Propagate non-linearity down chain of stores
  for (; it < st_a->size(); ++it)
  {
    TNode store = (*st_a)[it];
    Assert(store.getKind() == Kind::STORE);
    setNonLinear(store[0]);
  }

  // Instantiate ROW lemmas that were ignored before
  size_t it2 = 0;
  RowLemmaType lem;
  for (; it2 < i_a->size(); ++it2)
  {
    TNode i = (*i_a)[it2];
    it = 0;
    for (; it < inst_a->size(); ++it)
    {
      TNode store = (*inst_a)[it];
      Assert(store.getKind() == Kind::STORE);
      TNode j = store[1];
      TNode c = store[0];
      lem = std::make_tuple(store, c, j, i);
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::setNonLinear (" << store << ", " << c
                          << ", " << j << ", " << i << ")\n";
      queueRowLemma(lem);
    }
  }
}

void ArraySolverDefault::mergeArrays(TNode a, TNode b)
{
  // Note: a is the new representative
  Assert(a.getType().isArray() && b.getType().isArray());

  if (d_mergeInProgress)
  {
    // Nested call to mergeArrays, just push on the queue and return
    d_mergeQueue.push(a.eqNode(b));
    return;
  }

  d_mergeInProgress = true;
  bool optLinear = options().arrays.arraysOptimizeLinear;
  bool weakEquiv = options().arrays.arraysWeakEquivalence;

  Node n;
  while (true)
  {
    // Normally, a is its own representative, but it's possible for a to have
    // been merged with another array after it got queued up by the equality
    // engine, so we take its representative to be safe.
    a = d_ee->getRepresentative(a);
    Assert(d_ee->getRepresentative(b) == a);
    Trace("arrays-merge") << spaces(context()->getLevel()) << "Arrays::merge: ("
                          << a << ", " << b << ")\n";

    if (optLinear && !weakEquiv)
    {
      bool aNL = d_infoMap.isNonLinear(a);
      bool bNL = d_infoMap.isNonLinear(b);
      if (aNL)
      {
        // If both are already marked non-linear there is nothing to do.
        if (!bNL)
        {
          setNonLinear(b);
        }
      }
      else
      {
        if (bNL)
        {
          setNonLinear(a);
        }
        else
        {
          // Check for new non-linear arrays.
          const CTNodeList* astores = d_infoMap.getStores(a);
          const CTNodeList* bstores = d_infoMap.getStores(b);
          Assert(astores->size() <= 1 && bstores->size() <= 1);
          if (astores->size() > 0 && bstores->size() > 0)
          {
            setNonLinear(a);
            setNonLinear(b);
          }
        }
      }
    }

    TNode constArrA = d_infoMap.getConstArr(a);
    TNode constArrB = d_infoMap.getConstArr(b);
    if (constArrA.isNull())
    {
      if (!constArrB.isNull())
      {
        d_infoMap.setConstArr(a, constArrB);
      }
    }
    else if (!constArrB.isNull())
    {
      if (constArrA != constArrB)
      {
        conflict(constArrA, constArrB);
      }
    }

    TNode mayRepA = d_mayEqualEqualityEngine.getRepresentative(a);
    TNode mayRepB = d_mayEqualEqualityEngine.getRepresentative(b);

    // If a and b have different default values associated with their mayequal
    // equivalence classes, things get complicated.  Similarly, if two mayequal
    // equivalence classes have different constant representatives, it's not
    // clear what to do. - disallow these cases for now.  -Clark
    DefValMap::iterator it = d_defValues.find(mayRepA);
    DefValMap::iterator it2 = d_defValues.find(mayRepB);
    TNode defValue;

    if (it != d_defValues.end())
    {
      defValue = (*it).second;
      if ((it2 != d_defValues.end() && (defValue != (*it2).second))
          || (mayRepA.isConst() && mayRepB.isConst() && mayRepA != mayRepB))
      {
        throw LogicException(
            "Array theory solver does not yet support write-chains connecting "
            "two different constant arrays");
      }
    }
    else if (it2 != d_defValues.end())
    {
      defValue = (*it2).second;
    }
    d_mayEqualEqualityEngine.assertEquality(a.eqNode(b), true, d_true);
    Assert(d_mayEqualEqualityEngine.consistent());
    if (!defValue.isNull())
    {
      mayRepA = d_mayEqualEqualityEngine.getRepresentative(a);
      d_defValues[mayRepA] = defValue;
    }

    checkRowLemmas(a, b);
    checkRowLemmas(b, a);

    // merge info adds the list of the 2nd argument to the first
    d_infoMap.mergeInfo(a, b);

    if (weakEquiv)
    {
      d_arrayMerges.push_back(a.eqNode(b));
    }

    // If no more to do, break
    if (d_state.isInConflict() || d_mergeQueue.empty())
    {
      break;
    }

    // Otherwise, prepare for next iteration
    n = d_mergeQueue.front();
    a = n[0];
    b = n[1];
    d_mergeQueue.pop();
  }
  d_mergeInProgress = false;
}

void ArraySolverDefault::checkStore(TNode a)
{
  if (options().arrays.arraysWeakEquivalence) return;

  Trace("arrays-cri") << "Arrays::checkStore " << a << "\n";

  if (TraceIsOn("arrays-cri"))
  {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(a.getKind() == Kind::STORE);
  TNode b = a[0];
  TNode i = a[1];

  TNode brep = d_ee->getRepresentative(b);

  if (!options().arrays.arraysOptimizeLinear || d_infoMap.isNonLinear(brep))
  {
    const CTNodeList* js = d_infoMap.getIndices(brep);
    size_t it = 0;
    RowLemmaType lem;
    for (; it < js->size(); ++it)
    {
      TNode j = (*js)[it];
      if (i == j) continue;
      lem = std::make_tuple(a, b, i, j);
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::checkStore (" << a << ", " << b << ", "
                          << i << ", " << j << ")\n";
      queueRowLemma(lem);
    }
  }
}

void ArraySolverDefault::checkRowForIndex(TNode i, TNode a)
{
  if (options().arrays.arraysWeakEquivalence) return;

  Trace("arrays-cri") << "Arrays::checkRowForIndex " << a << "\n";
  Trace("arrays-cri") << "                   index " << i << "\n";

  if (TraceIsOn("arrays-cri"))
  {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(d_ee->getRepresentative(a) == a);

  TNode constArr = d_infoMap.getConstArr(a);
  if (!constArr.isNull())
  {
    ArrayStoreAll storeAll = constArr.getConst<ArrayStoreAll>();
    Node defValue = storeAll.getValue();
    Node selConst = nodeManager()->mkNode(Kind::SELECT, constArr, i);
    if (!d_ee->hasTerm(selConst))
    {
      d_preRegCb(selConst);
    }
    // not currently supported in proofs, use TRUST
    d_im.assertInference(selConst.eqNode(defValue),
                         true,
                         InferenceId::ARRAYS_CONST_ARRAY_DEFAULT,
                         d_true,
                         ProofRule::TRUST);
  }

  const CTNodeList* stores = d_infoMap.getStores(a);
  const CTNodeList* instores = d_infoMap.getInStores(a);
  size_t it = 0;
  RowLemmaType lem;

  for (; it < stores->size(); ++it)
  {
    TNode store = (*stores)[it];
    Assert(store.getKind() == Kind::STORE);
    TNode j = store[1];
    if (i == j) continue;
    lem = std::make_tuple(store, store[0], j, i);
    Trace("arrays-lem") << spaces(context()->getLevel())
                        << "Arrays::checkRowForIndex (" << store << ", "
                        << store[0] << ", " << j << ", " << i << ")\n";
    queueRowLemma(lem);
  }

  if (!options().arrays.arraysOptimizeLinear || d_infoMap.isNonLinear(a))
  {
    it = 0;
    for (; it < instores->size(); ++it)
    {
      TNode instore = (*instores)[it];
      Assert(instore.getKind() == Kind::STORE);
      TNode j = instore[1];
      if (i == j) continue;
      lem = std::make_tuple(instore, instore[0], j, i);
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::checkRowForIndex (" << instore << ", "
                          << instore[0] << ", " << j << ", " << i << ")\n";
      queueRowLemma(lem);
    }
  }
}

// a just became equal to b
// look for new ROW lemmas
void ArraySolverDefault::checkRowLemmas(TNode a, TNode b)
{
  if (options().arrays.arraysWeakEquivalence) return;

  Trace("arrays-crl") << "Arrays::checkLemmas begin \n" << a << "\n";
  if (TraceIsOn("arrays-crl")) d_infoMap.getInfo(a)->print();
  Trace("arrays-crl") << "  ------------  and " << b << "\n";
  if (TraceIsOn("arrays-crl")) d_infoMap.getInfo(b)->print();

  const CTNodeList* i_a = d_infoMap.getIndices(a);
  size_t it = 0;
  TNode constArr = d_infoMap.getConstArr(b);
  if (!constArr.isNull())
  {
    for (; it < i_a->size(); ++it)
    {
      TNode i = (*i_a)[it];
      Node selConst = nodeManager()->mkNode(Kind::SELECT, constArr, i);
      if (!d_ee->hasTerm(selConst))
      {
        d_preRegCb(selConst);
      }
    }
  }

  const CTNodeList* st_b = d_infoMap.getStores(b);
  const CTNodeList* inst_b = d_infoMap.getInStores(b);
  size_t its;

  RowLemmaType lem;

  for (it = 0; it < i_a->size(); ++it)
  {
    TNode i = (*i_a)[it];
    its = 0;
    for (; its < st_b->size(); ++its)
    {
      TNode store = (*st_b)[its];
      Assert(store.getKind() == Kind::STORE);
      TNode j = store[1];
      TNode c = store[0];
      lem = std::make_tuple(store, c, j, i);
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::checkRowLemmas (" << store << ", " << c
                          << ", " << j << ", " << i << ")\n";
      queueRowLemma(lem);
    }
  }

  if (!options().arrays.arraysOptimizeLinear || d_infoMap.isNonLinear(b))
  {
    for (it = 0; it < i_a->size(); ++it)
    {
      TNode i = (*i_a)[it];
      its = 0;
      for (; its < inst_b->size(); ++its)
      {
        TNode store = (*inst_b)[its];
        Assert(store.getKind() == Kind::STORE);
        TNode j = store[1];
        TNode c = store[0];
        lem = std::make_tuple(store, c, j, i);
        Trace("arrays-lem")
            << spaces(context()->getLevel()) << "Arrays::checkRowLemmas ("
            << store << ", " << c << ", " << j << ", " << i << ")\n";
        queueRowLemma(lem);
      }
    }
  }
  Trace("arrays-crl") << "Arrays::checkLemmas done.\n";
}

void ArraySolverDefault::propagateRowLemma(RowLemmaType lem)
{
  Trace("pf::array") << "TheoryArrays: RowLemma Propagate called. "
                        "arraysPropagate = "
                     << options().arrays.arraysPropagate << std::endl;

  TNode a, b, i, j;
  std::tie(a, b, i, j) = lem;

  Assert(a.getType().isArray() && b.getType().isArray());
  if (d_ee->areEqual(a, b) || d_ee->areEqual(i, j))
  {
    return;
  }

  NodeManager* nm = nodeManager();
  Node aj = nm->mkNode(Kind::SELECT, a, j);
  Node bj = nm->mkNode(Kind::SELECT, b, j);

  // Try to avoid introducing new read terms: track whether these already exist
  bool ajExists = d_ee->hasTerm(aj);
  bool bjExists = d_ee->hasTerm(bj);
  bool bothExist = ajExists && bjExists;

  // If propagating, check propagations
  int64_t prop = options().arrays.arraysPropagate;
  if (prop > 0)
  {
    if (d_ee->areDisequal(i, j, true) && (bothExist || prop > 1))
    {
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::queueRowLemma: propagating aj = bj ("
                          << aj << ", " << bj << ")\n";
      Node aj_eq_bj = aj.eqNode(bj);
      Node reason =
          (i.isConst() && j.isConst()) ? d_true : i.eqNode(j).notNode();
      d_permRef.push_back(reason);
      if (!ajExists)
      {
        d_preRegCb(aj);
      }
      if (!bjExists)
      {
        d_preRegCb(bj);
      }
      d_im.assertInference(aj_eq_bj,
                           true,
                           InferenceId::ARRAYS_READ_OVER_WRITE,
                           reason,
                           ProofRule::ARRAYS_READ_OVER_WRITE);
      ++d_numProp;
      return;
    }
    if (bothExist && d_ee->areDisequal(aj, bj, true))
    {
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::queueRowLemma: propagating i = j (" << i
                          << ", " << j << ")\n";
      Node reason =
          (aj.isConst() && bj.isConst()) ? d_true : aj.eqNode(bj).notNode();
      Node j_eq_i = j.eqNode(i);
      d_im.assertInference(j_eq_i,
                           true,
                           InferenceId::ARRAYS_READ_OVER_WRITE_CONTRA,
                           reason,
                           ProofRule::ARRAYS_READ_OVER_WRITE_CONTRA);
      ++d_numProp;
      return;
    }
  }
}

void ArraySolverDefault::queueRowLemma(RowLemmaType lem)
{
  Trace("pf::array") << "Array solver: queue row lemma called" << std::endl;

  if (d_state.isInConflict() || d_RowAlreadyAdded.contains(lem))
  {
    return;
  }
  TNode a, b, i, j;
  std::tie(a, b, i, j) = lem;

  Assert(a.getType().isArray() && b.getType().isArray());
  if (d_ee->areEqual(a, b) || d_ee->areEqual(i, j))
  {
    return;
  }

  NodeManager* nm = nodeManager();
  Node aj = nm->mkNode(Kind::SELECT, a, j);
  Node bj = nm->mkNode(Kind::SELECT, b, j);

  // Try to avoid introducing new read terms: track whether these already
  // exist
  bool ajExists = d_ee->hasTerm(aj);
  bool bjExists = d_ee->hasTerm(bj);
  bool bothExist = ajExists && bjExists;

  int64_t prop = options().arrays.arraysPropagate;

  if (prop > 0)
  {
    propagateRowLemma(lem);
  }

  // Prefer equality between indexes so as not to introduce new read terms
  if (options().arrays.arraysEagerIndexSplitting && !bothExist
      && !d_ee->areDisequal(i, j, false))
  {
    Node i_eq_j;
    i_eq_j = d_valuation.ensureLiteral(i.eqNode(j));  // TODO: think about this
    d_out.preferPhase(i_eq_j, true);
    d_decisionRequests.push(i_eq_j);
  }

  if (options().arrays.arraysEagerLemmas || bothExist)
  {
    // Make sure that any terms introduced by rewriting are appropriately
    // stored in the equality database
    Node aj2 = rewrite(aj);
    if (aj != aj2)
    {
      if (!ajExists)
      {
        d_preRegCb(aj);
      }
      if (!d_ee->hasTerm(aj2))
      {
        d_preRegCb(aj2);
      }
      d_im.assertInference(aj.eqNode(aj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
    }
    Node bj2 = rewrite(bj);
    if (bj != bj2)
    {
      if (!bjExists)
      {
        d_preRegCb(bj);
      }
      if (!d_ee->hasTerm(bj2))
      {
        d_preRegCb(bj2);
      }
      d_im.assertInference(bj.eqNode(bj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
    }
    if (aj2 == bj2)
    {
      return;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = rewrite(eq1);
    if (eq1_r == d_true)
    {
      if (!d_ee->hasTerm(aj2))
      {
        d_preRegCb(aj2);
      }
      if (!d_ee->hasTerm(bj2))
      {
        d_preRegCb(bj2);
      }
      d_im.assertInference(eq1,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
      return;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = rewrite(eq2);
    if (eq2_r == d_true)
    {
      d_im.assertInference(eq2,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
      return;
    }

    Node lemma = nm->mkNode(Kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem") << "Arrays::addRowLemma (1) adding " << lemma << "\n";
    d_RowAlreadyAdded.insert(lem);
    // use non-rewritten nodes
    d_im.arrayLemma(aj.eqNode(bj),
                    InferenceId::ARRAYS_READ_OVER_WRITE,
                    eq2.notNode(),
                    ProofRule::ARRAYS_READ_OVER_WRITE);
    ++d_numRow;
  }
  else
  {
    d_RowQueue.push(lem);
  }
}

Node ArraySolverDefault::getNextDecisionRequest()
{
  if (!d_decisionRequests.empty())
  {
    Node n = d_decisionRequests.front();
    d_decisionRequests.pop();
    return n;
  }
  return Node::null();
}

bool ArraySolverDefault::dischargeLemmas()
{
  bool reduceSharing = options().arrays.arraysReduceSharing;
  bool lemmasAdded = false;

  for (size_t count = 0, sz = d_RowQueue.size(); count < sz; ++count)
  {
    RowLemmaType l = d_RowQueue.front();
    d_RowQueue.pop();
    if (d_RowAlreadyAdded.contains(l))
    {
      continue;
    }

    TNode a, b, i, j;
    std::tie(a, b, i, j) = l;
    Assert(a.getType().isArray() && b.getType().isArray());

    NodeManager* nm = nodeManager();
    Node aj = nm->mkNode(Kind::SELECT, a, j);
    Node bj = nm->mkNode(Kind::SELECT, b, j);
    bool ajExists = d_ee->hasTerm(aj);
    bool bjExists = d_ee->hasTerm(bj);

    // Check for redundant lemma
    if (!d_ee->hasTerm(i) || !d_ee->hasTerm(j) || d_ee->areEqual(i, j)
        || !d_ee->hasTerm(a) || !d_ee->hasTerm(b) || d_ee->areEqual(a, b)
        || (ajExists && bjExists && d_ee->areEqual(aj, bj)))
    {
      continue;
    }

    int64_t prop = options().arrays.arraysPropagate;
    if (prop > 0)
    {
      propagateRowLemma(l);
      if (d_state.isInConflict())
      {
        return true;
      }
    }

    // Make sure that any terms introduced by rewriting are appropriately
    // stored in the equality database
    Node aj2 = rewrite(aj);
    if (aj != aj2)
    {
      if (!ajExists)
      {
        d_preRegCb(aj);
      }
      if (!d_ee->hasTerm(aj2))
      {
        d_preRegCb(aj2);
      }
      d_im.assertInference(aj.eqNode(aj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
    }
    Node bj2 = rewrite(bj);
    if (bj != bj2)
    {
      if (!bjExists)
      {
        d_preRegCb(bj);
      }
      if (!d_ee->hasTerm(bj2))
      {
        d_preRegCb(bj2);
      }
      d_im.assertInference(bj.eqNode(bj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
    }
    if (aj2 == bj2)
    {
      continue;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = rewrite(eq1);
    if (eq1_r == d_true)
    {
      if (!d_ee->hasTerm(aj2))
      {
        d_preRegCb(aj2);
      }
      if (!d_ee->hasTerm(bj2))
      {
        d_preRegCb(bj2);
      }
      d_im.assertInference(eq1,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
      continue;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = rewrite(eq2);
    if (eq2_r == d_true)
    {
      d_im.assertInference(eq2,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           ProofRule::MACRO_SR_PRED_INTRO);
      continue;
    }

    Node lem = nm->mkNode(Kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem") << "Arrays::addRowLemma (2) adding " << lem << "\n";
    d_RowAlreadyAdded.insert(l);
    // use non-rewritten nodes, theory preprocessing will rewrite
    d_im.arrayLemma(aj.eqNode(bj),
                    InferenceId::ARRAYS_READ_OVER_WRITE,
                    eq2.notNode(),
                    ProofRule::ARRAYS_READ_OVER_WRITE);
    ++d_numRow;
    lemmasAdded = true;
    if (reduceSharing)
    {
      return true;
    }
  }
  return lemmasAdded;
}

/////////////////////////////////////////////////////////////////////////////
// WEAK EQUIVALENCE
/////////////////////////////////////////////////////////////////////////////

TNode ArraySolverDefault::weakEquivGetRep(TNode node)
{
  TNode pointer;
  while (true)
  {
    pointer = d_infoMap.getWeakEquivPointer(node);
    if (pointer.isNull())
    {
      return node;
    }
    node = pointer;
  }
}

TNode ArraySolverDefault::weakEquivGetRepIndex(TNode node, TNode index)
{
  Assert(!index.isNull());
  TNode pointer, index2;
  while (true)
  {
    pointer = d_infoMap.getWeakEquivPointer(node);
    if (pointer.isNull())
    {
      return node;
    }
    index2 = d_infoMap.getWeakEquivIndex(node);
    if (index2.isNull() || !d_ee->areEqual(index, index2))
    {
      node = pointer;
    }
    else
    {
      TNode secondary = d_infoMap.getWeakEquivSecondary(node);
      if (secondary.isNull())
      {
        return node;
      }
      node = secondary;
    }
  }
}

void ArraySolverDefault::visitAllLeaves(TNode reason,
                                        vector<TNode>& conjunctions)
{
  switch (reason.getKind())
  {
    case Kind::AND:
      Assert(reason.getNumChildren() == 2);
      visitAllLeaves(reason[0], conjunctions);
      visitAllLeaves(reason[1], conjunctions);
      break;
    case Kind::NOT: conjunctions.push_back(reason); break;
    case Kind::EQUAL:
      d_ee->explainEquality(reason[0], reason[1], true, conjunctions);
      break;
    default: Unreachable();
  }
}

void ArraySolverDefault::weakEquivBuildCond(TNode node,
                                            TNode index,
                                            vector<TNode>& conjunctions)
{
  Assert(!index.isNull());
  TNode pointer, index2;
  while (true)
  {
    pointer = d_infoMap.getWeakEquivPointer(node);
    if (pointer.isNull())
    {
      return;
    }
    index2 = d_infoMap.getWeakEquivIndex(node);
    if (index2.isNull())
    {
      // Null index means these two nodes became equal: explain the equality.
      d_ee->explainEquality(node, pointer, true, conjunctions);
      node = pointer;
    }
    else if (!d_ee->areEqual(index, index2))
    {
      // If indices are not equal in current context, need to add that to the
      // lemma.
      Node reason = index.eqNode(index2).notNode();
      d_permRef.push_back(reason);
      conjunctions.push_back(reason);
      node = pointer;
    }
    else
    {
      TNode secondary = d_infoMap.getWeakEquivSecondary(node);
      if (secondary.isNull())
      {
        return;
      }
      TNode reason = d_infoMap.getWeakEquivSecondaryReason(node);
      Assert(!reason.isNull());
      visitAllLeaves(reason, conjunctions);
      node = secondary;
    }
  }
}

void ArraySolverDefault::weakEquivMakeRep(TNode node)
{
  TNode pointer = d_infoMap.getWeakEquivPointer(node);
  if (pointer.isNull())
  {
    return;
  }
  weakEquivMakeRep(pointer);
  d_infoMap.setWeakEquivPointer(pointer, node);
  d_infoMap.setWeakEquivIndex(pointer, d_infoMap.getWeakEquivIndex(node));
  d_infoMap.setWeakEquivPointer(node, TNode());
  weakEquivMakeRepIndex(node);
}

void ArraySolverDefault::weakEquivMakeRepIndex(TNode node)
{
  TNode secondary = d_infoMap.getWeakEquivSecondary(node);
  if (secondary.isNull())
  {
    return;
  }
  TNode index = d_infoMap.getWeakEquivIndex(node);
  Assert(!index.isNull());
  TNode index2 = d_infoMap.getWeakEquivIndex(secondary);
  Node reason;
  TNode next;
  while (index2.isNull() || !d_ee->areEqual(index, index2))
  {
    next = d_infoMap.getWeakEquivPointer(secondary);
    d_infoMap.setWeakEquivSecondary(node, next);
    reason = d_infoMap.getWeakEquivSecondaryReason(node);
    if (index2.isNull())
    {
      reason = reason.andNode(secondary.eqNode(next));
    }
    else
    {
      reason = reason.andNode(index.eqNode(index2).notNode());
    }
    d_permRef.push_back(reason);
    d_infoMap.setWeakEquivSecondaryReason(node, reason);
    if (next.isNull())
    {
      return;
    }
    secondary = next;
    index2 = d_infoMap.getWeakEquivIndex(secondary);
  }
  weakEquivMakeRepIndex(secondary);
  d_infoMap.setWeakEquivSecondary(secondary, node);
  d_infoMap.setWeakEquivSecondaryReason(
      secondary, d_infoMap.getWeakEquivSecondaryReason(node));
  d_infoMap.setWeakEquivSecondary(node, TNode());
  d_infoMap.setWeakEquivSecondaryReason(node, TNode());
}

void ArraySolverDefault::weakEquivAddSecondary(TNode index,
                                               TNode arrayFrom,
                                               TNode arrayTo,
                                               TNode reason)
{
  std::unordered_set<TNode> marked;
  vector<TNode> index_trail;
  vector<TNode>::iterator it, iend;
  Node equivalence_trail = reason;
  Node current_reason;
  TNode pointer, indexRep;
  if (!index.isNull())
  {
    index_trail.push_back(index);
    marked.insert(d_ee->getRepresentative(index));
  }
  while (arrayFrom != arrayTo)
  {
    index = d_infoMap.getWeakEquivIndex(arrayFrom);
    pointer = d_infoMap.getWeakEquivPointer(arrayFrom);
    if (!index.isNull())
    {
      indexRep = d_ee->getRepresentative(index);
      if (marked.find(indexRep) == marked.end()
          && weakEquivGetRepIndex(arrayFrom, index) != arrayTo)
      {
        weakEquivMakeRepIndex(arrayFrom);
        d_infoMap.setWeakEquivSecondary(arrayFrom, arrayTo);
        current_reason = equivalence_trail;
        for (it = index_trail.begin(), iend = index_trail.end(); it != iend;
             ++it)
        {
          current_reason = current_reason.andNode(index.eqNode(*it).notNode());
        }
        d_permRef.push_back(current_reason);
        d_infoMap.setWeakEquivSecondaryReason(arrayFrom, current_reason);
      }
      marked.insert(indexRep);
    }
    else
    {
      equivalence_trail = equivalence_trail.andNode(arrayFrom.eqNode(pointer));
    }
    arrayFrom = pointer;
  }
}

void ArraySolverDefault::checkWeakEquiv(CVC5_UNUSED bool arraysMerged)
{
  eq::EqClassesIterator eqcs_i =
      eq::EqClassesIterator(&d_mayEqualEqualityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i)
  {
    Node eqc = (*eqcs_i);
    if (!eqc.getType().isArray())
    {
      continue;
    }
    eq::EqClassIterator eqc_i =
        eq::EqClassIterator(eqc, &d_mayEqualEqualityEngine);
    TNode rep = d_mayEqualEqualityEngine.getRepresentative(*eqc_i);
    TNode weakEquivRep = weakEquivGetRep(rep);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      TNode n = *eqc_i;
      Assert(!arraysMerged || weakEquivGetRep(n) == weakEquivRep);
      TNode pointer = d_infoMap.getWeakEquivPointer(n);
      TNode index = d_infoMap.getWeakEquivIndex(n);
      TNode secondary = d_infoMap.getWeakEquivSecondary(n);
      Assert(pointer.isNull() == (weakEquivGetRep(n) == n));
      Assert(!pointer.isNull() || secondary.isNull());
      Assert(!index.isNull() || secondary.isNull());
      Assert(d_infoMap.getWeakEquivSecondaryReason(n).isNull()
             || !secondary.isNull());
      if (!pointer.isNull())
      {
        if (index.isNull())
        {
          Assert(d_ee->areEqual(n, pointer));
        }
        else
        {
          Assert(
              (n.getKind() == Kind::STORE && n[0] == pointer && n[1] == index)
              || (pointer.getKind() == Kind::STORE && pointer[0] == n
                  && pointer[1] == index));
        }
      }
    }
  }
}

/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

void ArraySolverDefault::computeRelevantTerms(std::set<Node>& termSet)
{
  NodeManager* nm = nodeManager();
  // Fixed-point iteration to get all reads included because of RIntro2 rule
  bool changed;
  do
  {
    changed = false;
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_ee);
    for (; !eqcs_i.isFinished(); ++eqcs_i)
    {
      Node eqc = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_ee);
      for (; !eqc_i.isFinished(); ++eqc_i)
      {
        Node n = *eqc_i;
        if (n.getKind() == Kind::SELECT && termSet.find(n) != termSet.end())
        {
          // Find all terms equivalent to n[0] and get corresponding read terms
          Node array_eqc = d_ee->getRepresentative(n[0]);
          eq::EqClassIterator array_eqc_i =
              eq::EqClassIterator(array_eqc, d_ee);
          for (; !array_eqc_i.isFinished(); ++array_eqc_i)
          {
            Node arr = *array_eqc_i;
            if (arr.getKind() == Kind::STORE
                && termSet.find(arr) != termSet.end()
                && !d_ee->areEqual(arr[1], n[1]))
            {
              Node r = nm->mkNode(Kind::SELECT, arr, n[1]);
              if (termSet.find(r) == termSet.end() && d_ee->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(a) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
              r = nm->mkNode(Kind::SELECT, arr[0], n[1]);
              if (termSet.find(r) == termSet.end() && d_ee->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(b) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
            }
          }

          // Find all stores in which n[0] appears and get corresponding
          // read terms
          const CTNodeList* instores = d_infoMap.getInStores(array_eqc);
          size_t it = 0;
          for (; it < instores->size(); ++it)
          {
            TNode instore = (*instores)[it];
            Assert(instore.getKind() == Kind::STORE);
            if (termSet.find(instore) != termSet.end()
                && !d_ee->areEqual(instore[1], n[1]))
            {
              Node r = nm->mkNode(Kind::SELECT, instore, n[1]);
              if (termSet.find(r) == termSet.end() && d_ee->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(c) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
              r = nm->mkNode(Kind::SELECT, instore[0], n[1]);
              if (termSet.find(r) == termSet.end() && d_ee->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(d) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
            }
          }
        }
      }
    }
  } while (changed);
}

void ArraySolverDefault::augmentModelSelects(
    std::map<Node, std::vector<Node>>& /*selects*/,
    const std::set<Node>& /*termSet*/)
{
  // The default solver does not need to augment the selects map.
  // Model consistency is ensured by computeRelevantTerms (RIntro2 fixed-point).
}

/////////////////////////////////////////////////////////////////////////////
// CARE GRAPH
/////////////////////////////////////////////////////////////////////////////

void ArraySolverDefault::computeCareGraph(AddCarePairFn addCarePair)
{
  if (!d_sharedTerms)
  {
    return;
  }

  // Synchronize d_constReadsContext with SAT context
  Assert(d_constReadsContext->getLevel() <= context()->getLevel());
  while (d_constReadsContext->getLevel() < context()->getLevel())
  {
    d_constReadsContext->push();
  }

  // Go through the read terms and see if there are any to split on

  // Give constReadsContext a push so that all the work it does here is erased
  // - models can change if context changes at all.
  // The context is popped at the end.  If this loop is interrupted for some
  // reason, we have to make sure the context still gets popped or the solver
  // will be in an inconsistent state.
  d_constReadsContext->push();
  unsigned size = d_reads.size();
  for (unsigned i = 0; i < size; ++i)
  {
    TNode r1 = d_reads[i];

    Trace("arrays::sharing")
        << "TheoryArrays::computeCareGraph(): checking read " << r1
        << std::endl;
    Assert(d_ee->hasTerm(r1));
    TNode x = r1[1];

    if (!d_ee->isTriggerTerm(x, THEORY_ARRAYS))
    {
      Trace("arrays::sharing")
          << "TheoryArrays::computeCareGraph(): not connected to shared "
             "terms, skipping"
          << std::endl;
      continue;
    }
    Node x_shared = d_ee->getTriggerTermRepresentative(x, THEORY_ARRAYS);

    // Get the model value of index and find all reads that read from that same
    // model value: these are the pairs we have to check.  Also, insert this
    // read in the list at the proper index.

    if (!x_shared.isConst())
    {
      x_shared = d_valuation.getCandidateModelValue(x_shared);
    }
    if (!x_shared.isNull())
    {
      CTNodeList* temp;
      CNodeNListMap::iterator it = d_constReads.find(x_shared);
      if (it == d_constReads.end())
      {
        // This is the only x_shared with this model value - no need to create
        // any splits
        temp = new (true) CTNodeList(d_constReadsContext);
        d_constReads[x_shared] = temp;
      }
      else
      {
        temp = (*it).second;
        for (size_t j = 0; j < temp->size(); ++j)
        {
          checkPair(r1, (*temp)[j], addCarePair);
        }
      }
      temp->push_back(r1);
    }
    else
    {
      // We don't know the model value for x.  Just do brute force examination
      // of all pairs of reads.  Note that we have to loop over *all* reads
      // here, not just subsequent reads, because there may be an earlier read
      // that *does* have a model value.  So if we don't check here, the two
      // reads won't get compared.
      for (unsigned j = 0; j < size; ++j)
      {
        TNode r2 = d_reads[j];
        Assert(d_ee->hasTerm(r2));
        checkPair(r1, r2, addCarePair);
      }
      for (unsigned j = 0; j < d_constReadsList.size(); ++j)
      {
        TNode r2 = d_constReadsList[j];
        Assert(d_ee->hasTerm(r2));
        checkPair(r1, r2, addCarePair);
      }
    }
  }
  d_constReadsContext->pop();
}

/////////////////////////////////////////////////////////////////////////////
// PRESOLVE
/////////////////////////////////////////////////////////////////////////////

void ArraySolverDefault::presolve()
{
  if (!d_dstratInit)
  {
    d_dstratInit = true;
    // add the decision strategy, which is user-context-independent
    d_im.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_ARRAYS,
        d_dstrat.get(),
        DecisionManager::STRAT_SCOPE_CTX_INDEPENDENT);
  }
}

/////////////////////////////////////////////////////////////////////////////
// DECISION STRATEGY
/////////////////////////////////////////////////////////////////////////////

ArraySolverDefault::ArraySolverDefaultDecisionStrategy::
    ArraySolverDefaultDecisionStrategy(ArraySolverDefault* solver)
    : DecisionStrategy(solver->d_env), d_solver(solver)
{
}

void ArraySolverDefault::ArraySolverDefaultDecisionStrategy::initialize() {}

Node ArraySolverDefault::ArraySolverDefaultDecisionStrategy::
    getNextDecisionRequest()
{
  return d_solver->getNextDecisionRequest();
}

std::string ArraySolverDefault::ArraySolverDefaultDecisionStrategy::identify()
    const
{
  return std::string("th_arrays_dec");
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the AEXT calculus-based array solver.
 */

#include "theory/arrays/aext_solver.h"

#include <deque>

#include "expr/array_store_all.h"
#include "expr/node_manager.h"
#include "smt/logic_exception.h"
#include "theory/arrays/skolem_cache.h"
#include "theory/theory_model.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arrays {

AextArraySolver::AextArraySolver(Env& env,
                                 TheoryState& state,
                                 InferenceManager& im,
                                 Valuation valuation,
                                 eq::EqualityEngine& mayEqualEE,
                                 DefValMap& defValues)
    : ArraySolver(env, state, im, valuation, mayEqualEE, defValues),
      d_selects(context()),
      d_stores(context()),
      d_arrayDisequalities(context()),
      d_witnessDiseqs(context()),
      d_lemmaCache(context()),
      d_numCongruenceLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numCongruenceLemmas")),
      d_numAccessStoreLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numAccessStoreLemmas")),
      d_numDisequalityLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numDisequalityLemmas")),
      d_numConstArrayLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numConstArrayLemmas")),
      d_numCheckCalls(statisticsRegistry().registerInt(
          "theory::arrays::aext::numCheckCalls")),
      d_numPropagationsDown(statisticsRegistry().registerInt(
          "theory::arrays::aext::numPropagationsDown")),
      d_numPropagationsUp(statisticsRegistry().registerInt(
          "theory::arrays::aext::numPropagationsUp")),
      d_numRIntro2Propagations(statisticsRegistry().registerInt(
          "theory::arrays::aext::numRIntro2Propagations")),
      d_readReadIndexPairsValid(false),
      d_arrayModelsHash(0)
{
}

AextArraySolver::~AextArraySolver() {}

void AextArraySolver::finishInit(eq::EqualityEngine* ee)
{
  Assert(ee != nullptr);
  d_ee = ee;
}

std::string AextArraySolver::identify() const { return "AextArraySolver"; }

/////////////////////////////////////////////////////////////////////////////
// TERM REGISTRATION
/////////////////////////////////////////////////////////////////////////////

void AextArraySolver::preRegisterSelect(TNode node)
{
  Assert(node.getKind() == Kind::SELECT);
  d_selects.push_back(node);
}

void AextArraySolver::preRegisterStore(TNode node)
{
  Assert(node.getKind() == Kind::STORE);
  d_stores.push_back(node);

  // InitW: create virtual read select(store(a, i, v), i) and assert RIntro1.
  NodeManager* nm = nodeManager();
  Node ni = nm->mkNode(Kind::SELECT, node, node[1]);
  if (!d_ee->hasTerm(ni))
  {
    d_ee->addTerm(ni);
  }
  // Explicitly register the virtual read (the eqNotifyNewClass callback
  // can't do it because hasTerm already returns true).
  preRegisterSelect(ni);

  // RIntro1: select(store(a, i, v), i) = v
  Node eq = ni.eqNode(node[2]);
  d_im.assertInference(eq,
                        true,
                        InferenceId::ARRAYS_READ_OVER_WRITE_1,
                        nm->mkConst<bool>(true),
                        ProofRule::ARRAYS_READ_OVER_WRITE_1);
}

void AextArraySolver::preRegisterStoreAll(TNode /*node*/)
{
  // STORE_ALL registration for AEXT: no additional solver-specific work needed.
  // The shared code in TheoryArrays already sets d_defValues.
}

/////////////////////////////////////////////////////////////////////////////
// EQUALITY ENGINE CALLBACKS
/////////////////////////////////////////////////////////////////////////////

void AextArraySolver::eqNotifyMerge(TNode a, TNode b)
{
  mergeArraysModelOnly(a, b);
}

void AextArraySolver::mergeArraysModelOnly(TNode a, TNode b)
{
  Assert(a.getType().isArray() && b.getType().isArray());
  a = d_ee->getRepresentative(a);
  Assert(d_ee->getRepresentative(b) == a);

  Node d_true = nodeManager()->mkConst<bool>(true);

  // Maintain d_mayEqualEqualityEngine and d_defValues for model construction
  TNode mayRepA = d_mayEqualEqualityEngine.getRepresentative(a);
  TNode mayRepB = d_mayEqualEqualityEngine.getRepresentative(b);

  DefValMap::iterator itA = d_defValues.find(mayRepA);
  DefValMap::iterator itB = d_defValues.find(mayRepB);
  TNode defValue;

  if (itA != d_defValues.end())
  {
    defValue = (*itA).second;
    if ((itB != d_defValues.end() && defValue != (*itB).second)
        || (mayRepA.isConst() && mayRepB.isConst() && mayRepA != mayRepB))
    {
      throw LogicException(
          "Array theory solver does not yet support write-chains connecting "
          "two different constant arrays");
    }
  }
  else if (itB != d_defValues.end())
  {
    defValue = (*itB).second;
    if (mayRepA.isConst() && mayRepB.isConst() && mayRepA != mayRepB)
    {
      throw LogicException(
          "Array theory solver does not yet support write-chains connecting "
          "two different constant arrays");
    }
  }
  else if (mayRepA.isConst() && mayRepB.isConst() && mayRepA != mayRepB)
  {
    throw LogicException(
        "Array theory solver does not yet support write-chains connecting "
        "two different constant arrays");
  }
  d_mayEqualEqualityEngine.assertEquality(a.eqNode(b), true, d_true);
  Assert(d_mayEqualEqualityEngine.consistent());
  if (!defValue.isNull())
  {
    mayRepA = d_mayEqualEqualityEngine.getRepresentative(a);
    d_defValues[mayRepA] = defValue;
  }
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////

void AextArraySolver::notifyArrayDisequality(TNode a, TNode /*b*/, TNode reason)
{
  Assert(a.getType().isArray());
  d_arrayDisequalities.push_back(reason);
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

void AextArraySolver::postCheck(Theory::Effort level) { check(level); }

void AextArraySolver::check(Theory::Effort level)
{
  if (!Theory::fullEffort(level))
  {
    return;
  }
  if (d_state.isInConflict())
  {
    return;
  }

  ++d_numCheckCalls;
  Trace("arrays::aext") << "AextArraySolver::check() with " << d_selects.size()
                         << " selects and " << d_stores.size() << " stores"
                         << std::endl;

  // Clear per-check data structures. d_readReadIndexPairs is not cleared
  // here; computeCareGraph() invalidates it based on a hash of
  // d_arrayModels, so that combination rounds without meaningful model
  // changes can reuse the cached pairs.
  d_pendingCarePairs.clear();
  d_pendingCarePairCache.clear();
  d_checkAccessCache.clear();
  d_arrayModels.clear();

  // Build the parent store map for RowU propagation.
  buildParentMap();

  // Compute active arrays for RowU gating.
  computeActiveArrays();

  // RIntro2 theory propagation
  propagateRIntro2();

  // Propagate all registered selects through store chains.
  for (size_t i = 0, sz = d_selects.size(); i < sz; ++i)
  {
    if (d_state.isInConflict())
    {
      return;
    }
    checkAccess(d_selects[i]);
  }

  // Handle disequalities (DisEq rule)
  if (!d_state.isInConflict())
  {
    checkDisequalities();
  }

  // Pending care pairs: for pairs where at least one index is not a
  // trigger term, send explicit split lemmas since the care graph
  // cannot handle them.
  if (!d_state.isInConflict())
  {
    for (const auto& [t1, t2] : d_pendingCarePairs)
    {
      if (d_state.isInConflict())
      {
        break;
      }
      if (d_ee->areEqual(t1, t2) || d_ee->areDisequal(t1, t2, false))
      {
        continue;
      }
      // Trigger-term pairs are handled via the care graph.
      if (d_ee->isTriggerTerm(t1, THEORY_ARRAYS)
          && d_ee->isTriggerTerm(t2, THEORY_ARRAYS))
      {
        continue;
      }
      Node split = t1.eqNode(t2);
      if (d_lemmaCache.insert(split))
      {
        Trace("arrays::aext")
            << "Index split (non-shared): " << split << std::endl;
        d_im.lemma(split.orNode(split.notNode()),
                   InferenceId::ARRAYS_AEXT_INDEX_SPLIT);
      }
    }
  }

  Trace("arrays::aext") << "AextArraySolver::check() done" << std::endl;
}

void AextArraySolver::buildParentMap()
{
  d_parentStores.clear();
  for (size_t i = 0, sz = d_stores.size(); i < sz; ++i)
  {
    TNode store = d_stores[i];
    if (!d_ee->hasTerm(store))
    {
      continue;
    }
    TNode baseRep = d_ee->getRepresentative(store[0]);
    d_parentStores[baseRep].push_back(store);
  }
}

void AextArraySolver::computeActiveArrays()
{
  d_activeArrays.clear();
  std::vector<TNode> worklist;

  // Seed: find store reps whose EQ class has > 1 member.
  std::unordered_set<TNode> checked;
  for (size_t i = 0, sz = d_stores.size(); i < sz; ++i)
  {
    TNode store = d_stores[i];
    if (!d_ee->hasTerm(store))
    {
      continue;
    }
    TNode rep = d_ee->getRepresentative(store);
    if (!checked.insert(rep).second)
    {
      continue;
    }

    eq::EqClassIterator eqi(rep, d_ee);
    ++eqi;  // skip first
    if (!eqi.isFinished())
    {
      d_activeArrays.insert(rep);
      worklist.push_back(rep);
    }
  }

  // Propagate downward: mark store bases as active.
  while (!worklist.empty())
  {
    TNode rep = worklist.back();
    worklist.pop_back();
    eq::EqClassIterator eqi(rep, d_ee);
    while (!eqi.isFinished())
    {
      TNode n = *eqi;
      if (n.getKind() == Kind::STORE)
      {
        TNode baseRep = d_ee->getRepresentative(n[0]);
        if (d_activeArrays.insert(baseRep).second)
        {
          worklist.push_back(baseRep);
        }
      }
      ++eqi;
    }
  }
}

void AextArraySolver::checkAccess(TNode select)
{
  Assert(select.getKind() == Kind::SELECT);

  if (!d_checkAccessCache.insert(select).second)
  {
    return;
  }
  if (!d_ee->hasTerm(select))
  {
    return;
  }

  TNode index = select[1];
  TNode indexRep = d_ee->getRepresentative(index);
  NodeManager* nm = nodeManager();

  std::vector<TNode> visit;
  visit.push_back(select[0]);

  while (!visit.empty() && !d_state.isInConflict())
  {
    TNode array = visit.back();
    visit.pop_back();

    TNode arrayRep = d_ee->getRepresentative(array);

    // Step 1: Record this read and check for congruence (CongR).
    {
      auto& model = d_arrayModels[arrayRep];
      auto it = model.find(indexRep);
      if (it != model.end())
      {
        PropagatedRead& existing = it->second;
        if (!d_ee->areEqual(select, existing.select))
        {
          Node conc = select.eqNode(existing.select);
          std::vector<Node> expVec;
          std::vector<std::vector<PathEdge>> paths(2);
          findPathConditions(select, arrayRep, expVec, &paths[0]);
          findPathConditions(existing.select, arrayRep, expVec, &paths[1]);
          if (index != existing.index)
          {
            expVec.push_back(index.eqNode(existing.index));
          }
          Node exp = nm->mkAnd(expVec);
          Trace("arrays::aext")
              << "CongR: " << exp << " => " << conc << std::endl;
          if (d_lemmaCache.insert(conc))
          {
            d_im.arrayLemma(conc,
                            InferenceId::ARRAYS_AEXT_CONGRUENCE,
                            exp,
                            ProofRule::ARRAYS_READ_OVER_WRITE,
                            std::move(paths));
            ++d_numCongruenceLemmas;
          }
        }
        continue;
      }
      model[indexRep] = {select, index};

      // Read-read care pairs between trigger-term indices are emitted from
      // computeCareGraph() in a single pass over d_arrayModels, to avoid
      // O(N^2) work per propagation step at arrays with many reads.
    }

    // Step 2: Check for AccessStore (matching index by representative).
    {
      eq::EqClassIterator eqi(arrayRep, d_ee);
      while (!eqi.isFinished())
      {
        TNode n = *eqi;
        if (n.getKind() == Kind::STORE)
        {
          TNode storeIndexRep = d_ee->getRepresentative(n[1]);
          if (indexRep == storeIndexRep)
          {
            if (!d_ee->areEqual(select, n[2]))
            {
              Node conc = select.eqNode(n[2]);
              std::vector<Node> expVec;
              std::vector<std::vector<PathEdge>> paths(1);
              TNode entryArray =
                  findPathConditions(select, arrayRep, expVec, &paths[0]);
              if (index != n[1])
              {
                expVec.push_back(index.eqNode(n[1]));
              }
              if (entryArray != n)
              {
                expVec.push_back(entryArray.eqNode(static_cast<Node>(n)));
              }
              Node reason = nm->mkAnd(expVec);
              Trace("arrays::aext")
                  << "AccessStore: entryArray=" << entryArray << " store=" << n
                  << " reason=" << reason << " => " << conc << std::endl;
              d_im.arrayLemma(conc,
                              InferenceId::ARRAYS_AEXT_ROW,
                              reason,
                              ProofRule::ARRAYS_READ_OVER_WRITE,
                              std::move(paths));
              ++d_numAccessStoreLemmas;
            }
            break;
          }
        }
        ++eqi;
      }
    }

    // Step 2b: Check for AccessConstArray (STORE_ALL in EQ class).
    {
      eq::EqClassIterator eqca(arrayRep, d_ee);
      while (!eqca.isFinished())
      {
        TNode n = *eqca;
        if (n.getKind() == Kind::STORE_ALL)
        {
          ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
          Node defValue = storeAll.getValue();
          if (!d_ee->hasTerm(defValue) || !d_ee->areEqual(select, defValue))
          {
            Node conc = select.eqNode(defValue);
            std::vector<Node> expVec;
            std::vector<std::vector<PathEdge>> paths(1);
            TNode entryArray =
                findPathConditions(select, arrayRep, expVec, &paths[0]);
            if (entryArray != n)
            {
              expVec.push_back(entryArray.eqNode(static_cast<Node>(n)));
            }
            Node reason = nm->mkAnd(expVec);
            Trace("arrays::aext") << "AccessConstArray: " << reason << " => "
                                  << conc << std::endl;
            d_im.arrayLemma(conc,
                            InferenceId::ARRAYS_CONST_ARRAY_DEFAULT,
                            reason,
                            ProofRule::ARRAYS_READ_OVER_WRITE_1,
                            std::move(paths));
            ++d_numConstArrayLemmas;
          }
          break;
        }
        ++eqca;
      }
    }

    // Step 3: RowD -- propagate downward through stores
    {
      eq::EqClassIterator eqi2(arrayRep, d_ee);
      while (!eqi2.isFinished())
      {
        TNode n = *eqi2;
        if (n.getKind() == Kind::STORE
            && d_ee->getRepresentative(n[1]) != indexRep)
        {
          if (!d_ee->areDisequal(index, n[1], false))
          {
            Node split = index.eqNode(n[1]);
            if (!rewrite(split).isConst()
                && d_pendingCarePairCache.insert(split).second)
            {
              d_pendingCarePairs.emplace_back(index, n[1]);
            }
          }
          Trace("arrays::aext") << "  RowD push: " << n[0] << std::endl;
          visit.push_back(n[0]);
          ++d_numPropagationsDown;
        }
        ++eqi2;
      }
    }

    // Step 4: RowU -- propagate upward through parent stores.
    if (d_activeArrays.count(arrayRep))
    {
      auto pit = d_parentStores.find(arrayRep);
      if (pit != d_parentStores.end())
      {
        for (TNode store : pit->second)
        {
          TNode storeIndexRep = d_ee->getRepresentative(store[1]);
          if (indexRep != storeIndexRep)
          {
            if (!d_ee->areDisequal(index, store[1], false))
            {
              Node split = index.eqNode(store[1]);
              if (!rewrite(split).isConst()
                  && d_pendingCarePairCache.insert(split).second)
              {
                d_pendingCarePairs.emplace_back(index, store[1]);
              }
            }
            Trace("arrays::aext") << "  RowU push: " << store << std::endl;
            visit.push_back(store);
            ++d_numPropagationsUp;
          }
        }
      }
    }
  }
}

TNode AextArraySolver::findPathConditions(TNode select,
                                          TNode targetRep,
                                          std::vector<Node>& conds,
                                          std::vector<PathEdge>* pathEdges)
{
  TNode index = select[1];
  TNode indexRep = d_ee->getRepresentative(index);
  TNode startArray = select[0];
  TNode startRep = d_ee->getRepresentative(startArray);

  // Trivial case: already at target.
  if (startRep == targetRep)
  {
    if (startArray != startRep)
    {
      conds.push_back(startArray.eqNode(static_cast<Node>(startRep)));
    }
    if (pathEdges)
    {
      pathEdges->push_back({TNode(), false});
    }
    return startArray;
  }

  struct BFSEdge
  {
    TNode entryArray;
    TNode store;
    TNode fromRep;
    bool isRowU;
  };

  std::unordered_map<TNode, BFSEdge> bfsEdges;
  bfsEdges[startRep] = {startArray, TNode(), TNode(), false};

  std::deque<TNode> queue;
  queue.push_back(startRep);
  bool found = false;

  while (!queue.empty() && !found)
  {
    TNode arrayRep = queue.front();
    queue.pop_front();

    // RowD
    {
      eq::EqClassIterator eqi(arrayRep, d_ee);
      while (!eqi.isFinished() && !found)
      {
        TNode n = *eqi;
        if (n.getKind() == Kind::STORE
            && d_ee->getRepresentative(n[1]) != indexRep)
        {
          TNode childRep = d_ee->getRepresentative(n[0]);
          if (bfsEdges.find(childRep) == bfsEdges.end())
          {
            bfsEdges[childRep] = {n[0], n, arrayRep, false};
            if (childRep == targetRep)
            {
              found = true;
            }
            else
            {
              queue.push_back(childRep);
            }
          }
        }
        ++eqi;
      }
    }

    if (found)
    {
      break;
    }

    // RowU
    {
      auto pit = d_parentStores.find(arrayRep);
      if (pit != d_parentStores.end())
      {
        for (TNode store : pit->second)
        {
          if (d_ee->getRepresentative(store[1]) != indexRep)
          {
            TNode storeRep = d_ee->getRepresentative(store);
            if (bfsEdges.find(storeRep) == bfsEdges.end())
            {
              bfsEdges[storeRep] = {store, store, arrayRep, true};
              if (storeRep == targetRep)
              {
                found = true;
                break;
              }
              queue.push_back(storeRep);
            }
          }
        }
      }
    }
  }

  Assert(found) << "findPathConditions: no path from " << startArray
                << " to rep " << targetRep;

  // Walk back from targetRep to startRep, extracting conditions.
  TNode cur = targetRep;
  while (true)
  {
    auto it = bfsEdges.find(cur);
    Assert(it != bfsEdges.end());
    const BFSEdge& be = it->second;

    if (be.store.isNull())
    {
      if (be.entryArray != cur)
      {
        conds.push_back(be.entryArray.eqNode(static_cast<Node>(cur)));
      }
      if (pathEdges)
      {
        pathEdges->push_back({TNode(), false});
      }
      break;
    }

    if (be.entryArray != cur)
    {
      conds.push_back(be.entryArray.eqNode(static_cast<Node>(cur)));
    }

    auto pit = bfsEdges.find(be.fromRep);
    Assert(pit != bfsEdges.end());
    TNode prevEntry = pit->second.entryArray;

    if (be.isRowU)
    {
      if (prevEntry != be.store[0])
      {
        conds.push_back(prevEntry.eqNode(be.store[0]));
      }
    }
    else
    {
      if (prevEntry != be.store)
      {
        conds.push_back(prevEntry.eqNode(static_cast<Node>(be.store)));
      }
    }
    conds.push_back(index.eqNode(be.store[1]).notNode());

    if (pathEdges)
    {
      pathEdges->push_back({be.store, be.isRowU});
    }

    cur = be.fromRep;
  }

  return bfsEdges[targetRep].entryArray;
}

void AextArraySolver::propagateRIntro2()
{
  NodeManager* nm = nodeManager();

  // Build readsByArray[arrayRep][indexRep] -> existing select.
  std::unordered_map<TNode, std::unordered_map<TNode, TNode>> readsByArray;
  for (size_t i = 0, sz = d_selects.size(); i < sz; ++i)
  {
    TNode s = d_selects[i];
    if (!d_ee->hasTerm(s)) continue;
    TNode aRep = d_ee->getRepresentative(s[0]);
    TNode iRep = d_ee->getRepresentative(s[1]);
    readsByArray[aRep][iRep] = s;
  }

  // Iterate stores and look for propagation opportunities.
  for (size_t si = 0, ssz = d_stores.size(); si < ssz; ++si)
  {
    if (d_state.isInConflict()) return;
    TNode store = d_stores[si];
    if (!d_ee->hasTerm(store)) continue;
    TNode k = store[1];
    TNode storeRep = d_ee->getRepresentative(store);
    TNode baseRep = d_ee->getRepresentative(store[0]);

    if (storeRep == baseRep) continue;

    auto storeIt = readsByArray.find(storeRep);
    if (storeIt == readsByArray.end()) continue;

    auto baseIt = readsByArray.find(baseRep);
    if (baseIt == readsByArray.end()) continue;

    for (const auto& [jRep, rN] : storeIt->second)
    {
      if (d_state.isInConflict()) return;
      if (d_ee->getRepresentative(k) == jRep) continue;

      auto rit = baseIt->second.find(jRep);
      if (rit == baseIt->second.end()) continue;
      TNode rC = rit->second;
      if (rN == rC || d_ee->areEqual(rN, rC)) continue;

      TNode j = rN[1];

      if (d_ee->areDisequal(j, k, true))
      {
        Node eq = rN.eqNode(rC);
        if (!d_lemmaCache.insert(eq)) continue;
        std::vector<Node> expVec;
        if (rN[0] != store)
        {
          expVec.push_back(rN[0].eqNode(static_cast<Node>(store)));
        }
        if (rC[0] != store[0])
        {
          expVec.push_back(rC[0].eqNode(store[0]));
        }
        if (rC[1] != j)
        {
          expVec.push_back(rC[1].eqNode(j));
        }
        expVec.push_back(j.eqNode(k).notNode());
        Node reason = nm->mkAnd(expVec);
        Trace("arrays::aext")
            << "RIntro2: " << reason << " => " << eq << std::endl;
        d_im.arrayLemma(eq,
                        InferenceId::ARRAYS_READ_OVER_WRITE,
                        reason,
                        ProofRule::ARRAYS_READ_OVER_WRITE);
        d_im.assertInference(eq,
                             true,
                             InferenceId::ARRAYS_READ_OVER_WRITE,
                             reason,
                             ProofRule::ARRAYS_READ_OVER_WRITE);
        ++d_numRIntro2Propagations;
        continue;
      }
    }
  }
}

void AextArraySolver::checkDisequalities()
{
  NodeManager* nm = nodeManager();

  for (size_t i = 0, sz = d_arrayDisequalities.size(); i < sz; ++i)
  {
    if (d_state.isInConflict())
    {
      break;
    }
    TNode fact = d_arrayDisequalities[i];
    if (d_witnessDiseqs.contains(fact))
    {
      continue;
    }
    d_witnessDiseqs.insert(fact);

    TNode a = fact[0][0];
    TNode b = fact[0][1];

    // Cap witness lemmas per canonical (rep_a, rep_b) pair. Once the cap is
    // reached, further facts mapping to the same pair are covered via EE
    // congruence by one of the already-emitted lemmas; emitting more only
    // bloats the SAT clause database with duplicate-modulo-congruence
    // extensionality axioms. The cap preserves SAT steering on small
    // problems (where each fact's witness tends to be distinct) and caps
    // blowup on larger ones (where many facts share a representative pair).
    constexpr uint32_t kWitnessCapPerRepPair = 30;
    TNode repA = d_ee->getRepresentative(a);
    TNode repB = d_ee->getRepresentative(b);
    Node repPair = repA < repB ? repA.eqNode(repB) : repB.eqNode(repA);
    uint32_t& count = d_witnessRepPairCount[repPair];
    if (count >= kWitnessCapPerRepPair)
    {
      continue;
    }
    ++count;

    Node k = SkolemCache::getExtIndexSkolem(nm, fact);
    Node ak = nm->mkNode(Kind::SELECT, a, k);
    Node bk = nm->mkNode(Kind::SELECT, b, k);

    Node eq = ak.eqNode(bk);
    Trace("arrays::aext") << "DisEq lemma: " << fact << " => " << eq.notNode()
                           << std::endl;
    d_im.arrayLemma(eq.notNode(),
                    InferenceId::ARRAYS_AEXT_DISEQUALITY,
                    fact,
                    ProofRule::ARRAYS_EXT);
    ++d_numDisequalityLemmas;
  }
}

/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

void AextArraySolver::computeRelevantTerms(std::set<Node>& /*termSet*/)
{
  // AEXT solver does not need RIntro2 fixed-point for relevant terms.
  // Model consistency is ensured by augmentModelSelects() which propagates
  // reads through store chains in both directions.
}

void AextArraySolver::augmentModelSelects(
    std::map<Node, std::vector<Node>>& selects, const std::set<Node>& termSet)
{
  // Propagate reads through store chains in both directions.
  // The AEXT solver does not create explicit select(base, i) terms via
  // Row lemmas, so the model builder needs to trace reads through stores
  // to ensure all arrays in a store chain get consistent values.

  // Precompute map from child array rep to parent store nodes.
  std::unordered_map<TNode, std::vector<TNode>> parentStores;
  {
    eq::EqClassesIterator eqcs = eq::EqClassesIterator(d_ee);
    for (; !eqcs.isFinished(); ++eqcs)
    {
      Node eqc = (*eqcs);
      if (!eqc.getType().isArray())
      {
        continue;
      }
      eq::EqClassIterator eci(eqc, d_ee);
      for (; !eci.isFinished(); ++eci)
      {
        TNode t = *eci;
        if (t.getKind() == Kind::STORE)
        {
          TNode childRep = d_ee->getRepresentative(t[0]);
          parentStores[childRep].push_back(t);
        }
      }
    }
  }

  for (set<Node>::iterator si = termSet.begin(); si != termSet.end(); ++si)
  {
    Node n = *si;
    if (n.getKind() != Kind::SELECT)
    {
      continue;
    }
    TNode idx = n[1];
    // Walk through array reps, following store chains and EE merges
    // in both directions.
    std::vector<TNode> visit;
    std::unordered_set<TNode> visited;
    visit.push_back(d_ee->getRepresentative(n[0]));
    while (!visit.empty())
    {
      TNode arrRep = visit.back();
      visit.pop_back();
      if (!visited.insert(arrRep).second)
      {
        continue;
      }
      // Downward: iterate stores in this EQ class, follow to children.
      eq::EqClassIterator eci(arrRep, d_ee);
      for (; !eci.isFinished(); ++eci)
      {
        TNode t = *eci;
        if (t.getKind() == Kind::STORE)
        {
          if (!d_ee->areEqual(idx, t[1]))
          {
            TNode baseRep = d_ee->getRepresentative(t[0]);
            selects[baseRep].push_back(n);
            visit.push_back(baseRep);
          }
        }
      }
      // Upward: find stores whose child is in this class.
      auto pit = parentStores.find(arrRep);
      if (pit != parentStores.end())
      {
        for (TNode s : pit->second)
        {
          if (!d_ee->areEqual(idx, s[1]))
          {
            TNode storeRep = d_ee->getRepresentative(s);
            selects[storeRep].push_back(n);
            visit.push_back(storeRep);
          }
        }
      }
    }
  }
}

/////////////////////////////////////////////////////////////////////////////
// CARE GRAPH
/////////////////////////////////////////////////////////////////////////////

void AextArraySolver::computeCareGraph(AddCarePairFn addCarePair)
{
  // Check whether cached read-read pairs are still valid for the current
  // d_arrayModels. Between two consecutive combination rounds, check() may
  // have re-propagated but often produces the same set of (arrayRep,
  // indexRep) entries, so the cache can be reused. Use a commutative hash
  // so iteration order of the underlying unordered_maps does not matter.
  size_t hash = d_arrayModels.size();
  for (const auto& [arrayRep, model] : d_arrayModels)
  {
    size_t idxHash = 0;
    for (const auto& [idxRep, read] : model)
    {
      idxHash += std::hash<TNode>()(idxRep);
    }
    hash += std::hash<TNode>()(arrayRep) * 31 + model.size() * 17 + idxHash;
  }
  if (hash != d_arrayModelsHash)
  {
    d_arrayModelsHash = hash;
    d_readReadIndexPairs.clear();
    d_readReadIndexPairsValid = false;
  }

  for (const auto& [t1, t2] : d_pendingCarePairs)
  {
    if (d_ee->areEqual(t1, t2) || d_ee->areDisequal(t1, t2, false))
    {
      continue;
    }
    if (!d_ee->isTriggerTerm(t1, THEORY_ARRAYS)
        || !d_ee->isTriggerTerm(t2, THEORY_ARRAYS))
    {
      continue;
    }
    TNode s1 = d_ee->getTriggerTermRepresentative(t1, THEORY_ARRAYS);
    TNode s2 = d_ee->getTriggerTermRepresentative(t2, THEORY_ARRAYS);
    if (s1 == s2)
    {
      continue;
    }
    EqualityStatus es = d_valuation.getEqualityStatus(s1, s2);
    if (es == EQUALITY_FALSE || es == EQUALITY_FALSE_AND_PROPAGATED
        || es == EQUALITY_FALSE_IN_MODEL)
    {
      continue;
    }
    Trace("arrays::sharing")
        << "AEXT care pair: " << t1 << " vs " << t2 << " shared=(" << s1 << ", "
        << s2 << ")" << std::endl;
    addCarePair(s1, s2);
  }
  // Read-read care pairs: pairwise between trigger-term index reads at the
  // same array. Populate d_readReadIndexPairs on the first call after each
  // check() (O(K^2) per array, doing all EE-based filtering once) and reuse
  // it across subsequent combination rounds until the next check()
  // invalidates it. Between combination rounds without an intervening
  // check(), EE is stable, so trigger-term reps and areEqual/areDisequal
  // results do not change.
  if (!d_readReadIndexPairsValid)
  {
    // For each arrayRep we partition reads in d_arrayModels[arrayRep] into:
    //  - native: the read's original array is EE-equal to arrayRep
    //    (i.e., read.select[0] EE-equal to arrayRep)
    //  - propagated: reached arrayRep via a Row step through store chains
    // TheoryArrays::computeCareGraph() already enumerates all pairs of
    // reads in d_reads via its O(|d_reads|^2) checkPair loop, which emits
    // every care pair whose read arrays share a may-equal class. Two
    // native reads at arrayRep are both EE-equal (hence may-equal) to
    // arrayRep, so TheoryArrays will already emit their pair. AEXT only
    // needs to cover pairs where at least one side is a propagated read,
    // since such reads can land at an arrayRep that is not EE-equal to
    // the read's original array.
    std::vector<TNode> triggerIndices;
    std::vector<TNode> triggerReps;
    std::vector<bool> isPropagated;
    for (const auto& [arrayRep, model] : d_arrayModels)
    {
      triggerIndices.clear();
      triggerReps.clear();
      isPropagated.clear();
      for (const auto& [idxRep, read] : model)
      {
        if (!d_ee->isTriggerTerm(read.index, THEORY_ARRAYS)) continue;
        triggerIndices.push_back(read.index);
        triggerReps.push_back(
            d_ee->getTriggerTermRepresentative(read.index, THEORY_ARRAYS));
        isPropagated.push_back(d_ee->getRepresentative(read.select[0])
                               != arrayRep);
      }
      for (size_t i = 0, sz = triggerIndices.size(); i < sz; ++i)
      {
        TNode idx1 = triggerIndices[i];
        TNode s1 = triggerReps[i];
        bool prop1 = isPropagated[i];
        for (size_t j = i + 1; j < sz; ++j)
        {
          if (!prop1 && !isPropagated[j]) continue;
          TNode s2 = triggerReps[j];
          if (s1 == s2) continue;
          TNode idx2 = triggerIndices[j];
          if (d_ee->areDisequal(idx1, idx2, false)) continue;
          d_readReadIndexPairs.emplace_back(s1, s2);
        }
      }
    }
    d_readReadIndexPairsValid = true;
  }
  for (const auto& [s1, s2] : d_readReadIndexPairs)
  {
    EqualityStatus es = d_valuation.getEqualityStatus(s1, s2);
    if (es == EQUALITY_FALSE || es == EQUALITY_FALSE_AND_PROPAGATED
        || es == EQUALITY_FALSE_IN_MODEL)
    {
      continue;
    }
    Trace("arrays::sharing") << "AEXT care pair (read-read): shared=(" << s1
                             << ", " << s2 << ")" << std::endl;
    addCarePair(s1, s2);
  }
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

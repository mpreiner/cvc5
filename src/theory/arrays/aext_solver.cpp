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
#include "theory/arrays/skolem_cache.h"
#include "theory/theory_model.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arrays {

AextArraySolver::AextArraySolver(Env& env,
                                 TheoryState& state,
                                 InferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_ee(nullptr),
      d_selects(context()),
      d_stores(context()),
      d_arrayDisequalities(context()),
      d_witnessDiseqs(context()),
      d_lemmaCache(context()),
      d_numIndexSplitLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numIndexSplitLemmas")),
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
          "theory::arrays::aext::numPropagationsUp"))
{
}

AextArraySolver::~AextArraySolver() {}

void AextArraySolver::finishInit(eq::EqualityEngine* ee)
{
  Assert(ee != nullptr);
  d_ee = ee;
}

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

void AextArraySolver::notifyMerge(TNode /*a*/, TNode /*b*/)
{
  // Merges are handled lazily: the next check() call will re-propagate
  // selects through the updated equivalence classes.
}

void AextArraySolver::notifyDisequality(TNode a, TNode /*b*/, TNode reason)
{
  Assert(a.getType().isArray());
  d_arrayDisequalities.push_back(reason);
}

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

  // Clear per-check data structures
  d_pendingSplits.clear();
  d_pendingSplitCache.clear();
  d_checkAccessCache.clear();
  d_arrayModels.clear();

  // Build the parent store map for RowU propagation.
  buildParentMap();

  // Compute active arrays for RowU gating.
  computeActiveArrays();

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

  // Send pending index splits.  Use model-based filtering: splits where
  // the indices have different equality status in the current SAT model
  // are deferred (they will be retried on future check() calls since
  // d_pendingSplitCache is per-check, not context-dependent).
  if (!d_state.isInConflict())
  {
    Valuation& val = d_state.getValuation();
    for (const auto& [t1, t2] : d_pendingSplits)
    {
      if (d_state.isInConflict())
      {
        break;
      }
      // Skip if already decided by the EE during this check.
      if (d_ee->areEqual(t1, t2) || d_ee->areDisequal(t1, t2, false))
      {
        continue;
      }
      // Filter by model equality status when available.
      if (d_ee->isTriggerTerm(t1, THEORY_ARRAYS)
          && d_ee->isTriggerTerm(t2, THEORY_ARRAYS))
      {
        Node s1 = d_ee->getTriggerTermRepresentative(t1, THEORY_ARRAYS);
        Node s2 = d_ee->getTriggerTermRepresentative(t2, THEORY_ARRAYS);
        EqualityStatus eqStatus = val.getEqualityStatus(s1, s2);
        if (eqStatus == EQUALITY_FALSE
            || eqStatus == EQUALITY_FALSE_AND_PROPAGATED
            || eqStatus == EQUALITY_FALSE_IN_MODEL)
        {
          continue;
        }
      }
      Node split = t1.eqNode(t2);
      if (d_lemmaCache.insert(split))
      {
        Trace("arrays::aext") << "Index split: " << split << std::endl;
        d_im.lemma(split.orNode(split.notNode()),
                   InferenceId::ARRAYS_AEXT_INDEX_SPLIT);
        ++d_numIndexSplitLemmas;
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

  // Lightweight visit stack: just the array node, no path conditions
  // or predecessor edges.  Path conditions are reconstructed on demand
  // via findPathConditions() when a conflict is detected.
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
        // CongR: two reads reached the same array (by representative)
        // at the same index. Check if their values differ.
        if (!d_ee->areEqual(select, existing.select))
        {
          Node conc = select.eqNode(existing.select);
          // Reconstruct path conditions from both reads via BFS.
          std::vector<Node> expVec;
          findPathConditions(select, arrayRep, expVec);
          findPathConditions(existing.select, arrayRep, expVec);
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
                            ProofRule::ARRAYS_READ_OVER_WRITE);
            ++d_numCongruenceLemmas;
          }
        }
        continue;
      }
      model[indexRep] = {select, index};
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
            // AccessStore: read index matches store index (same EE rep).
            // The value should be the stored value n[2].
            if (!d_ee->areEqual(select, n[2]))
            {
              Node conc = select.eqNode(n[2]);
              std::vector<Node> expVec;
              TNode entryArray = findPathConditions(select, arrayRep, expVec);
              if (index != n[1])
              {
                expVec.push_back(index.eqNode(n[1]));
              }
              // Guard with array equality if the entry array (the node
              // reached by the BFS) differs from the store (meaning the
              // store was brought in by an EE merge within this class).
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
                              ProofRule::ARRAYS_READ_OVER_WRITE);
              ++d_numAccessStoreLemmas;
            }
            break;
          }
        }
        ++eqi;
      }
    }

    // Step 2b: Check for AccessConstArray (STORE_ALL in EQ class).
    // When a read reaches a constant array, assert sel = defaultValue.
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
            TNode entryArray = findPathConditions(select, arrayRep, expVec);
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
                            ProofRule::TRUST);
            ++d_numConstArrayLemmas;
          }
          break;
        }
        ++eqca;
      }
    }

    // Step 3: RowD -- propagate downward through stores whose index
    // has a different representative.
    {
      eq::EqClassIterator eqi2(arrayRep, d_ee);
      while (!eqi2.isFinished())
      {
        TNode n = *eqi2;
        if (n.getKind() == Kind::STORE
            && d_ee->getRepresentative(n[1]) != indexRep)
        {
          // Representatives differ → pass through (RowD).
          // Record the pending split so the SAT solver can decide
          // whether the indices are actually equal.
          if (!d_ee->areDisequal(index, n[1], false))
          {
            Node split = index.eqNode(n[1]);
            if (!rewrite(split).isConst()
                && d_pendingSplitCache.insert(split).second)
            {
              d_pendingSplits.emplace_back(index, n[1]);
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
    // Only propagate if this array rep is active (reachable from an
    // equality chain). Without equalities, RowD alone suffices.
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
                  && d_pendingSplitCache.insert(split).second)
              {
                d_pendingSplits.emplace_back(index, store[1]);
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
                                          std::vector<Node>& conds)
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
    return startArray;
  }

  // BFS edge: same structure as the old PropEdge, but built on demand.
  struct BFSEdge
  {
    TNode entryArray; /**< concrete array node at this rep */
    TNode store;      /**< store traversed (null for start) */
    TNode fromRep;    /**< source rep (null for start) */
    bool isRowU;      /**< true if RowU edge */
  };

  std::unordered_map<TNode, BFSEdge> edges;
  edges[startRep] = {startArray, TNode(), TNode(), false};

  // BFS queue of array representatives.
  std::deque<TNode> queue;
  queue.push_back(startRep);
  bool found = false;

  while (!queue.empty() && !found)
  {
    TNode arrayRep = queue.front();
    queue.pop_front();

    // RowD: iterate EQ class for stores with different index.
    {
      eq::EqClassIterator eqi(arrayRep, d_ee);
      while (!eqi.isFinished() && !found)
      {
        TNode n = *eqi;
        if (n.getKind() == Kind::STORE
            && d_ee->getRepresentative(n[1]) != indexRep)
        {
          TNode childRep = d_ee->getRepresentative(n[0]);
          if (edges.find(childRep) == edges.end())
          {
            edges[childRep] = {n[0], n, arrayRep, false};
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

    // RowU: parent stores with different index.
    {
      auto pit = d_parentStores.find(arrayRep);
      if (pit != d_parentStores.end())
      {
        for (TNode store : pit->second)
        {
          if (d_ee->getRepresentative(store[1]) != indexRep)
          {
            TNode storeRep = d_ee->getRepresentative(store);
            if (edges.find(storeRep) == edges.end())
            {
              edges[storeRep] = {store, store, arrayRep, true};
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
    auto it = edges.find(cur);
    Assert(it != edges.end());
    const BFSEdge& edge = it->second;

    if (edge.store.isNull())
    {
      // Start node — add initial EE merge guard if needed.
      if (edge.entryArray != cur)
      {
        conds.push_back(edge.entryArray.eqNode(static_cast<Node>(cur)));
      }
      break;
    }

    // Guard for EE merge between the entry array and its representative.
    if (edge.entryArray != cur)
    {
      conds.push_back(edge.entryArray.eqNode(static_cast<Node>(cur)));
    }

    // Look up the entry array at the source rep.
    auto pit = edges.find(edge.fromRep);
    Assert(pit != edges.end());
    TNode prevEntry = pit->second.entryArray;

    if (edge.isRowU)
    {
      // RowU: we pushed the store itself; guard is prevEntry = store[0]
      if (prevEntry != edge.store[0])
      {
        conds.push_back(prevEntry.eqNode(edge.store[0]));
      }
    }
    else
    {
      // RowD: we pushed store[0]; guard is prevEntry = store
      if (prevEntry != edge.store)
      {
        conds.push_back(prevEntry.eqNode(static_cast<Node>(edge.store)));
      }
    }
    // Index disequality condition for passing through this store.
    conds.push_back(index.eqNode(edge.store[1]).notNode());

    cur = edge.fromRep;
  }

  return edges[targetRep].entryArray;
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

bool AextArraySolver::collectModelValues(TheoryModel* /*m*/,
                                         const std::set<Node>& /*termSet*/)
{
  return true;
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

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
      d_numCongruenceLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numCongruenceLemmas")),
      d_numAccessStoreLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numAccessStoreLemmas")),
      d_numDisequalityLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numDisequalityLemmas")),
      d_numCheckCalls(statisticsRegistry().registerInt(
          "theory::arrays::aext::numCheckCalls"))
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
  d_checkAccessCache.clear();
  d_arrayModels.clear();
  d_propEdgeMaps.clear();

  // Build the parent store map for RowU propagation.
  buildParentMap();

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

  // Propagation edge map for this select — records how each arrayRep
  // was reached, for lazy path condition reconstruction.
  PropEdgeMap& edgeMap = d_propEdgeMaps[select];

  // Lightweight visit stack: just the array node, no path conditions.
  std::vector<TNode> visit;
  TNode startRep = d_ee->getRepresentative(select[0]);
  // Record start node (no predecessor edge).
  edgeMap[startRep] = {select[0], TNode(), TNode(), false};
  visit.push_back(select[0]);

  std::unordered_set<TNode> visited;

  while (!visit.empty() && !d_state.isInConflict())
  {
    TNode array = visit.back();
    visit.pop_back();

    TNode arrayRep = d_ee->getRepresentative(array);
    if (!visited.insert(arrayRep).second)
    {
      continue;
    }

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
          // Reconstruct path conditions from both reads.
          std::vector<Node> expVec;
          collectPathConditions(select, arrayRep, edgeMap, expVec);
          collectPathConditions(existing.select,
                                arrayRep,
                                d_propEdgeMaps[existing.select],
                                expVec);
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
            // Reconstruct path conditions to this rep.
            std::vector<Node> expVec;
            collectPathConditions(select, arrayRep, edgeMap, expVec);
            if (index != n[1])
            {
              expVec.push_back(index.eqNode(n[1]));
            }
            // Guard with array equality if the entry array (where the
            // read was propagated to) differs from the store (meaning
            // the store was brought in by an EE merge within this
            // equivalence class).
            TNode entryArray = edgeMap[arrayRep].entryArray;
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

    // Step 3: RowD -- propagate downward through stores whose index
    // has a different representative. Even if AccessStore matched one
    // store, propagate through OTHER stores in the same EQ class (they
    // may be from a different store chain brought in by an equality).
    {
      TNode entryArray = edgeMap[arrayRep].entryArray;
      eq::EqClassIterator eqi2(arrayRep, d_ee);
      while (!eqi2.isFinished())
      {
        TNode n = *eqi2;
        if (n.getKind() == Kind::STORE
            && d_ee->getRepresentative(n[1]) != indexRep)
        {
          // Representatives differ → pass through (RowD).
          // Also generate a splitting lemma if the EE doesn't know
          // the disequality, so the SAT solver considers both cases.
          if (!d_ee->areDisequal(index, n[1], false))
          {
            Node split = index.eqNode(n[1]);
            // Skip if the rewriter can decide the equality (e.g.,
            // arithmetic proves i != i+1), as the split would be
            // trivially true and trigger an assertion in the IM.
            if (!rewrite(split).isConst() && d_lemmaCache.insert(split))
            {
              Trace("arrays::aext") << "Index split: " << split << std::endl;
              d_im.lemma(split.orNode(split.notNode()),
                         InferenceId::ARRAYS_AEXT_ROW);
            }
          }
          TNode childRep = d_ee->getRepresentative(n[0]);
          if (visited.find(childRep) == visited.end()
              && edgeMap.find(childRep) == edgeMap.end())
          {
            edgeMap[childRep] = {n[0], n, arrayRep, false};
            Trace("arrays::aext") << "  RowD push: " << n[0] << std::endl;
            visit.push_back(n[0]);
          }
        }
        ++eqi2;
      }
    }

    // Step 4: RowU -- always propagate upward through parent stores
    // whose base is in this EQ class, when the store index has a
    // different representative from the read index.
    {
      TNode entryArray = edgeMap[arrayRep].entryArray;
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
              // Skip if the rewriter can decide the equality (e.g.,
              // arithmetic proves i != i+1), as the split would be
              // trivially true and trigger an assertion in the IM.
              if (!rewrite(split).isConst() && d_lemmaCache.insert(split))
              {
                Trace("arrays::aext") << "Index split: " << split << std::endl;
                d_im.lemma(split.orNode(split.notNode()),
                           InferenceId::ARRAYS_AEXT_ROW);
              }
            }
            TNode storeRep = d_ee->getRepresentative(store);
            if (visited.find(storeRep) == visited.end()
                && edgeMap.find(storeRep) == edgeMap.end())
            {
              edgeMap[storeRep] = {store, store, arrayRep, true};
              Trace("arrays::aext") << "  RowU push: " << store << std::endl;
              visit.push_back(store);
            }
          }
        }
      }
    }
  }
}

void AextArraySolver::collectPathConditions(TNode select,
                                            TNode conflictRep,
                                            const PropEdgeMap& edgeMap,
                                            std::vector<Node>& conds)
{
  TNode index = select[1];

  // Walk back from conflictRep to the start of the propagation.
  TNode cur = conflictRep;
  while (true)
  {
    auto it = edgeMap.find(cur);
    Assert(it != edgeMap.end());
    const PropEdge& edge = it->second;

    if (edge.store.isNull())
    {
      // Start node — add initial EE merge guard if needed.
      if (edge.entryArray != cur)
      {
        conds.push_back(edge.entryArray.eqNode(static_cast<Node>(cur)));
      }
      break;
    }

    // Guard for EE merge between the pushed array and its representative.
    // E.g., RowU pushes store(a,i,v) but its rep is some other term R;
    // we need the guard store(a,i,v) = R.
    if (edge.entryArray != cur)
    {
      conds.push_back(edge.entryArray.eqNode(static_cast<Node>(cur)));
    }

    // Look up the entry array at the source rep (prevEntry).
    auto pit = edgeMap.find(edge.fromRep);
    Assert(pit != edgeMap.end());
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
    d_im.arrayLemma(
        eq.notNode(), InferenceId::ARRAYS_EXT, fact, ProofRule::ARRAYS_EXT);
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

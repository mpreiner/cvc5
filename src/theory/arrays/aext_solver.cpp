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
      d_lemmaCache(userContext()),
      d_numRowLemmas(statisticsRegistry().registerInt(
          "theory::arrays::aext::numRowLemmas")),
      d_numDisequality(statisticsRegistry().registerInt(
          "theory::arrays::aext::numDisequality")),
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
  // InitW: assert RIntro1 axiom select(store(a, i, v), i) = v
  NodeManager* nm = nodeManager();
  Node ni = nm->mkNode(Kind::SELECT, node, node[1]);
  if (!d_ee->hasTerm(ni))
  {
    d_ee->addTerm(ni);
  }
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
  // selects through the updated equivalence classes. The parent map is
  // rebuilt each check() so new merges are automatically reflected.
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

  // Clear per-check caches
  d_checkCache.clear();

  // Build the parent store map for RowU propagation.
  // Maps array representative -> STORE terms whose base is in that EQ class.
  buildParentMap();

  // Propagate all selects through store chains (RowD + RowU).
  // No fixed-point loop needed within a single check(): lemmas go to the SAT
  // solver and trigger a new check() call when processed. Internal facts
  // (assertInference) take effect immediately via the EE.
  for (size_t i = 0, sz = d_selects.size(); i < sz; ++i)
  {
    if (d_state.isInConflict())
    {
      return;
    }
    propagateSelect(d_selects[i]);
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
    Trace("arrays::aext::debug")
        << "  parentMap: rep(" << store[0] << ") = " << baseRep << " -> store "
        << store << std::endl;
  }
}

bool AextArraySolver::propagateSelect(TNode select)
{
  Assert(select.getKind() == Kind::SELECT);

  // Skip if already propagated in this check
  if (!d_checkCache.insert(select).second)
  {
    return false;
  }
  if (!d_ee->hasTerm(select))
  {
    return false;
  }

  bool changed = false;
  TNode index = select[1];
  TNode arrayRep = d_ee->getRepresentative(select[0]);

  Trace("arrays::aext::debug") << "  propagateSelect: " << select
                               << " arrayRep=" << arrayRep << std::endl;

  // RowD: look for STORE terms in the equivalence class of the array.
  // If the array is equal to store(b, j, v), propagate the read through it.
  eq::EqClassIterator eqi(arrayRep, d_ee);
  while (!eqi.isFinished())
  {
    TNode n = *eqi;
    if (n.getKind() == Kind::STORE)
    {
      changed |= generateRowLemma(n, index);
    }
    ++eqi;
  }

  // RowU: look for STORE terms whose base is in this equivalence class.
  // If store(a, j, v) exists where a is in the same EQ class as select's
  // array, then the read on a can be connected to a read on the store.
  auto it = d_parentStores.find(arrayRep);
  if (it != d_parentStores.end())
  {
    for (TNode store : it->second)
    {
      changed |= generateRowLemma(store, index);
    }
  }

  return changed;
}

bool AextArraySolver::generateRowLemma(TNode store, TNode index)
{
  Assert(store.getKind() == Kind::STORE);
  TNode storeIndex = store[1];

  // Row-eq case: i = j, handled by RIntro1 + EE congruence
  if (d_ee->areEqual(index, storeIndex))
  {
    return false;
  }

  NodeManager* nm = nodeManager();
  Node selStore = nm->mkNode(Kind::SELECT, store, index);
  Node selBase = nm->mkNode(Kind::SELECT, store[0], index);

  // Check if the rewriter can simplify these to the same term
  // (e.g., when the index is a concrete constant different from storeIndex)
  if (rewrite(selStore) == rewrite(selBase))
  {
    return false;
  }

  // If both terms exist in the EE and are already equal, nothing to do
  if (d_ee->hasTerm(selStore) && d_ee->hasTerm(selBase)
      && d_ee->areEqual(selStore, selBase))
  {
    return false;
  }

  // Generate the Row lemma (deduplicated).
  // The lemma is: i = j OR select(store(b, j, v), i) = select(b, i)
  // This is the standard disjunctive form of the read-over-write axiom.
  Node lemmaConc = selStore.eqNode(selBase);

  // Skip tautological lemmas (e.g. when the rewriter can simplify the
  // select through the store already).
  if (rewrite(lemmaConc).isConst())
  {
    return false;
  }

  if (!d_lemmaCache.insert(lemmaConc))
  {
    return false;
  }

  Node lemmaExp = index.eqNode(storeIndex).notNode();
  Trace("arrays::aext") << "AextArraySolver::generateRowLemma: " << lemmaExp
                        << " => " << lemmaConc << std::endl;
  d_im.arrayLemma(lemmaConc,
                  InferenceId::ARRAYS_AEXT_ROW,
                  lemmaExp,
                  ProofRule::ARRAYS_READ_OVER_WRITE);
  ++d_numRowLemmas;
  return true;
}

bool AextArraySolver::checkDisequalities()
{
  bool changed = false;
  NodeManager* nm = nodeManager();

  for (size_t i = 0, sz = d_arrayDisequalities.size(); i < sz; ++i)
  {
    if (d_state.isInConflict())
    {
      break;
    }
    TNode fact = d_arrayDisequalities[i];
    // fact is of the form (not (= a b))
    if (d_witnessDiseqs.contains(fact))
    {
      continue;
    }
    d_witnessDiseqs.insert(fact);

    TNode a = fact[0][0];
    TNode b = fact[0][1];

    // Generate witness skolem k for this disequality
    Node k = SkolemCache::getExtIndexSkolem(nm, fact);

    // Create witness reads
    Node ak = nm->mkNode(Kind::SELECT, a, k);
    Node bk = nm->mkNode(Kind::SELECT, b, k);

    // DisEq lemma: (a != b) => select(a, k) != select(b, k)
    Node eq = ak.eqNode(bk);
    Trace("arrays::aext") << "AextArraySolver::checkDisequalities: " << fact
                          << " => " << eq.notNode() << std::endl;
    d_im.arrayLemma(
        eq.notNode(), InferenceId::ARRAYS_EXT, fact, ProofRule::ARRAYS_EXT);
    ++d_numDisequality;
    changed = true;
  }
  return changed;
}

bool AextArraySolver::collectModelValues(TheoryModel* /*m*/,
                                         const std::set<Node>& /*termSet*/)
{
  // Model construction is delegated to TheoryArrays::collectModelValues,
  // which reads from the EE and termSet (solver-independent).
  return true;
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

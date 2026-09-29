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
                                 DefValMap& defValues,
                                 context::CDO<bool>& sharedTerms)
    : ArraySolver(
          env, state, im, valuation, mayEqualEE, defValues, sharedTerms),
      d_stateGen(context(), 0),
      d_selects(context()),
      d_stores(context()),
      d_arrayDisequalities(context()),
      d_witnessDiseqs(context()),
      d_witnessRepPairCount(context()),
      d_congruenceLemmaCache(context()),
      d_rintro2LemmaCache(context()),
      d_indexSplitCache(userContext()),
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
      d_numCheckSkips(statisticsRegistry().registerInt(
          "theory::arrays::aext::numCheckSkips")),
      d_numPropagationsDown(statisticsRegistry().registerInt(
          "theory::arrays::aext::numPropagationsDown")),
      d_numPropagationsUp(statisticsRegistry().registerInt(
          "theory::arrays::aext::numPropagationsUp")),
      d_numRIntro2Propagations(statisticsRegistry().registerInt(
          "theory::arrays::aext::numRIntro2Propagations"))
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

void AextArraySolver::notifyArrayDisequality(CVC5_UNUSED TNode a,
                                             TNode /*b*/,
                                             TNode reason)
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

  // Skip the check if nothing it reads has changed since the last one that ran
  // to completion. The propagation below is a function of the equality engine
  // and of d_selects / d_stores alone, so it would rebuild the same
  // d_arrayModels and reach the same conflicts. Those conflicts are all either
  // already recorded in a deduplication cache (CongR, RIntro2, index splits) or
  // already witnessed (DisEq), so a repeat run emits nothing new -- at most a
  // duplicate AccessStore lemma, which has no cache of its own.
  //
  // The state is sampled on entry, not on exit: check() itself asserts RIntro2
  // facts, and stamping the post-merge state would claim a complete check at a
  // state we never actually ran on.
  //
  // The generation match establishes that the current state extends the one
  // the last completed check ran on -- no pop has discarded it -- so its plain
  // fingerprint is comparable at all: without it, a sibling branch that
  // asserted a different fact and landed on the same count would match. Given
  // that, equal counts mean nothing was asserted or registered since, and the
  // structures below, which computeCareGraph() reads, describe this state.
  CheckState state{
      d_ee->getNumAssertedEqualities(), d_selects.size(), d_stores.size()};
  if (d_stateGen.get() == d_builtGen && d_builtState == state)
  {
    ++d_numCheckSkips;
    return;
  }

  ++d_numCheckCalls;
  Trace("arrays::aext") << "AextArraySolver::check() with " << d_selects.size()
                        << " selects and " << d_stores.size() << " stores"
                        << std::endl;

  // Clear per-check data structures. Everything here is rebuilt from
  // scratch below, and is only read during this check() and the
  // computeCareGraph() call that follows it.
  d_pendingCarePairs.clear();
  d_pendingCarePairCache.clear();
  d_checkAccessCache.clear();
  d_arrayModels.clear();
  d_builtGen = ++d_genCounter;
  d_builtState = state;

  // RIntro2 theory propagation. This runs before the two maps below are built,
  // because it asserts internal facts: the equalities it derives are between
  // SELECT terms, but congruence turns those into array merges whenever the
  // selects are store values. Building d_parentStores and d_activeArrays first
  // left them keyed on representatives that are no longer representatives, and
  // a missed d_parentStores lookup silently disables RowU -- the direction that
  // costs satisfiability completeness. (Measured before the reorder:
  // regress0/aufbv/fifo32bc06k08 had 15 of 108 checks where RIntro2 moved the
  // equality engine.)
  propagateRIntro2();
  // Both maps below iterate equivalence classes, and EqClassIterator requires
  // a consistent equality engine, so bail out before them if RIntro2 derived a
  // conflict. Nothing is stamped into d_stateGen on this path, so the next
  // check() redoes the work.
  if (d_state.isInConflict())
  {
    return;
  }

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
      if (d_indexSplitCache.insert(split))
      {
        Trace("arrays::aext")
            << "Index split (non-shared): " << split << std::endl;
        d_im.lemma(split.orNode(split.notNode()),
                   InferenceId::ARRAYS_AEXT_INDEX_SPLIT);
      }
    }
  }

  // Only a run that got all the way here without a conflict licenses a skip:
  // an aborted one may have left work undone.
  if (!d_state.isInConflict())
  {
    d_stateGen = d_builtGen;
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

/**
 * Compute the representatives from which RowU is allowed (see the invariant
 * documented on d_activeArrays in the header).
 *
 * The set is: every representative of a STORE term whose equivalence class has
 * more than one member, closed downwards through store bases.
 */
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

#ifdef CVC5_ASSERTIONS
  // Check the structural fact the whole gate rests on: if a store's base is
  // excluded, that store is alone in its class. Everything the invariant on
  // d_activeArrays argues -- that a CongR partner descends instead, that
  // AccessStore needs an index equality Step 4 excludes, that no STORE_ALL is
  // present -- is a case analysis over a singleton parent class, and says
  // nothing once the class has a second member.
  //
  // The seed and the closure above are what establish it, and they are easy
  // to perturb: seeding from something other than "class size > 1", or
  // closing over anything narrower than every STORE in the class, breaks it
  // without breaking any test, and the symptom is a wrong "sat". Assert it
  // directly rather than trusting the reader to re-derive it.
  for (size_t i = 0, sz = d_stores.size(); i < sz; ++i)
  {
    TNode store = d_stores[i];
    if (!d_ee->hasTerm(store))
    {
      continue;
    }
    if (d_activeArrays.count(d_ee->getRepresentative(store[0])))
    {
      continue;
    }
    eq::EqClassIterator eqi(d_ee->getRepresentative(store), d_ee);
    ++eqi;  // skip the store itself
    Assert(eqi.isFinished())
        << "RowU is gated off for the base of " << store
        << ", but that store's class has a second member, " << (*eqi)
        << ". The gate's soundness argument does not cover this.";
  }
#endif
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
  propagateFrom(select, select[0]);
}

void AextArraySolver::propagateFrom(TNode select, TNode start)
{
  TNode index = select[1];
  TNode indexRep = d_ee->getRepresentative(index);
  NodeManager* nm = nodeManager();

  std::vector<TNode> visit;
  visit.push_back(start);

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
          TNode entry1 =
              findPathConditions(select, arrayRep, expVec, &paths[0]);
          TNode entry2 =
              findPathConditions(existing.select, arrayRep, expVec, &paths[1]);
          if (entry1.isNull() || entry2.isNull())
          {
            // Unreachable by the argument on findPathConditions; drop the
            // lemma rather than send one whose guard we cannot produce.
            continue;
          }
          if (index != existing.index)
          {
            expVec.push_back(index.eqNode(existing.index));
          }
          Node exp = nm->mkAnd(expVec);
          Trace("arrays::aext")
              << "CongR: " << exp << " => " << conc << std::endl;
          // Keyed on the whole lemma: the same conclusion may be justified by
          // several distinct path condition sets, and each one has to be sent.
          if (d_congruenceLemmaCache.insert(exp.impNode(conc)))
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
              // The caller-added `entryArray = n` below is strictly stronger
              // than `entryArray = arrayRep`, so skip the latter.
              TNode entryArray = findPathConditions(
                  select, arrayRep, expVec, &paths[0], false);
              if (entryArray.isNull())
              {
                break;
              }
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
            // As in AccessStore: `entryArray = n` below subsumes the rep
            // equality, so do not emit it.
            TNode entryArray =
                findPathConditions(select, arrayRep, expVec, &paths[0], false);
            if (entryArray.isNull())
            {
              break;
            }
            if (entryArray != n)
            {
              expVec.push_back(entryArray.eqNode(static_cast<Node>(n)));
            }
            Node reason = nm->mkAnd(expVec);
            Trace("arrays::aext") << "AccessConstArray: " << reason << " => "
                                  << conc << std::endl;
            d_im.arrayLemma(conc,
                            InferenceId::ARRAYS_AEXT_CONST_ARRAY,
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
                                          std::vector<PathEdge>* pathEdges,
                                          bool linkEntryToTargetRep)
{
  TNode index = select[1];
  TNode indexRep = d_ee->getRepresentative(index);
  TNode startArray = select[0];
  TNode startRep = d_ee->getRepresentative(startArray);
  // conds is appended to, not owned: CongR passes the same vector for both of
  // its paths. Remember where this call's contribution starts so a failure can
  // leave the vector exactly as it found it.
  const size_t numCondsOnEntry = conds.size();

  // Trivial case: already at target.
  if (startRep == targetRep)
  {
    Node entryEq;
    if (startArray != startRep && linkEntryToTargetRep)
    {
      entryEq = startArray.eqNode(static_cast<Node>(startRep));
      conds.push_back(entryEq);
    }
    if (pathEdges)
    {
      pathEdges->push_back({TNode(), false, entryEq, Node(), Node()});
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

  // The BFS explores a superset of what forward propagation reached -- it does
  // not apply the d_activeArrays gate, and the equality engine does not move
  // during the select loop -- so every conflict checkAccess detects has a path
  // here. Should that ever stop holding, do not walk a tree that has no entry
  // for targetRep: the walk below would dereference an end iterator, which
  // Assert does not prevent in a production build. Report the failure instead
  // and let the caller drop the lemma.
  Assert(found) << "findPathConditions: no path from " << startArray
                << " to rep " << targetRep;
  if (!found)
  {
    conds.resize(numCondsOnEntry);
    if (pathEdges)
    {
      pathEdges->clear();
    }
    return TNode();
  }

  // Walk back from targetRep to startRep, extracting conditions.
  TNode cur = targetRep;
  while (true)
  {
    auto it = bfsEdges.find(cur);
    Assert(it != bfsEdges.end());
    const BFSEdge& be = it->second;

    // Each literal pushed below is also recorded on the edge, so the proof
    // converter can recover this edge's conditions without scanning the
    // flattened explanation by position.
    //
    // Only the target's entryEq -- the concrete array this path arrives at,
    // equated to targetRep -- is emitted. An intermediate node's is dead
    // weight: addPathSelectProof never mentions a representative, it threads a
    // concrete select through the chain and builds each CONG premise as
    // curSel[0] = store, which is syntactically this edge's linkEq, because
    // the BFS set entryArray to exactly the array the ROW step lands on. So
    // linkEq alone discharges every intermediate step, and an extra
    // `entryArray = rep` only adds an antecedent the proof never uses --
    // weakening the lemma, and duplicating a conjunct outright whenever it
    // coincides with the next edge's linkEq. The target's is different: it is
    // what convertCongruence's bridge walks to join two paths that entered the
    // same class through different terms.
    if (be.store.isNull())
    {
      Node entryEq;
      if (be.entryArray != cur && cur == targetRep && linkEntryToTargetRep)
      {
        entryEq = be.entryArray.eqNode(static_cast<Node>(cur));
        conds.push_back(entryEq);
      }
      if (pathEdges)
      {
        pathEdges->push_back({TNode(), false, entryEq, Node(), Node()});
      }
      break;
    }

    Node entryEq;
    if (be.entryArray != cur && cur == targetRep && linkEntryToTargetRep)
    {
      entryEq = be.entryArray.eqNode(static_cast<Node>(cur));
      conds.push_back(entryEq);
    }

    auto pit = bfsEdges.find(be.fromRep);
    Assert(pit != bfsEdges.end());
    TNode prevEntry = pit->second.entryArray;

    Node linkEq;
    if (be.isRowU)
    {
      if (prevEntry != be.store[0])
      {
        linkEq = prevEntry.eqNode(be.store[0]);
        conds.push_back(linkEq);
      }
    }
    else
    {
      if (prevEntry != be.store)
      {
        linkEq = prevEntry.eqNode(static_cast<Node>(be.store));
        conds.push_back(linkEq);
      }
    }
    Node indexDiseq = index.eqNode(be.store[1]).notNode();
    conds.push_back(indexDiseq);

    if (pathEdges)
    {
      pathEdges->push_back({be.store, be.isRowU, entryEq, linkEq, indexDiseq});
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
        // Keyed on the conclusion alone, unlike CongR: this inference also
        // asserts eq as an internal fact below, and an equality engine
        // assertion can only be undone by popping the context that this cache
        // lives in. So whenever the cache suppresses a re-derivation, eq still
        // holds; there is nothing for a second guard to add.
        if (!d_rintro2LemmaCache.insert(eq))
        {
          continue;
        }
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
                        InferenceId::ARRAYS_AEXT_RINTRO2,
                        reason,
                        ProofRule::ARRAYS_READ_OVER_WRITE);
        d_im.assertInference(eq,
                             true,
                             InferenceId::ARRAYS_AEXT_RINTRO2,
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

    TNode a = fact[0][0];
    TNode b = fact[0][1];

    // One witness lemma per canonical (rep_a, rep_b) pair is enough. If fact
    // f and an earlier fact f' both have representative pair (r_a, r_b) in
    // the current equality engine state, then f's arrays are equal to f''s,
    // so the index witnessing f' witnesses f as well by congruence. Further
    // lemmas for the same pair are extensionality axioms that differ only
    // modulo congruence, and they cost clause database.
    //
    // This was 30 until it was measured. At 30 the cap never fired at all:
    // over 2,505 SMT-LIB benchmarks (QF_AX, QF_ALIA, QF_AUFLIA, QF_AUFBV,
    // QF_ABV) the highest count any representative pair ever reached was 24,
    // so the code was unreachable and the "caps blowup on larger problems"
    // half of its rationale had never been exercised. Dropping to 1 -- what
    // the coverage argument above actually licenses -- is a wash or better
    // everywhere: no answer changes anywhere, 2383 -> 2384 solved overall,
    // and on QF_ALIA, the only logic where many facts share a pair, 109 ->
    // 113 solved. Restricted to the benchmarks the cap can even affect, it is
    // faster: -24.1s over the 18 such benchmarks in QF_ALIA, -1.9s over the 6
    // in QF_AX+QF_AUFLIA. (Aggregate timings over the full sets are not worth
    // quoting here; run-to-run noise on this harness is ~100s over 1,800
    // benchmarks, far larger than the effect.)
    //
    // Note the count is context-dependent, so it only suppresses witnesses
    // while we remain in the state that makes the argument above valid.
    // Note also that a suppressed fact is deliberately NOT recorded in
    // d_witnessDiseqs: we may have to emit its witness after backtracking,
    // when the covering lemma no longer applies.
    constexpr uint32_t kWitnessCapPerRepPair = 1;
    TNode repA = d_ee->getRepresentative(a);
    TNode repB = d_ee->getRepresentative(b);
    Node repPair = repA < repB ? repA.eqNode(repB) : repB.eqNode(repA);
    auto itc = d_witnessRepPairCount.find(repPair);
    uint32_t count = itc == d_witnessRepPairCount.end() ? 0 : (*itc).second;
    if (count >= kWitnessCapPerRepPair)
    {
      continue;
    }
    d_witnessRepPairCount[repPair] = count + 1;
    d_witnessDiseqs.insert(fact);

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
  //
  // WHY `!areEqual` IS THE RIGHT TEST, AND NOT TOO WEAK. Pushing read n into
  // selects[rep(t[0])] across a store t asserts select(t[0], idx) = n, which
  // needs idx != t[1]. The test below is only "not known equal", which is
  // weaker -- so the question is whether an index pair can still be undecided
  // here.
  //
  // It cannot, for any edge that matters. checkAccess walks the same graph
  // under the same condition (`rep(t[1]) != indexRep` is `!areEqual` on
  // representatives) and requests a split for every edge it takes, via
  // d_pendingCarePairs; by the time a model is built, the SAT solver has
  // decided each of them and the answer is in the equality engine. Three
  // places where the two walks differ, and why none of them opens a gap:
  //
  //  - checkAccess stops at an array where a read with the same index
  //    representative is already recorded (step 1). That other read carries on
  //    from there and requests the same splits. Its index term differs, but
  //    areEqual/areDisequal are representative-level, so it decides the same
  //    question.
  //  - checkAccess gates RowU on d_activeArrays; this walk does not. By the
  //    invariant documented on d_activeArrays, every store class reachable
  //    only through a gated edge is a singleton {s} with s a STORE -- and
  //    TheoryArrays::collectModelValues builds its `arrays` list only from
  //    classes holding a non-STORE term in termSet, so selects[rep(s)] is
  //    never read. Descending back out of such a class reaches rep(s[0]),
  //    which the walk has already visited. The gated region contributes
  //    nothing to the model.
  //  - checkAccess skips a pair whose split rewrites to a constant. Those are
  //    two distinct constants, which the equality engine already knows to be
  //    disequal.
  //
  // Do not "harden" this into areDisequal: that is strictly stronger than the
  // condition checkAccess propagates under, and dropping an edge here does not
  // make the model safer. The read stays pinned on the parent array, whose
  // value is store(base, t[1], v), so leaving the base unpinned at idx makes
  // the two disagree wherever the model picks idx != t[1].

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
  // Native read pairs: all pairs of registered reads whose index is a trigger
  // term. This is AEXT's counterpart of the bucketed sweep that
  // ArraySolverDefault runs over its own read list. AEXT keeps every read in
  // d_selects -- including the virtual reads select(store(a,i,v), i) created
  // by InitW, which are never routed through TheoryArrays::preRegisterSelect
  // -- so we sweep that list directly.
  if (d_sharedTerms)
  {
    size_t sz = d_selects.size();
    for (size_t i = 0; i < sz; ++i)
    {
      TNode r1 = d_selects[i];
      if (!d_ee->hasTerm(r1) || !d_ee->isTriggerTerm(r1[1], THEORY_ARRAYS))
      {
        continue;
      }
      for (size_t j = i + 1; j < sz; ++j)
      {
        TNode r2 = d_selects[j];
        if (!d_ee->hasTerm(r2))
        {
          continue;
        }
        checkPair(r1, r2, addCarePair);
      }
    }
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
  // same array.
  //
  // For each arrayRep we partition reads in d_arrayModels[arrayRep] into:
  //  - native: the read's original array is EE-equal to arrayRep
  //    (i.e., read.select[0] EE-equal to arrayRep)
  //  - propagated: reached arrayRep via a Row step through store chains
  // The d_selects sweep at the top of this method already enumerates all
  // pairs of registered reads, which emits every care pair whose read
  // arrays share a may-equal class. Two native reads at arrayRep are both
  // EE-equal (hence may-equal) to arrayRep, so that sweep already emits
  // their pair. What remains is to cover pairs where at least one side is
  // a propagated read, since such reads can land at an arrayRep that is
  // not EE-equal to the read's original array.
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
  }
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

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

#include <algorithm>
#include <deque>
#include <functional>

#include "expr/array_store_all.h"
#include "expr/node_manager.h"
#include "options/arrays_options.h"
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
      d_incrementalJoins(context()),
      d_lastCheckState(context()),
      d_lastSplitState(context()),
      d_checkAtStandardEffort(userContext(), true),
      d_selects(context()),
      d_stores(context()),
      d_constArrays(context()),
      d_arrayDisequalities(context()),
      d_witnessDiseqs(context()),
      d_witnessRepPairCount(context()),
      d_congruenceLemmaCache(context()),
      d_congruenceGuards(context()),
      d_rintro2LemmaCache(context()),
      d_indexSplitCache(userContext()),
      d_undoMark(context(), 0),
      d_mergeQueue(context()),
      d_disequalityQueue(context()),
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
      d_numCheckRestores(statisticsRegistry().registerInt(
          "theory::arrays::aext::numCheckRestores")),
      d_numUndoRecords(statisticsRegistry().registerInt(
          "theory::arrays::aext::numUndoRecords")),
      d_numDeltaResumes(statisticsRegistry().registerInt(
          "theory::arrays::aext::numDeltaResumes")),
      d_numDeltaRedoReads(statisticsRegistry().registerInt(
          "theory::arrays::aext::numDeltaRedoReads")),
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

namespace {

/**
 * Whether arrays of type t index or hold bit-vectors or floating-point
 * values, directly or through nested arrays.
 */
bool isOverBitVectorsOrFloatingPoint(TypeNode t)
{
  while (t.isArray())
  {
    TypeNode index = t.getArrayIndexType();
    if (index.isBitVector() || index.isFloatingPoint()
        || isOverBitVectorsOrFloatingPoint(index))
    {
      return true;
    }
    t = t.getArrayConstituentType();
  }
  return t.isBitVector() || t.isFloatingPoint();
}

}  // namespace

void AextArraySolver::notifyArrayType(TypeNode arrayType)
{
  if (d_checkAtStandardEffort.get()
      && isOverBitVectorsOrFloatingPoint(arrayType))
  {
    d_checkAtStandardEffort = false;
  }
}

void AextArraySolver::preRegisterSelect(TNode node)
{
  Assert(node.getKind() == Kind::SELECT);
  notifyArrayType(node[0].getType());
  d_selectOrder[node] = d_selects.size();
  d_selects.push_back(node);
}

void AextArraySolver::preRegisterStore(TNode node)
{
  Assert(node.getKind() == Kind::STORE);
  notifyArrayType(node.getType());
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

void AextArraySolver::preRegisterStoreAll(TNode node)
{
  // The shared code in TheoryArrays already sets d_defValues; AEXT only needs
  // to know which class the constant array is in (see updateClassLists).
  notifyArrayType(node.getType());
  d_constArrays.push_back(node);
}

/////////////////////////////////////////////////////////////////////////////
// EQUALITY ENGINE CALLBACKS
/////////////////////////////////////////////////////////////////////////////

void AextArraySolver::eqNotifyMerge(TNode a, TNode b)
{
  d_mergeQueue.push_back(b);
  mergeArraysModelOnly(a, b);
}

void AextArraySolver::eqNotifyMergeNonArray(TNode /*a*/, TNode b)
{
  d_mergeQueue.push_back(b);
}

void AextArraySolver::eqNotifyDisequal(TNode a, TNode b)
{
  d_disequalityQueue.push_back({a, b});
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
  // This runs at every effort level, standard included. Waiting for full
  // effort lets the SAT solver build a complete assignment before any array
  // reasoning prunes it: on QF_AUFLIA/cvc/pp-dmem, a Burch-Dill
  // pipelined-processor proof, that took over 25 times the decisions the
  // default solver needs, which derives its lemmas as facts arrive, and did
  // not finish. What makes checking this often affordable is that a check
  // only applies what changed since the previous one (see applyDelta).
  //
  // Index splits are the exception; see the loop that sends them.
  //
  // So is everything once an array over bit-vectors or floating-point is
  // registered: the check then waits for full effort (see
  // d_checkAtStandardEffort). The bit-vector solver refutes most
  // assignments at full effort, before this check even gets to run, so most
  // of what a standard effort check derives is about assignments that are
  // refuted anyway. It still costs: every lemma registers atoms for the
  // bit-blaster and enlarges the search, and the same lemmas are derived
  // again after every backtrack. On QF_ABV/dwp_formulas
  // try3_sameret_functions_dwp_sha512sum.sha512_init_ctx, solved in 1s with
  // 3 checks and 4 CongR lemmas at full effort, checking at standard effort
  // sent 1,009 CongR lemmas in the first 15s and timed out at 1200s. On a
  // QF_ABVFP KLEE query that needs 115 in total, it sent 13,506 in the first
  // 15s, 97% of them again after a backtrack had cleared the lemma cache.
  // QF_ABV/platania is the one family that gains from standard effort (+23
  // solved at 1200s), and that does not make up for the rest.
  if (d_state.isInConflict())
  {
    return;
  }
  bool fullEffort = Theory::fullEffort(level);
  if (!fullEffort && !d_checkAtStandardEffort.get())
  {
    return;
  }

  // Take the propagation state back to what the last check that completed on
  // the current context path left. Whatever was recorded after that belongs
  // to checks a pop has since undone, or to one a conflict cut short.
  undoToMark();

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
  // undoToMark has just taken the structures below, which computeCareGraph()
  // reads, back to the result of the check that fingerprint belongs to, so on
  // a match they describe this state.
  //
  // A full effort check still has index splits to send in that state if the
  // check that ran on it was at standard effort.
  CheckState state{
      d_ee->getNumAssertedEqualities(), d_selects.size(), d_stores.size()};
  if (d_lastCheckState.get() == state)
  {
    if (fullEffort)
    {
      sendIndexSplits(state);
    }
    ++d_numCheckSkips;
    return;
  }

  ++d_numCheckCalls;
  Trace("arrays::aext") << "AextArraySolver::check() with " << d_selects.size()
                        << " selects and " << d_stores.size() << " stores"
                        << std::endl;
  d_gateOpenedNow.clear();
  d_undoCounters.push_back({d_numSelectsDone,
                            d_numStoresDone,
                            d_numMergesDone,
                            d_listSelectsDone,
                            d_listStoresDone,
                            d_listConstArraysDone,
                            d_listMergesDone,
                            d_listDisequalitiesDone});
  d_undoLog.push_back({UndoRecord::COUNTERS, Node(), Node(), Node()});

  // RIntro2 theory propagation. This runs before the class lists and the gate
  // below are brought up to date, because it asserts internal facts: the
  // equalities it derives are between SELECT terms, but congruence turns
  // those into array merges whenever the selects are store values. Updating
  // the lists first left them keyed on representatives that are no longer
  // representatives, and a missed parent lookup silently disables RowU -- the
  // direction that costs satisfiability completeness. (Measured before the
  // reorder: regress0/aufbv/fifo32bc06k08 had 15 of 108 checks where RIntro2
  // moved the equality engine.) For the same reason it runs before
  // applyDelta: the merges it causes are queued like any other, and handled
  // with them.
  //
  // It only looks at what changed since the last check (see
  // updateClassLists), and the facts it asserts are changes too, so it runs
  // interleaved with bringing the class lists up to date until neither has
  // anything left to do.
  do
  {
    updateClassLists();
    propagateRIntro2();
    // Everything below assumes a consistent equality engine --
    // EqClassIterator, for one, requires it -- so bail out if RIntro2
    // derived a conflict. Nothing is stamped on this path, so the next
    // check() undoes what this one recorded and redoes it.
    if (d_state.isInConflict())
    {
      return;
    }
  } while (d_listMergesDone < d_mergeQueue.size());
  checkGatePrecondition();

  applyDelta();
  if (d_state.isInConflict())
  {
    return;
  }

  // Handle disequalities (DisEq rule)
  checkDisequalities();

  if (fullEffort)
  {
    sendIndexSplits(state);
  }

  // Only a run that got all the way here without a conflict licenses a skip,
  // or keeps what it recorded: an aborted one may have left work undone.
  if (!d_state.isInConflict())
  {
    d_undoMark = d_undoLog.size();
    d_lastCheckState = state;
    if (options().arrays.arraysAextCheckIncremental)
    {
      checkIncrementalState();
      checkRIntro2Complete();
    }
  }

  Trace("arrays::aext") << "AextArraySolver::check() done" << std::endl;
}

void AextArraySolver::addSlot(TNode arrayRep, TNode indexRep, TNode select)
{
  d_arrayModels[arrayRep][indexRep] = {select, select[1]};
  if (!d_inShadowRebuild)
  {
    d_undoLog.push_back(
        {UndoRecord::SLOT_ADDED, arrayRep, indexRep, Node()});
  }
}

void AextArraySolver::removeSlot(TNode arrayRep, TNode indexRep)
{
  auto it = d_arrayModels.find(arrayRep);
  Assert(it != d_arrayModels.end());
  auto jt = it->second.find(indexRep);
  Assert(jt != it->second.end());
  if (!d_inShadowRebuild)
  {
    d_undoLog.push_back(
        {UndoRecord::SLOT_REMOVED, arrayRep, indexRep, jt->second.select});
  }
  it->second.erase(jt);
  if (it->second.empty())
  {
    d_arrayModels.erase(it);
  }
}

bool AextArraySolver::markWalked(TNode select)
{
  if (!d_checkAccessCache.insert(select).second)
  {
    return false;
  }
  if (!d_inShadowRebuild)
  {
    d_undoLog.push_back(
        {UndoRecord::WALKED_ADDED, select, Node(), Node()});
  }
  return true;
}

bool AextArraySolver::unmarkWalked(TNode select)
{
  if (d_checkAccessCache.erase(select) == 0)
  {
    return false;
  }
  if (!d_inShadowRebuild)
  {
    d_undoLog.push_back(
        {UndoRecord::WALKED_REMOVED, select, Node(), Node()});
  }
  return true;
}

std::vector<std::pair<TNode, TNode>> AextArraySolver::pendingIndexPairs()
{
  std::vector<std::pair<TNode, TNode>> pairs;
  std::unordered_set<std::pair<TNode, TNode>, PairHashFunction<TNode, TNode>>
      seen;
  auto consider = [&](TNode index, TNode storeIndex) {
    if (d_ee->areEqual(index, storeIndex)
        || d_ee->areDisequal(index, storeIndex, false))
    {
      return;
    }
    if (seen.emplace(index, storeIndex).second)
    {
      pairs.emplace_back(index, storeIndex);
    }
  };
  for (const auto& [arrayRep, model] : d_arrayModels)
  {
    const ClassLists& lists = classListsOf(arrayRep);
    bool active = d_activeArrays.count(arrayRep);
    for (const auto& [indexRep, read] : model)
    {
      for (TNode n : lists.d_stores)
      {
        consider(read.index, n[1]);
      }
      if (active)
      {
        for (TNode store : lists.d_parents)
        {
          consider(read.index, store[1]);
        }
      }
    }
  }
  return pairs;
}

void AextArraySolver::sendIndexSplits(const CheckState& state)
{
  // Index splits: for undecided pairs where at least one index is not a
  // trigger term, send an explicit split lemma, since the care graph cannot
  // handle them.
  //
  // Only at full effort. A split exists to get an index pair decided before
  // the SAT solver declares a model, so nothing is lost by waiting for one,
  // and sending it earlier registers an index equality atom for every pair
  // any read crossed on the way to some partial assignment. With bit-vector
  // indices each such atom is bit-blasted: on QF_ABV/dwp_formulas, splits at
  // standard effort took 11 instances that solve in under 4s to timeouts,
  // one of them from 17,596 decisions against 106. Measured over 2,505
  // SMT-LIB benchmarks at 30s, waiting solves 21 more (2376 -> 2397),
  // mostly QF_ABV (366 -> 378) and QF_ALIA (117 -> 125), with no losses
  // beyond noise.
  if (d_lastSplitState.get() == state)
  {
    return;
  }
  for (const auto& [t1, t2] : pendingIndexPairs())
  {
    // Trigger-term pairs are handled via the care graph.
    if (d_ee->isTriggerTerm(t1, THEORY_ARRAYS)
        && d_ee->isTriggerTerm(t2, THEORY_ARRAYS))
    {
      continue;
    }
    Node split = t1.eqNode(t2);
    if (d_indexSplitCache.insert(split))
    {
      Trace("arrays::aext") << "Index split (non-shared): " << split
                            << std::endl;
      d_im.lemma(split.orNode(split.notNode()),
                 InferenceId::ARRAYS_AEXT_INDEX_SPLIT);
    }
  }
  d_lastSplitState = state;
}

void AextArraySolver::undoToMark()
{
  size_t mark = d_undoMark.get();
  Assert(mark <= d_undoLog.size());
  if (mark < d_undoLog.size())
  {
    ++d_numCheckRestores;
    d_numUndoRecords += d_undoLog.size() - mark;
  }
  while (d_undoLog.size() > mark)
  {
    const UndoRecord& u = d_undoLog.back();
    switch (u.d_kind)
    {
      case UndoRecord::SLOT_ADDED:
      {
        auto it = d_arrayModels.find(u.d_a);
        Assert(it != d_arrayModels.end() && it->second.count(u.d_b));
        it->second.erase(u.d_b);
        if (it->second.empty())
        {
          d_arrayModels.erase(it);
        }
        break;
      }
      case UndoRecord::SLOT_REMOVED:
        Assert(!d_arrayModels.count(u.d_a)
               || !d_arrayModels[u.d_a].count(u.d_b));
        d_arrayModels[u.d_a][u.d_b] = {u.d_c, u.d_c[1]};
        break;
      case UndoRecord::WALKED_ADDED: d_checkAccessCache.erase(u.d_a); break;
      case UndoRecord::WALKED_REMOVED: d_checkAccessCache.insert(u.d_a); break;
      case UndoRecord::GATE_OPENED: d_activeArrays.erase(u.d_a); break;
      case UndoRecord::STORE_LISTED:
        d_classLists[u.d_a].d_stores.pop_back();
        break;
      case UndoRecord::CONST_ARRAY_LISTED:
        d_classLists[u.d_a].d_constArrays.pop_back();
        break;
      case UndoRecord::PARENT_LISTED:
        d_classLists[u.d_a].d_parents.pop_back();
        break;
      case UndoRecord::READ_LISTED:
        d_classLists[u.d_a].d_reads.pop_back();
        break;
      case UndoRecord::INDEX_READ_LISTED:
        d_classLists[u.d_a].d_indexReads.pop_back();
        break;
      case UndoRecord::INDEX_STORE_LISTED:
        d_classLists[u.d_a].d_indexStores.pop_back();
        break;
      case UndoRecord::LISTS_MOVED:
      {
        // The moved elements are the last ones of each list of d_b: anything
        // appended after the move has been undone already.
        const UndoMove& m = d_undoMoves.back();
        ClassLists& into = d_classLists[u.d_b];
        ClassLists& from = d_classLists[u.d_a];
        auto moveBack = [](std::vector<TNode>& src,
                           std::vector<TNode>& dst,
                           size_t n) {
          Assert(src.size() >= n && dst.empty());
          dst.assign(src.end() - n, src.end());
          src.resize(src.size() - n);
        };
        moveBack(into.d_stores, from.d_stores, m.d_stores);
        moveBack(into.d_constArrays, from.d_constArrays, m.d_constArrays);
        moveBack(into.d_parents, from.d_parents, m.d_parents);
        moveBack(into.d_reads, from.d_reads, m.d_reads);
        moveBack(into.d_indexReads, from.d_indexReads, m.d_indexReads);
        moveBack(into.d_indexStores, from.d_indexStores, m.d_indexStores);
        d_undoMoves.pop_back();
        break;
      }
      case UndoRecord::COUNTERS:
      {
        const UndoCounters& c = d_undoCounters.back();
        d_numSelectsDone = c.d_selects;
        d_numStoresDone = c.d_stores;
        d_numMergesDone = c.d_merges;
        d_listSelectsDone = c.d_listSelects;
        d_listStoresDone = c.d_listStores;
        d_listConstArraysDone = c.d_listConstArrays;
        d_listMergesDone = c.d_listMerges;
        d_listDisequalitiesDone = c.d_listDisequalities;
        d_undoCounters.pop_back();
        break;
      }
    }
    d_undoLog.pop_back();
  }
}

void AextArraySolver::applyDelta()
{
  // The losers of the merges since the last completed check on this path.
  std::vector<Node> losers;
  for (size_t sz = d_mergeQueue.size(); d_numMergesDone < sz;
       ++d_numMergesDone)
  {
    losers.push_back(d_mergeQueue[d_numMergesDone]);
  }

  // Every class a queued merge touched, by its current representative. The
  // queue only holds merges made on the current path, so their terms are
  // still in the equality engine.
  std::unordered_set<TNode> merged;
  for (const Node& b : losers)
  {
    Assert(d_ee->hasTerm(b));
    merged.insert(d_ee->getRepresentative(b));
  }

  // Index merges. They are the one change that can invalidate what is
  // recorded: an edge a read crossed closes once its store index joins the
  // read's index class, and the read has then no path to where it went next.
  // Only reads whose index class merged are affected -- every edge condition
  // compares a store index against the read's own index class, which for any
  // other read is still a different class -- so drop everything those reads
  // recorded and walk them again. Dropping an entry that another read stopped
  // at is fine: that read had the same index representative, so it is walked
  // again too.
  std::vector<TNode> redo;
  for (TNode m : merged)
  {
    for (TNode sel : classListsOf(m).d_indexReads)
    {
      if (unmarkWalked(sel))
      {
        redo.push_back(sel);
      }
    }
  }
  // Walk them again in the order they were registered, as a walk from
  // scratch would: which read gets to a slot first decides which is recorded
  // there, and so which lemmas are sent. The order of the index lists, which
  // is the order merges concatenated them in, costs a fifth more time on
  // QF_ABV/dwp_formulas.
  std::sort(redo.begin(), redo.end(), [this](TNode a, TNode b) {
    return d_selectOrder.at(a) < d_selectOrder.at(b);
  });
  if (!redo.empty())
  {
    std::vector<std::pair<TNode, TNode>> drop;
    for (const auto& [arrayRep, model] : d_arrayModels)
    {
      for (const auto& [indexRep, read] : model)
      {
        if (merged.count(d_ee->getRepresentative(read.index)))
        {
          drop.emplace_back(arrayRep, indexRep);
        }
      }
    }
    for (const auto& [arrayRep, indexRep] : drop)
    {
      removeSlot(arrayRep, indexRep);
    }
  }
  d_numDeltaRedoReads += redo.size();

  // Array merges. Move what was recorded at the losing representative to the
  // winning one; where both hold a read at the same index class, they have
  // just met, so check CongR between them and keep one. Every entry left keyed
  // on an index representative is still keyed on a representative: any index
  // class that merged was dropped above.
  std::unordered_set<TNode> dirty;
  for (const Node& b : losers)
  {
    if (!b.getType().isArray())
    {
      continue;
    }
    TNode r = d_ee->getRepresentative(b);
    dirty.insert(r);
    auto it = d_arrayModels.find(b);
    if (r == b || it == d_arrayModels.end())
    {
      continue;
    }
    std::vector<PropagatedRead> moved;
    std::vector<TNode> keys;
    for (const auto& [k, read] : it->second)
    {
      keys.push_back(k);
      moved.push_back(read);
    }
    for (size_t i = 0, n = keys.size(); i < n; ++i)
    {
      removeSlot(b, keys[i]);
      auto rit = d_arrayModels.find(r);
      if (rit != d_arrayModels.end())
      {
        auto jt = rit->second.find(keys[i]);
        if (jt != rit->second.end())
        {
          checkCongruence(moved[i], jt->second, r);
          continue;
        }
      }
      addSlot(r, keys[i], moved[i].select);
    }
  }

  // New stores. A store is a new RowD edge and AccessStore target at its own
  // class, and a new RowU edge out of its base's class.
  for (size_t sz = d_stores.size(); d_numStoresDone < sz; ++d_numStoresDone)
  {
    TNode store = d_stores[d_numStoresDone];
    if (d_ee->hasTerm(store))
    {
      dirty.insert(d_ee->getRepresentative(store));
      dirty.insert(d_ee->getRepresentative(store[0]));
    }
  }

  // The RowU gate only opens along a context path. A class it has opened at
  // since the last check has new RowU edges.
  for (TNode a : d_gateOpenedNow)
  {
    dirty.insert(d_ee->getRepresentative(a));
  }
  d_gateOpenedNow.clear();

  // Resume every read recorded at a changed class from there: it may now meet
  // stores, a constant array or parents that were not in its class, and edges
  // out of that class may have opened. Collect them first, since resuming
  // records more.
  std::vector<std::pair<TNode, TNode>> resume;
  for (TNode r : dirty)
  {
    auto it = d_arrayModels.find(r);
    if (it != d_arrayModels.end())
    {
      for (const auto& [k, read] : it->second)
      {
        resume.emplace_back(read.select, r);
      }
    }
  }
  d_numDeltaResumes += resume.size();
  for (const auto& [sel, r] : resume)
  {
    if (d_state.isInConflict())
    {
      return;
    }
    propagateFrom(sel, r, true);
  }

  // Finally the reads dropped above, and the reads registered since.
  for (TNode sel : redo)
  {
    if (d_state.isInConflict())
    {
      return;
    }
    checkAccess(sel);
  }
  for (size_t sz = d_selects.size(); d_numSelectsDone < sz; ++d_numSelectsDone)
  {
    if (d_state.isInConflict())
    {
      return;
    }
    checkAccess(d_selects[d_numSelectsDone]);
  }
}

void AextArraySolver::recordJoin(TNode t1, TNode t2, TNode guard)
{
  if (options().arrays.arraysAextCheckIncremental)
  {
    d_incrementalJoins.push_back(
        nodeManager()->mkNode(Kind::SEXPR, {t1, t2, guard}));
  }
}

bool AextArraySolver::isGuardFalsified(TNode guard) const
{
  auto falsified = [&](TNode lit) {
    bool pol = lit.getKind() != Kind::NOT;
    TNode atom = pol ? lit : lit[0];
    if (atom.getKind() != Kind::EQUAL || !d_ee->hasTerm(atom[0])
        || !d_ee->hasTerm(atom[1]))
    {
      return false;
    }
    return pol ? d_ee->areDisequal(atom[0], atom[1], false)
               : d_ee->areEqual(atom[0], atom[1]);
  };
  if (guard.getKind() == Kind::AND)
  {
    for (TNode lit : guard)
    {
      if (falsified(lit))
      {
        return true;
      }
    }
    return false;
  }
  return !guard.isConst() && falsified(guard);
}

void AextArraySolver::checkIncrementalState()
{
  // Rebuild into fresh structures, with lemmas replaced by recording what the
  // rebuild would have had to justify, and put the incremental ones back.
  auto models = std::move(d_arrayModels);
  auto accessCache = std::move(d_checkAccessCache);
  d_arrayModels.clear();
  d_checkAccessCache.clear();
  d_shadowObligations.clear();
  d_inShadowRebuild = true;
  for (size_t i = 0; i < d_numSelectsDone; ++i)
  {
    checkAccess(d_selects[i]);
  }
  d_inShadowRebuild = false;
  std::swap(models, d_arrayModels);
  std::swap(accessCache, d_checkAccessCache);
  // From here on, `models` is the rebuilt one.

  // Two terms are joined if they are equal, or if a lemma equating them was
  // sent on this path whose guard nothing has falsified since: until the SAT
  // solver falsifies a guard literal it cannot avoid the conclusion, and
  // falsifying an index disequality is an index merge, which the incremental
  // check reacts to. Terms outside the equality engine (a constant array's
  // default value) stand for themselves.
  std::unordered_map<Node, Node> parent;
  std::function<Node(Node)> find = [&](Node x) -> Node {
    if (d_ee->hasTerm(x))
    {
      x = d_ee->getRepresentative(x);
    }
    auto it = parent.find(x);
    if (it == parent.end() || it->second == x)
    {
      return x;
    }
    Node root = find(it->second);
    parent[x] = root;
    return root;
  };
  for (const Node& join : d_incrementalJoins)
  {
    if (!isGuardFalsified(join[2]))
    {
      Node r1 = find(join[0]);
      Node r2 = find(join[1]);
      if (r1 != r2)
      {
        parent[r1] = r2;
      }
    }
  }

  // Everything the rebuild derived, the incremental state reaches too: the
  // same slots and the same terms joined. (The undecided index pairs are
  // derived from the slots, so equal slots give equal pairs.)
  for (const auto& [t1, t2] : d_shadowObligations)
  {
    AlwaysAssert(find(t1) == find(t2))
        << "incremental AEXT check: the rebuild needs " << t1 << " = " << t2
        << ", which no live lemma provides";
  }
  auto slotCount = [](const auto& m) {
    size_t n = 0;
    for (const auto& [a, model] : m)
    {
      n += model.size();
    }
    return n;
  };
  AlwaysAssert(slotCount(models) == slotCount(d_arrayModels))
      << "incremental AEXT check: " << slotCount(d_arrayModels)
      << " slots, the rebuild has " << slotCount(models);
  for (const auto& [arrayRep, model] : models)
  {
    auto it = d_arrayModels.find(arrayRep);
    for (const auto& [indexRep, read] : model)
    {
      AlwaysAssert(it != d_arrayModels.end() && it->second.count(indexRep))
          << "incremental AEXT check: the rebuild records " << read.select
          << " at " << arrayRep << ", where nothing is recorded";
      TNode inc = it->second.at(indexRep).select;
      AlwaysAssert(find(inc) == find(read.select))
          << "incremental AEXT check: " << inc << " and " << read.select
          << " share a slot at " << arrayRep << " but are not joined";
    }
  }
  Trace("arrays::aext") << "incremental state agrees with a rebuild ("
                        << slotCount(models) << " slots)" << std::endl;
}

const AextArraySolver::ClassLists& AextArraySolver::classListsOf(
    TNode rep) const
{
  static const ClassLists s_none;
  auto it = d_classLists.find(rep);
  return it == d_classLists.end() ? s_none : it->second;
}

void AextArraySolver::addToClassList(TNode rep,
                                     UndoRecord::Kind which,
                                     TNode term)
{
  ClassLists& lists = d_classLists[rep];
  switch (which)
  {
    case UndoRecord::STORE_LISTED: lists.d_stores.push_back(term); break;
    case UndoRecord::CONST_ARRAY_LISTED:
      lists.d_constArrays.push_back(term);
      break;
    case UndoRecord::PARENT_LISTED: lists.d_parents.push_back(term); break;
    case UndoRecord::READ_LISTED: lists.d_reads.push_back(term); break;
    case UndoRecord::INDEX_READ_LISTED:
      lists.d_indexReads.push_back(term);
      break;
    case UndoRecord::INDEX_STORE_LISTED:
      lists.d_indexStores.push_back(term);
      break;
    default: Unreachable();
  }
  d_undoLog.push_back({which, rep, Node(), Node()});
}

void AextArraySolver::updateClassLists()
{
  // Along with the lists, collect the RIntro2 instances that the changes
  // applied here may have made true (see propagateRIntro2). An instance is a
  // store s, a read rN whose array is in the class of s and a read rC whose
  // array is in the class of s[0], at one index class J; each change below
  // names the stores whose instances it touches, and the index class they
  // are touched at, or all of them.
  auto instances = [&](TNode store, TNode indexRep) {
    if (d_ri2Queued.emplace(store, indexRep).second)
    {
      d_ri2Todo.emplace_back(store, indexRep);
    }
  };
  // Every store with an end in the class of arrayRep: it is in it, or its
  // base is.
  auto instancesAt = [&](TNode arrayRep, TNode indexRep) {
    const ClassLists& lists = classListsOf(arrayRep);
    for (TNode s : lists.d_stores)
    {
      instances(s, indexRep);
    }
    for (TNode s : lists.d_parents)
    {
      instances(s, indexRep);
    }
  };

  // Terms registered since. Each goes to the lists of the classes it is in
  // now, so it does not matter whether a merge queued below moved one.
  for (size_t sz = d_stores.size(); d_listStoresDone < sz; ++d_listStoresDone)
  {
    TNode store = d_stores[d_listStoresDone];
    if (d_ee->hasTerm(store))
    {
      addToClassList(
          d_ee->getRepresentative(store), UndoRecord::STORE_LISTED, store);
      addToClassList(
          d_ee->getRepresentative(store[0]), UndoRecord::PARENT_LISTED, store);
      addToClassList(d_ee->getRepresentative(store[1]),
                     UndoRecord::INDEX_STORE_LISTED,
                     store);
      instances(store, TNode());
      // A new store is alone in its class until a merge (queued below, if
      // any) says otherwise, so it seeds nothing; but if its class is
      // already one the gate is open at, the gate opens at its base too.
      if (d_activeArrays.count(d_ee->getRepresentative(store)))
      {
        openGate(d_ee->getRepresentative(store[0]));
      }
    }
  }
  for (size_t sz = d_constArrays.size(); d_listConstArraysDone < sz;
       ++d_listConstArraysDone)
  {
    TNode c = d_constArrays[d_listConstArraysDone];
    if (d_ee->hasTerm(c))
    {
      addToClassList(
          d_ee->getRepresentative(c), UndoRecord::CONST_ARRAY_LISTED, c);
    }
  }
  for (size_t sz = d_selects.size(); d_listSelectsDone < sz;
       ++d_listSelectsDone)
  {
    TNode read = d_selects[d_listSelectsDone];
    if (d_ee->hasTerm(read))
    {
      TNode arrayRep = d_ee->getRepresentative(read[0]);
      TNode indexRep = d_ee->getRepresentative(read[1]);
      addToClassList(arrayRep, UndoRecord::READ_LISTED, read);
      addToClassList(indexRep, UndoRecord::INDEX_READ_LISTED, read);
      instancesAt(arrayRep, indexRep);
    }
  }
  // Merges since: the lists of a class that lost go to the class it joined,
  // which is its representative now even if that has merged further.
  for (size_t sz = d_mergeQueue.size(); d_listMergesDone < sz;
       ++d_listMergesDone)
  {
    TNode b = d_mergeQueue[d_listMergesDone];
    TNode r = d_ee->getRepresentative(b);
    if (r == b)
    {
      continue;
    }
    auto it = d_classLists.find(b);
    const ClassLists& from = classListsOf(b);
    const ClassLists& into = classListsOf(r);
    // RIntro2 instances with a store on one side of the merge and a read on
    // the other are new. With the loser's stores, that is all their
    // instances; with the winner's, those at the index classes of the
    // loser's reads.
    for (TNode s : from.d_stores)
    {
      instances(s, TNode());
    }
    for (TNode s : from.d_parents)
    {
      instances(s, TNode());
    }
    if (!from.d_reads.empty())
    {
      std::unordered_set<TNode> indexReps;
      for (TNode read : from.d_reads)
      {
        indexReps.insert(d_ee->getRepresentative(read[1]));
      }
      for (TNode j : indexReps)
      {
        for (TNode s : into.d_stores)
        {
          instances(s, j);
        }
        for (TNode s : into.d_parents)
        {
          instances(s, j);
        }
      }
    }
    // As an index class: every read and every store indexed in the merged
    // class, on either side, is at an index class that may now be separated
    // from ones it was not separated from before -- the other side's
    // disequalities, or a constant the other side brings, now apply to it --
    // and the loser's reads also share an index class with the winner's.
    // That holds even if nothing is indexed in the loser's class: a
    // disequality with any of its members is enough.
    for (const std::vector<TNode>* reads :
         {&from.d_indexReads, &into.d_indexReads})
    {
      for (TNode read : *reads)
      {
        instancesAt(d_ee->getRepresentative(read[0]), r);
      }
    }
    for (const std::vector<TNode>* stores :
         {&from.d_indexStores, &into.d_indexStores})
    {
      for (TNode s : *stores)
      {
        instances(s, TNode());
      }
    }
    std::vector<TNode> movedStores = from.d_stores;
    if (it != d_classLists.end())
    {
      ClassLists moved = std::move(it->second);
      d_classLists.erase(it);
      ClassLists& dst = d_classLists[r];
      d_undoMoves.push_back({moved.d_stores.size(),
                             moved.d_constArrays.size(),
                             moved.d_parents.size(),
                             moved.d_reads.size(),
                             moved.d_indexReads.size(),
                             moved.d_indexStores.size()});
      auto append = [](std::vector<TNode>& d, const std::vector<TNode>& src) {
        d.insert(d.end(), src.begin(), src.end());
      };
      append(dst.d_stores, moved.d_stores);
      append(dst.d_constArrays, moved.d_constArrays);
      append(dst.d_parents, moved.d_parents);
      append(dst.d_reads, moved.d_reads);
      append(dst.d_indexReads, moved.d_indexReads);
      append(dst.d_indexStores, moved.d_indexStores);
      d_undoLog.push_back({UndoRecord::LISTS_MOVED, b, r, Node()});
    }
    if (b.getType().isArray())
    {
      updateGateOnMerge(b, r, movedStores);
    }
  }
  // Disequalities since, for the stores indexed on either side.
  for (size_t sz = d_disequalityQueue.size(); d_listDisequalitiesDone < sz;
       ++d_listDisequalitiesDone)
  {
    const auto& [a, b] = d_disequalityQueue[d_listDisequalitiesDone];
    TNode ra = d_ee->getRepresentative(a);
    TNode rb = d_ee->getRepresentative(b);
    for (TNode s : classListsOf(ra).d_indexStores)
    {
      instances(s, rb);
    }
    for (TNode s : classListsOf(rb).d_indexStores)
    {
      instances(s, ra);
    }
  }
}

void AextArraySolver::openGate(TNode arrayRep)
{
  // The gate's closure: open at a class, it is open at the base of every
  // store in it.
  std::vector<TNode> worklist{arrayRep};
  while (!worklist.empty())
  {
    TNode rep = worklist.back();
    worklist.pop_back();
    if (!d_activeArrays.insert(rep).second)
    {
      continue;
    }
    d_undoLog.push_back({UndoRecord::GATE_OPENED, rep, Node(), Node()});
    d_gateOpenedNow.push_back(rep);
    for (TNode n : classListsOf(rep).d_stores)
    {
      worklist.push_back(d_ee->getRepresentative(n[0]));
    }
  }
}

void AextArraySolver::updateGateOnMerge(TNode loser,
                                        TNode winner,
                                        const std::vector<TNode>& movedStores)
{
  // The merged class contains the loser's, so wherever the gate was open for
  // the loser's class it is for the merged one. The merged class has more
  // than one member, so if it holds a store it seeds the gate. And if the
  // gate is open there, it is open at the bases of the stores that joined.
  if (d_activeArrays.count(winner))
  {
    for (TNode n : movedStores)
    {
      openGate(d_ee->getRepresentative(n[0]));
    }
  }
  else if (d_activeArrays.count(loser)
           || !classListsOf(winner).d_stores.empty())
  {
    openGate(winner);
  }
}

void AextArraySolver::checkGatePrecondition()
{
#ifdef CVC5_ASSERTIONS
  // Check the structural fact the whole gate rests on: if a store's base is
  // excluded, that store is alone in its class. Everything the invariant on
  // d_activeArrays argues -- that a CongR partner descends instead, that
  // AccessStore needs an index equality Step 4 excludes, that no STORE_ALL is
  // present -- is a case analysis over a singleton parent class, and says
  // nothing once the class has a second member.
  //
  // The seed and the closure in openGate and updateGateOnMerge are what
  // establish it, and they are easy to perturb: seeding from something other
  // than "class size > 1", or closing over anything narrower than every
  // STORE in the class, breaks it without breaking any test, and the symptom
  // is a wrong "sat". Assert it directly rather than trusting the reader to
  // re-derive it.
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

  if (!markWalked(select))
  {
    return;
  }
  if (!d_ee->hasTerm(select))
  {
    return;
  }
  propagateFrom(select, select[0]);
}

void AextArraySolver::checkCongruence(const PropagatedRead& arriving,
                                      const PropagatedRead& existing,
                                      TNode arrayRep)
{
  if (d_ee->areEqual(arriving.select, existing.select))
  {
    return;
  }
  if (d_inShadowRebuild)
  {
    d_shadowObligations.emplace_back(arriving.select, existing.select);
    return;
  }
  // The two may have met before on this path, and the lemma sent then still
  // forces them equal as long as nothing has falsified its guard: the SAT
  // solver cannot avoid the conclusion without assigning a guard literal
  // false, and the only way to do that without a conflict is to merge an
  // index class into one a path edge's store index is in -- an index merge,
  // after which both reads are walked again and meet afresh. Meeting again
  // through a different path would otherwise send a second lemma with a
  // different guard each time, which resuming reads at merged classes does
  // constantly.
  Node pairKey = arriving.select < existing.select
                     ? arriving.select.eqNode(existing.select)
                     : existing.select.eqNode(arriving.select);
  auto pit = d_congruenceGuards.find(pairKey);
  if (pit != d_congruenceGuards.end() && !isGuardFalsified((*pit).second))
  {
    return;
  }
  Node conc = arriving.select.eqNode(existing.select);
  std::vector<Node> expVec;
  std::vector<std::vector<PathEdge>> paths(2);
  TNode entry1 =
      findPathConditions(arriving.select, arrayRep, expVec, &paths[0]);
  TNode entry2 =
      findPathConditions(existing.select, arrayRep, expVec, &paths[1]);
  if (entry1.isNull() || entry2.isNull())
  {
    // Unreachable by the argument on findPathConditions; drop the lemma
    // rather than send one whose guard we cannot produce.
    return;
  }
  if (arriving.index != existing.index)
  {
    expVec.push_back(arriving.index.eqNode(existing.index));
  }
  Node exp = nodeManager()->mkAnd(expVec);
  Trace("arrays::aext") << "CongR: " << exp << " => " << conc << std::endl;
  recordJoin(arriving.select, existing.select, exp);
  d_congruenceGuards[pairKey] = exp;
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

void AextArraySolver::propagateFrom(TNode select,
                                    TNode start,
                                    bool recordedAtStart)
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

    // Step 1: Record this read and check for congruence (CongR). A read
    // resumed where it is already recorded skips this for its own entry.
    if (recordedAtStart)
    {
      recordedAtStart = false;
      Assert(d_arrayModels.count(arrayRep)
             && d_arrayModels[arrayRep].count(indexRep)
             && d_arrayModels[arrayRep][indexRep].select == select)
          << "resuming " << select << " where it is not recorded";
    }
    else
    {
      auto& model = d_arrayModels[arrayRep];
      auto it = model.find(indexRep);
      if (it != model.end())
      {
        checkCongruence({select, index}, it->second, arrayRep);
        continue;
      }
      addSlot(arrayRep, indexRep, select);

      // Read-read care pairs between trigger-term indices are emitted from
      // computeCareGraph() in a single pass over d_arrayModels, to avoid
      // O(N^2) work per propagation step at arrays with many reads.
    }

    const ClassLists& lists = classListsOf(arrayRep);

    // Step 2: Check for AccessStore (matching index by representative).
    for (TNode n : lists.d_stores)
    {
      if (d_ee->getRepresentative(n[1]) != indexRep)
      {
        continue;
      }
      if (!d_ee->areEqual(select, n[2]))
      {
        if (d_inShadowRebuild)
        {
          d_shadowObligations.emplace_back(select, n[2]);
          break;
        }
        Node conc = select.eqNode(n[2]);
        std::vector<Node> expVec;
        std::vector<std::vector<PathEdge>> paths(1);
        // The caller-added `entryArray = n` below is strictly stronger than
        // `entryArray = arrayRep`, so skip the latter.
        TNode entryArray =
            findPathConditions(select, arrayRep, expVec, &paths[0], false);
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
        recordJoin(select, n[2], reason);
        d_im.arrayLemma(conc,
                        InferenceId::ARRAYS_AEXT_ROW,
                        reason,
                        ProofRule::ARRAYS_READ_OVER_WRITE,
                        std::move(paths));
        ++d_numAccessStoreLemmas;
      }
      break;
    }

    // Step 2b: Check for AccessConstArray (STORE_ALL in EQ class).
    if (!lists.d_constArrays.empty())
    {
      TNode n = lists.d_constArrays[0];
      Node defValue = n.getConst<ArrayStoreAll>().getValue();
      if (!d_ee->hasTerm(defValue) || !d_ee->areEqual(select, defValue))
      {
        if (d_inShadowRebuild)
        {
          d_shadowObligations.emplace_back(select, defValue);
        }
        else
        {
          Node conc = select.eqNode(defValue);
          std::vector<Node> expVec;
          std::vector<std::vector<PathEdge>> paths(1);
          // As in AccessStore: `entryArray = n` below subsumes the rep
          // equality, so do not emit it.
          TNode entryArray =
              findPathConditions(select, arrayRep, expVec, &paths[0], false);
          if (!entryArray.isNull())
          {
            if (entryArray != n)
            {
              expVec.push_back(entryArray.eqNode(static_cast<Node>(n)));
            }
            Node reason = nm->mkAnd(expVec);
            Trace("arrays::aext") << "AccessConstArray: " << reason << " => "
                                  << conc << std::endl;
            recordJoin(select, defValue, reason);
            d_im.arrayLemma(conc,
                            InferenceId::ARRAYS_AEXT_CONST_ARRAY,
                            reason,
                            ProofRule::ARRAYS_READ_OVER_WRITE_1,
                            std::move(paths));
            ++d_numConstArrayLemmas;
          }
        }
      }
    }

    // Step 3: RowD -- propagate downward through stores
    for (TNode n : lists.d_stores)
    {
      if (d_ee->getRepresentative(n[1]) != indexRep)
      {
        Trace("arrays::aext") << "  RowD push: " << n[0] << std::endl;
        visit.push_back(n[0]);
        ++d_numPropagationsDown;
      }
    }

    // Step 4: RowU -- propagate upward through parent stores.
    if (d_activeArrays.count(arrayRep))
    {
      for (TNode store : lists.d_parents)
      {
        TNode storeIndexRep = d_ee->getRepresentative(store[1]);
        if (indexRep != storeIndexRep)
        {
          Trace("arrays::aext") << "  RowU push: " << store << std::endl;
          visit.push_back(store);
          ++d_numPropagationsUp;
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

    const ClassLists& lists = classListsOf(arrayRep);

    // RowD
    for (TNode n : lists.d_stores)
    {
      if (d_ee->getRepresentative(n[1]) != indexRep)
      {
        TNode childRep = d_ee->getRepresentative(n[0]);
        if (bfsEdges.find(childRep) == bfsEdges.end())
        {
          bfsEdges[childRep] = {n[0], n, arrayRep, false};
          if (childRep == targetRep)
          {
            found = true;
            break;
          }
          queue.push_back(childRep);
        }
      }
    }

    if (found)
    {
      break;
    }

    // RowU
    for (TNode store : lists.d_parents)
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

  // The BFS explores a superset of what forward propagation reached -- it does
  // not apply the d_activeArrays gate, and the equality engine does not move
  // during the select loop -- so every conflict checkAccess detects has a path
  // here. What earlier checks recorded is kept valid for this by the handling
  // of index merges in applyDelta (VALIDITY on the propagation state). Should
  // that ever stop holding, do not walk a tree that has no entry for
  // targetRep: the walk below would dereference an end iterator, which Assert
  // does not prevent in a production build. Report the failure instead and
  // let the caller drop the lemma.
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
  // RIntro2: for a store s = store(b, k, v), a read rN whose array is in the
  // class of s and a read rC whose array is in the class of b, at the same
  // index class J other than k's, are equal once j != k is entailed. Only the
  // instances updateClassLists found touched by a change since the last run
  // are checked; the others were checked when they last changed, and their
  // outcome cannot have changed since.
  std::vector<std::pair<TNode, TNode>> todo;
  todo.swap(d_ri2Todo);
  d_ri2Queued.clear();
  // The reads at each array class, by index class.
  std::unordered_map<TNode, std::unordered_map<TNode, TNode>> readsAt;
  auto readsOf = [&](TNode arrayRep)
      -> const std::unordered_map<TNode, TNode>& {
    auto [it, inserted] = readsAt.try_emplace(arrayRep);
    if (inserted)
    {
      for (TNode r : classListsOf(arrayRep).d_reads)
      {
        it->second[d_ee->getRepresentative(r[1])] = r;
      }
    }
    return it->second;
  };
  for (const auto& [store, indexRep] : todo)
  {
    if (d_state.isInConflict())
    {
      return;
    }
    TNode storeRep = d_ee->getRepresentative(store);
    TNode baseRep = d_ee->getRepresentative(store[0]);
    if (storeRep == baseRep)
    {
      continue;
    }
    const auto& atStore = readsOf(storeRep);
    const auto& atBase = readsOf(baseRep);
    if (indexRep.isNull())
    {
      for (const auto& [jRep, rN] : atStore)
      {
        auto rit = atBase.find(jRep);
        if (rit != atBase.end())
        {
          fireRIntro2(store, rN, rit->second);
        }
      }
    }
    else
    {
      auto nit = atStore.find(indexRep);
      auto rit = atBase.find(indexRep);
      if (nit != atStore.end() && rit != atBase.end())
      {
        fireRIntro2(store, nit->second, rit->second);
      }
    }
  }
}

void AextArraySolver::fireRIntro2(TNode store, TNode rN, TNode rC)
{
  TNode k = store[1];
  TNode j = rN[1];
  if (d_ee->getRepresentative(k) == d_ee->getRepresentative(j) || rN == rC
      || d_ee->areEqual(rN, rC) || !d_ee->areDisequal(j, k, true))
  {
    return;
  }
  Node eq = rN.eqNode(rC);
  // Keyed on the conclusion alone, unlike CongR: this inference also asserts
  // eq as an internal fact below, and an equality engine assertion can only
  // be undone by popping the context that this cache lives in. So whenever
  // the cache suppresses a re-derivation, eq still holds; there is nothing
  // for a second guard to add.
  if (!d_rintro2LemmaCache.insert(eq))
  {
    return;
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
  Node reason = nodeManager()->mkAnd(expVec);
  Trace("arrays::aext") << "RIntro2: " << reason << " => " << eq << std::endl;
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
}

void AextArraySolver::checkRIntro2Complete()
{
  // Every instance a pass over all stores and reads would fire has fired --
  // unless something has changed since the last run, as DisEq lemmas do by
  // registering reads; the next check takes care of that.
  if (d_listSelectsDone < d_selects.size() || d_listStoresDone < d_stores.size()
      || d_listMergesDone < d_mergeQueue.size()
      || d_listDisequalitiesDone < d_disequalityQueue.size())
  {
    return;
  }
  std::unordered_map<TNode, std::unordered_map<TNode, TNode>> readsByArray;
  for (size_t i = 0, sz = d_selects.size(); i < sz; ++i)
  {
    TNode r = d_selects[i];
    if (d_ee->hasTerm(r))
    {
      readsByArray[d_ee->getRepresentative(r[0])]
                  [d_ee->getRepresentative(r[1])] = r;
    }
  }
  for (size_t si = 0, ssz = d_stores.size(); si < ssz; ++si)
  {
    TNode store = d_stores[si];
    if (!d_ee->hasTerm(store))
    {
      continue;
    }
    TNode k = store[1];
    auto sit = readsByArray.find(d_ee->getRepresentative(store));
    auto bit = readsByArray.find(d_ee->getRepresentative(store[0]));
    if (sit == readsByArray.end() || bit == readsByArray.end()
        || sit == bit)
    {
      continue;
    }
    for (const auto& [jRep, rN] : sit->second)
    {
      auto rit = bit->second.find(jRep);
      if (rit == bit->second.end() || d_ee->getRepresentative(k) == jRep)
      {
        continue;
      }
      AlwaysAssert(d_ee->areEqual(rN, rit->second)
                   || !d_ee->areDisequal(rN[1], k, false))
          << "incremental AEXT check: RIntro2 through " << store
          << " would equate " << rN << " and " << rit->second
          << ", which no run derived";
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
  // representatives), and every full effort check requests a split for every
  // undecided edge out of where it recorded a read (see pendingIndexPairs);
  // by the time a model is built, the SAT solver has decided each of them
  // and the answer is in the equality engine. Three
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
  //  - pendingIndexPairs skips a pair the equality engine already separates,
  //    two distinct constants included. That is a decided pair.
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

  for (const auto& [t1, t2] : pendingIndexPairs())
  {
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

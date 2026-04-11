/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Default array solver (Row/Ext eager lemma generation).
 *
 * Implements the standard decision procedure for the extensional theory of
 * arrays based on eager Row lemma instantiation and Ext lemma generation on
 * array disequalities.  Extracted from TheoryArrays.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__ARRAY_SOLVER_DEFAULT_H
#define CVC5__THEORY__ARRAYS__ARRAY_SOLVER_DEFAULT_H

#include <tuple>
#include <unordered_map>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "theory/arrays/array_info.h"
#include "theory/arrays/array_solver.h"
#include "theory/decision_strategy.h"
#include "theory/output_channel.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

class ArraySolverDefault : public ArraySolver
{
 public:
  ArraySolverDefault(Env& env,
                     TheoryState& state,
                     InferenceManager& im,
                     Valuation valuation,
                     eq::EqualityEngine& mayEqualEE,
                     DefValMap& defValues,
                     OutputChannel& out,
                     PreRegCallback preRegCb,
                     context::CDO<bool>& sharedTerms);
  ~ArraySolverDefault() override;

  void finishInit(eq::EqualityEngine* ee) override;

  void preRegisterSelect(TNode node) override;
  void preRegisterStore(TNode node) override;
  void preRegisterStoreAll(TNode node) override;

  void eqNotifyMerge(TNode a, TNode b) override;

  void postCheck(Theory::Effort level) override;
  void notifyArrayDisequality(TNode a, TNode b, TNode fact) override;

  void computeRelevantTerms(std::set<Node>& termSet) override;
  void augmentModelSelects(std::map<Node, std::vector<Node>>& selects,
                           const std::set<Node>& termSet) override;

  void computeCareGraph(AddCarePairFn addCarePair) override;

  void presolve() override;
  std::string identify() const override;

 private:
  using RowLemmaType = std::tuple<TNode, TNode, TNode, TNode>;

  /** Conflict when merging constants */
  void conflict(TNode a, TNode b);

  void mergeArrays(TNode a, TNode b);
  void setNonLinear(TNode a);
  void checkStore(TNode a);
  void checkRowForIndex(TNode i, TNode a);
  void checkRowLemmas(TNode a, TNode b);
  void propagateRowLemma(RowLemmaType lem);
  void queueRowLemma(RowLemmaType lem);
  bool dischargeLemmas();

  Node getSkolem(TNode ref);
  Node mkAnd(std::vector<TNode>& conjunctions,
             bool invert = false,
             unsigned startIndex = 0);

  Node removeRepLoops(TNode a, TNode rep);
  Node expandStores(TNode s,
                    std::vector<TNode>& assumptions,
                    bool checkLoop = false,
                    TNode a = TNode(),
                    TNode b = TNode());

  // Weak equivalence methods
  TNode weakEquivGetRep(TNode node);
  TNode weakEquivGetRepIndex(TNode node, TNode index);
  void visitAllLeaves(TNode reason, std::vector<TNode>& conjunctions);
  void weakEquivBuildCond(TNode node,
                          TNode index,
                          std::vector<TNode>& conjunctions);
  void weakEquivMakeRep(TNode node);
  void weakEquivMakeRepIndex(TNode node);
  void weakEquivAddSecondary(TNode index,
                             TNode arrayFrom,
                             TNode arrayTo,
                             TNode reason);
  void checkWeakEquiv(bool arraysMerged);

  /** Get next decision request for eager index splitting. */
  Node getNextDecisionRequest();

  /** Check a pair of reads for the care graph. */
  void checkPair(TNode r1, TNode r2, AddCarePairFn& addCarePair);

  /** Output channel for preferPhase/ensureLiteral. */
  OutputChannel& d_out;
  /** Callback for preregistering internally-created terms. */
  PreRegCallback d_preRegCb;
  /** Reference to shared terms flag (owned by TheoryArrays). */
  context::CDO<bool>& d_sharedTerms;

  /** True/false constants. */
  Node d_true;
  Node d_false;

  // Statistics
  IntStat d_numRow;
  IntStat d_numExt;
  IntStat d_numProp;
  IntStat d_numExplain;
  IntStat d_numNonLinear;
  IntStat d_numGetModelValSplits;
  IntStat d_numGetModelValConflicts;
  IntStat d_numSetModelValSplits;
  IntStat d_numSetModelValConflicts;

  /** Array metadata tracking */
  ArrayInfo d_infoMap;

  context::CDQueue<Node> d_mergeQueue;
  bool d_mergeInProgress;

  context::CDQueue<RowLemmaType> d_RowQueue;
  context::CDHashSet<RowLemmaType, RowLemmaTypeHashFunction> d_RowAlreadyAdded;

  /** Read terms (non-const index) for care graph. */
  context::CDList<TNode> d_reads;

  typedef std::unordered_map<Node, CTNodeList*> CNodeNListMap;
  CNodeNListMap d_constReads;
  context::CDList<TNode> d_constReadsList;
  context::Context* d_constReadsContext;

  /** Helper class to keep d_constReadsContext in sync with satContext */
  class ContextPopper : public context::ContextNotifyObj
  {
    context::Context* d_satContext;
    context::Context* d_contextToPop;

   protected:
    void contextNotifyPop() override
    {
      if (d_contextToPop->getLevel() > d_satContext->getLevel())
      {
        d_contextToPop->pop();
      }
    }

   public:
    ContextPopper(context::Context* context, context::Context* contextToPop)
        : context::ContextNotifyObj(context),
          d_satContext(context),
          d_contextToPop(contextToPop)
    {
    }
  };
  ContextPopper d_contextPopper;

  /** Decision requests for eager index splitting. */
  context::CDQueue<Node> d_decisionRequests;

  /** Permanent references for node lifetime management. */
  context::CDList<Node> d_permRef;

  typedef std::
      unordered_map<std::pair<TNode, TNode>, CTNodeList*, TNodePairHashFunction>
          ReadBucketMap;
  ReadBucketMap d_readBucketTable;
  context::Context* d_readTableContext;
  context::CDList<Node> d_arrayMerges;
  std::vector<CTNodeList*> d_readBucketAllocations;

  /**
   * The decision strategy for the theory of arrays, which calls the
   * getNextDecisionRequest function below.
   */
  class ArraySolverDefaultDecisionStrategy : public DecisionStrategy
  {
   public:
    ArraySolverDefaultDecisionStrategy(ArraySolverDefault* solver);
    void initialize() override;
    Node getNextDecisionRequest() override;
    std::string identify() const override;

   private:
    ArraySolverDefault* d_solver;
  };
  /** an instance of the above decision strategy */
  std::unique_ptr<ArraySolverDefaultDecisionStrategy> d_dstrat;
  /** Have we registered the above strategy? (context-independent) */
  bool d_dstratInit;
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__ARRAY_SOLVER_DEFAULT_H */

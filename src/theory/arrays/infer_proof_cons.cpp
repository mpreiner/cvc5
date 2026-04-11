/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference to proof conversion for the AEXT array solver.
 */

#include "theory/arrays/infer_proof_cons.h"

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_id.h"
#include "theory/arrays/skolem_cache.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arrays {

ArraysInferProofCons::ArraysInferProofCons(Env& env, context::Context* c)
    : EnvObj(env), d_lazyFactMap(c == nullptr ? &d_context : c)
{
}

void ArraysInferProofCons::notifyFact(Node conc, Node exp, InferenceId id)
{
  if (d_lazyFactMap.find(conc) != d_lazyFactMap.end())
  {
    return;
  }
  Node symFact = CDProof::getSymmFact(conc);
  if (!symFact.isNull() && d_lazyFactMap.find(symFact) != d_lazyFactMap.end())
  {
    return;
  }
  d_lazyFactMap.insert(conc, {exp, id, {}});
}

void ArraysInferProofCons::notifyFact(
    Node conc,
    Node exp,
    InferenceId id,
    std::vector<std::vector<PathEdge>>&& paths)
{
  if (d_lazyFactMap.find(conc) != d_lazyFactMap.end())
  {
    return;
  }
  Node symFact = CDProof::getSymmFact(conc);
  if (!symFact.isNull() && d_lazyFactMap.find(symFact) != d_lazyFactMap.end())
  {
    return;
  }
  d_lazyFactMap.insert(conc, {exp, id, std::move(paths)});
}

std::shared_ptr<ProofNode> ArraysInferProofCons::getProofFor(Node fact)
{
  Trace("arrays-ipc") << "arrays-ipc: ask proof for " << fact << std::endl;
  CDProof pf(d_env);
  auto it = d_lazyFactMap.find(fact);
  if (it == d_lazyFactMap.end())
  {
    Node factSym = CDProof::getSymmFact(fact);
    if (!factSym.isNull())
    {
      it = d_lazyFactMap.find(factSym);
    }
  }
  AlwaysAssert(it != d_lazyFactMap.end())
      << "arrays-ipc: no stored inference for " << fact;
  const InferInfo& ii = (*it).second;
  convert(ii, fact, &pf);
  return pf.getProofFor(fact);
}

std::string ArraysInferProofCons::identify() const
{
  return "arrays::InferProofCons";
}

void ArraysInferProofCons::convert(const InferInfo& ii,
                                   TNode conc,
                                   CDProof* cdp)
{
  InferenceId id = ii.d_id;
  TNode exp = ii.d_exp;
  Trace("arrays-ipc") << "convert: " << id << ": " << conc << " by " << exp
                       << std::endl;
  // Flatten the explanation into individual literals.
  std::vector<Node> expv;
  if (!exp.isNull() && !exp.isConst())
  {
    if (exp.getKind() == Kind::AND)
    {
      for (const Node& ec : exp)
      {
        expv.push_back(ec);
      }
    }
    else
    {
      expv.push_back(exp);
    }
  }

  bool success = false;
  switch (id)
  {
    case InferenceId::ARRAYS_READ_OVER_WRITE_1:
    {
      // RIntro1: select(store(a,i,v), i) = v
      Assert(conc.getKind() == Kind::EQUAL);
      cdp->addStep(
          conc, ProofRule::ARRAYS_READ_OVER_WRITE_1, {}, {conc[0]});
      success = true;
    }
    break;
    case InferenceId::ARRAYS_AEXT_CONGRUENCE:
    {
      convertCongruence(ii, conc, expv, cdp);
      success = true;
    }
    break;
    case InferenceId::ARRAYS_AEXT_ROW:
    {
      convertAccessStore(ii, conc, expv, cdp);
      success = true;
    }
    break;
    case InferenceId::ARRAYS_CONST_ARRAY_DEFAULT:
    {
      convertAccessConstArray(ii, conc, expv, cdp);
      success = true;
    }
    break;
    case InferenceId::ARRAYS_READ_OVER_WRITE:
    {
      convertRIntro2(conc, expv, cdp);
      success = true;
    }
    break;
    case InferenceId::ARRAYS_AEXT_DISEQUALITY:
    {
      // ExtensionalityWitness: NOT(= a b) => NOT(= select(a,k) select(b,k))
      Assert(expv.size() == 1);
      cdp->addStep(conc, ProofRule::ARRAYS_EXT, {expv[0]}, {});
      success = true;
    }
    break;
    default: break;
  }

  if (!success)
  {
    Trace("arrays-ipc") << "...failed " << id << std::endl;
    cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_ARRAYS, expv, {});
  }
  else
  {
    Trace("arrays-ipc") << "...success" << std::endl;
  }
}

// ============================================================
// Path proof helper
// ============================================================

Node ArraysInferProofCons::addPathSelectProof(
    CDProof* cdp,
    Node sel,
    const std::vector<PathEdge>& pathEdges,
    const std::vector<Node>& expv,
    size_t& expIdx)
{
  // Path edges are in target-to-start order. The last element has
  // store.isNull() (start node).  We process in reverse for the proof.
  //
  // For each store edge we build:
  //   RowD: select(store, i) = select(store[0], i)  by ROW
  //   RowU: select(store[0], i) = select(store, i)  by SYMM of ROW
  //
  // Between edges, EE merge guards (array equalities from the conditions)
  // bridge via CONG.
  //
  // The conditions in expv are in target-to-start order, matching the
  // pathEdges order.  Each store edge contributes: 0-2 array EQUALs
  // + 1 NOT.  The start edge contributes 0-1 array EQUAL.

  Assert(!pathEdges.empty() && pathEdges.back().store.isNull())
      << "pathEdges must end with the start node (null store)";

  NodeManager* nm = nodeManager();
  Node readIndex = sel[1];
  size_t numStoreEdges = pathEdges.size() - 1;

  // Partition conditions into per-edge groups.
  struct EdgeConds
  {
    std::vector<Node> arrayEqs;
    Node indexDiseq;
  };
  std::vector<EdgeConds> ec(pathEdges.size());

  for (size_t e = 0; e < numStoreEdges; ++e)
  {
    while (expIdx < expv.size() && expv[expIdx].getKind() == Kind::EQUAL)
    {
      ec[e].arrayEqs.push_back(expv[expIdx++]);
    }
    Assert(expIdx < expv.size() && expv[expIdx].getKind() == Kind::NOT);
    ec[e].indexDiseq = expv[expIdx++];
  }
  // Start edge: at most one array equality (startArray = startRep guard).
  // Stop consuming when we see a condition not related to our path.
  // The start guard, if present, has one side equal to sel[0].
  if (expIdx < expv.size() && expv[expIdx].getKind() == Kind::EQUAL)
  {
    Node lit = expv[expIdx];
    if (lit[0] == sel[0] || lit[1] == sel[0])
    {
      ec[numStoreEdges].arrayEqs.push_back(expv[expIdx++]);
    }
  }

  // Build proof purely from PathEdge structure.
  // Process edges in REVERSE order (start → target), matching how
  // we walk from sel's array toward the target array rep.
  //
  // For RowD edge (store in parent class, store[0] in child class):
  //   Forward (start→target): we go from store to store[0].
  //   ROW: select(store, i) = select(store[0], i).
  //
  // For RowU edge (store[0] in child class, store in parent class):
  //   Forward (start→target): we go from store[0] to store.
  //   SYMM of ROW: select(store[0], i) = select(store, i).
  //
  // Between edges, CONG steps bridge via explanation equalities.
  // We track curSel and advance it through each step.

  Node curSel = sel;
  std::vector<Node> transEqs;

  for (size_t ie = numStoreEdges; ie > 0; --ie)
  {
    size_t e = ie - 1;
    const PathEdge& pe = pathEdges[e];
    TNode store = pe.store;
    Assert(!store.isNull() && store.getKind() == Kind::STORE);

    // ROW: select(store, i) = select(store[0], i)
    Node selectOnStore =
        nm->mkNode(Kind::SELECT, static_cast<Node>(store), readIndex);
    Node selectOnChild = nm->mkNode(Kind::SELECT, store[0], readIndex);
    Node diseq = store[1].eqNode(readIndex).notNode();
    Node rowConc = selectOnStore.eqNode(selectOnChild);
    cdp->addStep(
        rowConc, ProofRule::ARRAYS_READ_OVER_WRITE, {diseq}, {selectOnStore});

    if (!pe.isRowU)
    {
      // RowD: forward is store → store[0].
      // Need curSel to be select(store, readIndex).
      if (curSel != selectOnStore)
      {
        // CONG to bridge curSel to selectOnStore.
        Node arrEq = curSel[0].eqNode(static_cast<Node>(store));
        std::vector<Node> premises = {arrEq, Node()};
        expr::proveCong(d_env, cdp, curSel, premises);
        transEqs.push_back(curSel.eqNode(selectOnStore));
      }
      transEqs.push_back(rowConc);
      curSel = selectOnChild;
    }
    else
    {
      // RowU: forward is store[0] → store.
      // Need curSel to be select(store[0], readIndex).
      if (curSel != selectOnChild)
      {
        Node arrEq = curSel[0].eqNode(store[0]);
        std::vector<Node> premises = {arrEq, Node()};
        expr::proveCong(d_env, cdp, curSel, premises);
        transEqs.push_back(curSel.eqNode(selectOnChild));
      }
      // SYMM of ROW: select(store[0], i) = select(store, i)
      transEqs.push_back(selectOnChild.eqNode(selectOnStore));
      curSel = selectOnStore;
    }
  }

  // Chain with TRANS if needed.
  if (transEqs.size() > 1)
  {
    cdp->addStep(sel.eqNode(curSel), ProofRule::TRANS, transEqs, {});
  }

  return curSel;
}

// ============================================================
// Per-inference converters
// ============================================================

void ArraysInferProofCons::convertCongruence(const InferInfo& ii,
                                             TNode conc,
                                             const std::vector<Node>& expv,
                                             CDProof* cdp)
{
  // CongR: two selects reached the same array at the same index.
  // conc: sel1 = sel2
  // exp: [path1 conditions] [path2 conditions] [optional: index equality]
  // paths: ii.d_paths[0] = path for sel1, ii.d_paths[1] = path for sel2

  if (ii.d_paths.size() < 2)
  {
    Trace("arrays-ipc") << "convertCongruence: no path info, TRUST" << std::endl;
    cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_ARRAYS, expv, {});
    return;
  }

  Assert(conc.getKind() == Kind::EQUAL);
  Node sel1 = conc[0];
  Node sel2 = conc[1];
  Assert(sel1.getKind() == Kind::SELECT && sel2.getKind() == Kind::SELECT);

  size_t expIdx = 0;

  // Build path proof for sel1.
  Node endSel1 = addPathSelectProof(cdp, sel1, ii.d_paths[0], expv, expIdx);

  // Build path proof for sel2.
  Node endSel2 = addPathSelectProof(cdp, sel2, ii.d_paths[1], expv, expIdx);

  // Now we have:
  //   sel1 = endSel1 (= select(entryArr1, idx1))
  //   sel2 = endSel2 (= select(entryArr2, idx2))
  // And endSel1, endSel2 should be selects on the same array rep at the
  // same index rep.

  // Handle remaining conditions: index equality.
  // At this point, endSel1 = select(A, i1) and endSel2 = select(B, i2)
  // where A and B might be the same, and i1/i2 might be equal in EE.

  Trace("arrays-ipc") << "  endSel1=" << endSel1 << std::endl;
  Trace("arrays-ipc") << "  endSel2=" << endSel2 << std::endl;

  // Build equality between endSel1 and endSel2 if they differ.
  std::vector<Node> midTransEqs;
  if (endSel1 != endSel2)
  {
    NodeManager* nm = nodeManager();
    Node endArr1 = endSel1[0];
    Node endArr2 = endSel2[0];
    Node endIdx1 = endSel1[1];
    Node endIdx2 = endSel2[1];

    // Check remaining expv for index equalities.
    Node idxEq;
    while (expIdx < expv.size())
    {
      Node lit = expv[expIdx];
      ++expIdx;
      if (lit.getKind() == Kind::EQUAL
          && ((lit[0] == endIdx1 && lit[1] == endIdx2)
              || (lit[0] == endIdx2 && lit[1] == endIdx1)))
      {
        idxEq = lit;
      }
    }

    // If the endpoints' arrays differ, we need to bridge them.
    // Both paths used CONG steps from explanation equalities.
    // These equalities are assumptions in our proof (already consumed
    // by the path proofs as CONG premises).  We can reference them
    // again to build the bridge — CDProof handles sharing.
    if (endArr1 != endArr2)
    {
      // Collect ALL array equalities from the explanation (including
      // those already consumed by path proofs) as an undirected graph.
      std::unordered_map<TNode, std::vector<std::pair<TNode, Node>>> adjMap;
      for (const Node& lit : expv)
      {
        if (lit.getKind() == Kind::EQUAL && lit[0].getType().isArray())
        {
          adjMap[lit[0]].push_back({lit[1], lit});
          adjMap[lit[1]].push_back({lit[0], lit});
        }
      }

      // BFS from endArr1 to endArr2 through the equality graph.
      std::unordered_map<TNode, std::pair<TNode, Node>> parent;
      std::deque<TNode> bfsQ;
      bfsQ.push_back(endArr1);
      parent[endArr1] = {TNode(), Node()};
      bool bridgeFound = false;
      while (!bfsQ.empty() && !bridgeFound)
      {
        TNode cur = bfsQ.front();
        bfsQ.pop_front();
        auto ait = adjMap.find(cur);
        if (ait == adjMap.end()) continue;
        for (const auto& [next, eq] : ait->second)
        {
          if (parent.find(next) != parent.end()) continue;
          parent[next] = {cur, eq};
          if (next == endArr2)
          {
            bridgeFound = true;
            break;
          }
          bfsQ.push_back(next);
        }
      }

      if (bridgeFound)
      {
        // Walk back from endArr2 to endArr1, building CONG steps.
        // Each step: select(A, idx) = select(B, idx) from A = B.
        Node curArr = endArr2;
        Node readIdx = endIdx1;
        std::vector<Node> bridgeEqs;
        while (curArr != endArr1)
        {
          auto [prevArr, eq] = parent[curArr];
          Node selPrev = nm->mkNode(Kind::SELECT, prevArr, readIdx);
          Node selCur = nm->mkNode(Kind::SELECT, curArr, readIdx);
          Node eqToUse = (eq[0] == prevArr) ? eq : eq[1].eqNode(eq[0]);
          std::vector<Node> premises = {eqToUse, Node()};
          expr::proveCong(d_env, cdp, selPrev, premises);
          bridgeEqs.push_back(selPrev.eqNode(selCur));
          curArr = prevArr;
        }
        // bridgeEqs is in endArr2→endArr1 order (walk from endArr2
        // back through parent links to endArr1).  Each eq is
        //   select(prevArr, readIdx) = select(curArr, readIdx)
        // where prevArr is toward endArr1.
        // We need endSel1 = endSel2, i.e.,
        //   select(endArr1, readIdx) = select(endArr2, readIdx).
        // Reversed, the chain starts from endArr1 and ends at endArr2.
        // But the individual steps are already in the right direction
        // for SYMM.  CDProof handles direction via auto-SYMM.
        //
        // Just push all bridge equalities to midTransEqs.
        // CDProof + TRANS will chain them.
        Trace("arrays-ipc") << "  bridge found, " << bridgeEqs.size()
                             << " steps" << std::endl;
        for (auto it = bridgeEqs.rbegin(); it != bridgeEqs.rend(); ++it)
        {
          Trace("arrays-ipc") << "  bridge eq: " << *it << std::endl;
          midTransEqs.push_back(*it);
        }
      }
      else
      {
        // No path found through equalities; fall back to TRUST.
        Trace("arrays-ipc") << "convertCongruence: can't bridge arrays from "
                            << endArr1 << " to " << endArr2
                            << ", adjMap size=" << adjMap.size()
                            << ", TRUST" << std::endl;
        cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_ARRAYS, expv, {});
        return;
      }

      // After bridging arrays, handle index if needed.
      if (endIdx1 != endIdx2 && !idxEq.isNull())
      {
        Node selBridged = nm->mkNode(Kind::SELECT, endArr2, endIdx1);
        Node eqToUse = (idxEq[0] == endIdx1) ? idxEq : idxEq[1].eqNode(idxEq[0]);
        std::vector<Node> premises = {Node(), eqToUse};
        expr::proveCong(d_env, cdp, selBridged, premises);
        midTransEqs.push_back(selBridged.eqNode(endSel2));
      }
    }
    else if (endIdx1 != endIdx2)
    {
      // Arrays match but indices differ.
      Node idxPrem = idxEq.isNull() ? endIdx1.eqNode(endIdx2) : idxEq;
      Node eqToUse = (idxPrem[0] == endIdx1) ? idxPrem : idxPrem[1].eqNode(idxPrem[0]);
      std::vector<Node> premises = {Node(), eqToUse};
      expr::proveCong(d_env, cdp, endSel1, premises);
      midTransEqs.push_back(endSel1.eqNode(endSel2));
    }
  }

  // Now chain everything: sel1 = endSel1 [= endSel2] = sel2
  // The path proofs already added sel1 = endSel1 and sel2 = endSel2.
  // We need: sel1 = sel2
  // So: sel1 = endSel1, endSel1 = endSel2, endSel2 = sel2 (SYMM of sel2 = endSel2)
  std::vector<Node> finalTransEqs;

  // sel1 = endSel1 (from path proof)
  if (sel1 != endSel1)
  {
    finalTransEqs.push_back(sel1.eqNode(endSel1));
  }

  // endSel1 = endSel2 (from CONG, if needed)
  for (const Node& eq : midTransEqs)
  {
    finalTransEqs.push_back(eq);
  }

  // endSel2 = sel2 (SYMM of sel2 = endSel2 from path proof)
  if (sel2 != endSel2)
  {
    finalTransEqs.push_back(endSel2.eqNode(sel2));
  }

  if (finalTransEqs.size() > 1)
  {
    cdp->addStep(conc, ProofRule::TRANS, finalTransEqs, {});
  }
  else if (finalTransEqs.size() == 1 && finalTransEqs[0] != conc)
  {
    // Might need SYMM
    cdp->addStep(conc, ProofRule::TRANS, finalTransEqs, {});
  }
  // If finalTransEqs is empty, sel1 == endSel1 == endSel2 == sel2, i.e. conc
  // is trivially true.  That shouldn't happen (we wouldn't generate a lemma).
}

void ArraysInferProofCons::convertAccessStore(const InferInfo& ii,
                                              TNode conc,
                                              const std::vector<Node>& expv,
                                              CDProof* cdp)
{
  // AccessStore: select(a, i) = v where store(b, j, v) has i==j in EE.
  // conc: select(a, i) = v
  // exp: [path conditions] [optional: i = j] [optional: entryArray = store]
  // paths: ii.d_paths[0] = path from sel to the array rep containing the store

  if (ii.d_paths.empty())
  {
    Trace("arrays-ipc") << "convertAccessStore: no path info, TRUST" << std::endl;
    cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_ARRAYS, expv, {});
    return;
  }

  NodeManager* nm = nodeManager();
  Assert(conc.getKind() == Kind::EQUAL);
  Node sel = conc[0];
  Node val = conc[1];
  Assert(sel.getKind() == Kind::SELECT);

  size_t expIdx = 0;
  Node endSel = addPathSelectProof(cdp, sel, ii.d_paths[0], expv, expIdx);

  // endSel = select(entryArray, readIndex)
  // Now consume remaining conditions: index equality and array equality to store.
  Node readIndex = sel[1];
  Node endArray = endSel[0];
  Node store;
  Node storeIdx;
  Node indexEq;
  Node arrayEq;

  while (expIdx < expv.size())
  {
    Node lit = expv[expIdx];
    ++expIdx;
    if (lit.getKind() == Kind::EQUAL)
    {
      // Determine if this is index or array equality.
      // The AEXT solver adds: index.eqNode(n[1]) for index eq,
      // entryArray.eqNode(n) for array eq to the store.
      if (lit[0] == readIndex || lit[1] == readIndex)
      {
        indexEq = lit;
      }
      else
      {
        arrayEq = lit;
      }
    }
  }

  // Identify the store term from the value.
  // val is store[2], so we need to find a store with that value.
  // It's in the arrayEq (if present) or endArray is the store itself.
  if (!arrayEq.isNull())
  {
    // arrayEq is entryArray = store or store = entryArray.
    if (arrayEq[0] == endArray)
    {
      store = arrayEq[1];
    }
    else
    {
      store = arrayEq[0];
    }
  }
  else
  {
    store = endArray;
  }

  if (store.getKind() != Kind::STORE || store[2] != val)
  {
    // Can't reconstruct; fall back to TRUST.
    Trace("arrays-ipc") << "convertAccessStore: can't identify store, TRUST"
                        << std::endl;
    cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_ARRAYS, expv, {});
    return;
  }

  storeIdx = store[1];
  std::vector<Node> transEqs;

  // sel = endSel (from path proof)
  if (sel != endSel)
  {
    transEqs.push_back(sel.eqNode(endSel));
  }

  // endSel = select(store, readIndex) via CONG from arrayEq
  if (!arrayEq.isNull())
  {
    Node selOnStore = nm->mkNode(Kind::SELECT, static_cast<Node>(store), readIndex);
    Node eqToUse = (endArray == arrayEq[0]) ? arrayEq : arrayEq[1].eqNode(arrayEq[0]);
    std::vector<Node> premises = {eqToUse, Node()};
    expr::proveCong(d_env, cdp, endSel, premises);
    transEqs.push_back(endSel.eqNode(selOnStore));
    endSel = selOnStore;
  }

  // select(store, readIndex) = select(store, storeIdx) via CONG from indexEq
  if (!indexEq.isNull() && readIndex != storeIdx)
  {
    Node selOnStoreWithStoreIdx =
        nm->mkNode(Kind::SELECT, static_cast<Node>(store), storeIdx);
    Node eqToUse;
    if (indexEq[0] == readIndex && indexEq[1] == storeIdx)
    {
      eqToUse = indexEq;
    }
    else
    {
      eqToUse = readIndex.eqNode(storeIdx);
    }
    std::vector<Node> premises = {Node(), eqToUse};
    expr::proveCong(d_env, cdp, endSel, premises);
    transEqs.push_back(
        endSel.eqNode(selOnStoreWithStoreIdx));
    endSel = selOnStoreWithStoreIdx;
  }

  // ROW_1: select(store(b, storeIdx, v), storeIdx) = v
  Node row1Conc = endSel.eqNode(val);
  cdp->addStep(row1Conc, ProofRule::ARRAYS_READ_OVER_WRITE_1, {}, {endSel});
  transEqs.push_back(row1Conc);

  // Chain with TRANS.
  if (transEqs.size() > 1)
  {
    cdp->addStep(conc, ProofRule::TRANS, transEqs, {});
  }
}

void ArraysInferProofCons::convertAccessConstArray(
    const InferInfo& ii,
    TNode conc,
    const std::vector<Node>& expv,
    CDProof* cdp)
{
  // AccessConstArray: select(a, i) = defaultValue
  // conc: select(a, i) = defaultValue
  // exp: [path conditions] [optional: entryArray = constArray]

  if (ii.d_paths.empty())
  {
    Trace("arrays-ipc") << "convertAccessConstArray: no path info, TRUST"
                        << std::endl;
    cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_ARRAYS, expv, {});
    return;
  }

  NodeManager* nm = nodeManager();
  Assert(conc.getKind() == Kind::EQUAL);
  Node sel = conc[0];
  Node defVal = conc[1];
  Assert(sel.getKind() == Kind::SELECT);
  Node readIndex = sel[1];

  size_t expIdx = 0;
  Node endSel = addPathSelectProof(cdp, sel, ii.d_paths[0], expv, expIdx);

  // Consume remaining array equality to constant array.
  Node constArr;
  Node arrayEq;
  while (expIdx < expv.size())
  {
    Node lit = expv[expIdx];
    ++expIdx;
    if (lit.getKind() == Kind::EQUAL)
    {
      arrayEq = lit;
    }
  }

  std::vector<Node> transEqs;
  if (sel != endSel)
  {
    transEqs.push_back(sel.eqNode(endSel));
  }

  // CONG to reach select(constArr, readIndex).
  if (!arrayEq.isNull())
  {
    Node endArray = endSel[0];
    constArr = (arrayEq[0] == endArray) ? arrayEq[1] : arrayEq[0];
    Node selOnConst = nm->mkNode(Kind::SELECT, constArr, readIndex);
    Node eqToUse = (endArray == arrayEq[0]) ? arrayEq : arrayEq[1].eqNode(arrayEq[0]);
    std::vector<Node> premises = {eqToUse, Node()};
    expr::proveCong(d_env, cdp, endSel, premises);
    transEqs.push_back(endSel.eqNode(selOnConst));
    endSel = selOnConst;
  }
  else
  {
    constArr = endSel[0];
  }

  // THEORY_REWRITE: select(constArr, readIndex) = defaultValue
  Node rwConc = endSel.eqNode(defVal);
  cdp->addTheoryRewriteStep(rwConc, ProofRewriteRule::ARRAYS_SELECT_CONST);
  transEqs.push_back(rwConc);

  if (transEqs.size() > 1)
  {
    cdp->addStep(conc, ProofRule::TRANS, transEqs, {});
  }
}

void ArraysInferProofCons::convertRIntro2(TNode conc,
                                          const std::vector<Node>& expv,
                                          CDProof* cdp)
{
  // RIntro2: rN = rC through a single store.
  // conc: rN = rC where rN = select(X, j), rC = select(Y, j')
  // exp: [optional: X = store] [optional: Y = store[0]]
  //      [optional: j' = j] [required: NOT(= j k)]
  //
  // The store is store(c, k, v), X is EE-equal to store, Y is EE-equal to c.

  NodeManager* nm = nodeManager();
  Assert(conc.getKind() == Kind::EQUAL);
  Node rN = conc[0];  // select(X, j)
  Node rC = conc[1];  // select(Y, j')
  Assert(rN.getKind() == Kind::SELECT && rC.getKind() == Kind::SELECT);

  // Parse the explanation.
  Node store;
  Node arrEqN;   // X = store
  Node arrEqC;   // Y = store[0]
  Node idxEq;    // j' = j
  Node idxDiseq; // NOT(= j k)

  for (const Node& lit : expv)
  {
    if (lit.getKind() == Kind::NOT)
    {
      idxDiseq = lit;
    }
    else if (lit.getKind() == Kind::EQUAL)
    {
      // Determine which equality this is.
      // arrEqN: one side is rN[0], other side is a STORE
      // arrEqC: one side is rC[0], other side is store[0]
      // idxEq: indices
      if (lit[0] == rN[0] || lit[1] == rN[0])
      {
        arrEqN = lit;
      }
      else if (lit[0] == rC[0] || lit[1] == rC[0])
      {
        arrEqC = lit;
      }
      else if (lit[0] == rC[1] || lit[1] == rC[1]
               || lit[0] == rN[1] || lit[1] == rN[1])
      {
        idxEq = lit;
      }
    }
  }

  // Identify the store from arrEqN.
  if (!arrEqN.isNull())
  {
    store = (arrEqN[0] == rN[0]) ? arrEqN[1] : arrEqN[0];
  }
  else
  {
    // rN[0] IS the store.
    store = rN[0];
  }

  if (store.getKind() != Kind::STORE)
  {
    Trace("arrays-ipc") << "convertRIntro2: can't identify store, TRUST"
                        << std::endl;
    cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_ARRAYS, expv, {});
    return;
  }

  Assert(!idxDiseq.isNull());
  TNode j = rN[1];
  TNode k = store[1];
  Node storeChild = store[0];

  std::vector<Node> transEqs;

  // Step 1: rN = select(store, j) via CONG from arrEqN
  Node selOnStore = nm->mkNode(Kind::SELECT, static_cast<Node>(store), j);
  if (rN != selOnStore)
  {
    Assert(!arrEqN.isNull());
    Node eqToUse =
        (arrEqN[0] == rN[0]) ? arrEqN : arrEqN[1].eqNode(arrEqN[0]);
    std::vector<Node> premises = {eqToUse, Node()};
    expr::proveCong(d_env, cdp, rN, premises);
    transEqs.push_back(rN.eqNode(selOnStore));
  }

  // Step 2: ROW: select(store, j) = select(store[0], j)
  Node selOnChild = nm->mkNode(Kind::SELECT, storeChild, j);
  Node diseq = k.eqNode(j).notNode();
  Node rowConc = selOnStore.eqNode(selOnChild);
  cdp->addStep(
      rowConc, ProofRule::ARRAYS_READ_OVER_WRITE, {diseq}, {selOnStore});
  transEqs.push_back(rowConc);

  // Step 3: select(store[0], j) = select(Y, j) via CONG from arrEqC
  Node rCArray = rC[0];
  if (storeChild != rCArray)
  {
    Assert(!arrEqC.isNull());
    Node eqToUse;
    if (arrEqC[0] == rCArray)
    {
      eqToUse = arrEqC[1].eqNode(arrEqC[0]);
    }
    else
    {
      eqToUse = arrEqC;
    }
    // We want storeChild = rCArray, so we need the right direction.
    Node scEqRC = storeChild.eqNode(rCArray);
    // Check if arrEqC gives us this.
    if ((arrEqC[0] == storeChild && arrEqC[1] == rCArray)
        || (arrEqC[0] == rCArray && arrEqC[1] == storeChild))
    {
      eqToUse = (arrEqC[0] == storeChild)
                    ? arrEqC
                    : arrEqC[1].eqNode(arrEqC[0]);
    }
    std::vector<Node> premises = {eqToUse, Node()};
    expr::proveCong(d_env, cdp, selOnChild, premises);
    Node selOnRCArray = nm->mkNode(Kind::SELECT, rCArray, j);
    transEqs.push_back(selOnChild.eqNode(selOnRCArray));
  }

  // Step 4: select(Y, j) = select(Y, j') via CONG from idxEq
  TNode jPrime = rC[1];
  if (j != jPrime)
  {
    Assert(!idxEq.isNull());
    Node selOnRCj = nm->mkNode(Kind::SELECT, rCArray, j);
    Node eqToUse;
    if (idxEq[0] == j && idxEq[1] == jPrime)
    {
      eqToUse = idxEq;
    }
    else
    {
      eqToUse = j.eqNode(jPrime);
    }
    std::vector<Node> premises = {Node(), eqToUse};
    expr::proveCong(d_env, cdp, selOnRCj, premises);
    transEqs.push_back(selOnRCj.eqNode(rC));
  }

  // Chain all steps.
  if (transEqs.size() > 1)
  {
    cdp->addStep(conc, ProofRule::TRANS, transEqs, {});
  }
  else if (transEqs.size() == 1 && transEqs[0] != conc)
  {
    // Single step but might need renaming.
    cdp->addStep(conc, ProofRule::TRANS, transEqs, {});
  }
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

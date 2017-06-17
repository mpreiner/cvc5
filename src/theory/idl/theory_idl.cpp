/*********************                                                        */
/*! \file theory_idl.cpp
 **/

#include "theory/idl/theory_idl.h"

#include <set>
#include <queue>

#include "options/idl_options.h"
#include "theory/rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace idl {

TheoryIdl::TheoryIdl(context::Context* c, context::UserContext* u,
                     OutputChannel& out, Valuation valuation,
                     const LogicInfo& logicInfo)
  : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo),
  d_distances(c),
  d_propagationEdges(c),
  d_pathEdges(c),
  d_varList(c),
  d_propagatedLevels(c),
  d_explanations(c),
  d_distSetLevels(c),
  d_assertions(c),
  d_propagationIndices(c)
{}

void TheoryIdl::preRegisterTerm(TNode node) {
  Assert(node.getKind() != kind::NOT);
  if (node.isVar()) {
    d_varList.push_back(node);
    d_distances[std::make_pair(node, node)] = 0;
    d_distSetLevels[std::make_pair(node, node)] = 0;
    return;
  } else {
    IDLAssertion idl_assertion(node);
    if (idl_assertion.ok()) {
      TNodePair xy = std::make_pair(idl_assertion.getX(), idl_assertion.getY());
      std::vector<TNode> prop_edge;
      if(d_propagationEdges.contains(xy)) {
        prop_edge = d_propagationEdges[xy].get();
      }
      prop_edge.push_back(node);
      d_propagationEdges[xy] = prop_edge;
      numprops++;
    }
  }
}

void TheoryIdl::presolve() {
  // Debug("theory::idl") << "TheoryIdl::preSolve(): d_numVars = " << d_numVars << std::endl;
}

void TheoryIdl::postsolve() {
  // Debug("theory::idl") << "TheoryIdl::postSolve()" << std::endl;
}

Node TheoryIdl::ppRewrite(TNode atom) {
  Assert(atom.getKind() != kind::NOT);
  if (atom.getKind() == kind::EQUAL) {
    Node leq = NodeBuilder<2>(kind::LEQ) << atom[0] << atom[1];
    Node geq = NodeBuilder<2>(kind::GEQ) << atom[0] << atom[1];
    Node rewritten = Rewriter::rewrite(leq.andNode(geq));
    return rewritten;
  }
  return atom;
}

void TheoryIdl::propagate(Effort level) {
  // cout << "propagate! at level " << getSatContext()->getLevel() << " and current is " << d_currentLevel << endl;
  // if (d_levelJumped) {
  //   size_t numpropagated = 0;
  //   size_t sizebefore = d_propagationQueue.size();
  //   bool value;
  //   for (unsigned i = 0; i < d_propagationQueue.size(); ++i) {
  //     if(!d_valuation.hasSatValue(d_propagationQueue[i], value)) {
  //       numpropagated++;
  //       d_out->propagate(d_propagationQueue[i]);
  //     }
  //   }
  //   cout << "of " << sizebefore << " possibilities propagated " << numpropagated << endl;
  //   d_propagationQueue.clear();    
  //   d_levelJumped = false;
  // }
}

Node TheoryIdl::explain(TNode n) {
  Assert(d_propagationIndices.contains(n));
  std::pair<unsigned, unsigned> indices = d_propagationIndices[n];

  int level = d_propagatedLevels[n];

  unsigned assertionIdx = indices.second;
  unsigned firstAssertionIdx = indices.first;

  HashGraphType graph;
  HashGraphEdgesType next;

  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode x = d_varList[i];
    for (unsigned j = 0; j < d_varList.size(); ++j) {
      TNode y = d_varList[j];
      TNodePair xy = std::make_pair(x, y);
      if (d_distSetLevels.contains(xy) && (d_distSetLevels[xy] < level)) {
        Assert(d_distances.contains(xy));
        graph[xy] = ((context::CDOhash_map<TNodePair, Integer, TNodePairHashFunction>*)((d_distances[xy]).getAtLevel(level)))->get();
        next[xy] = ((context::CDOhash_map<TNodePair, TNode, TNodePairHashFunction>*)((d_pathEdges[xy]).getAtLevel(level)))->get();
      }
    }
  }

  for (unsigned k = firstAssertionIdx; k < assertionIdx; ++k) {
      IDLAssertion idl_assertion = IDLAssertion(d_assertions[k]);

  TNode x = idl_assertion.getX();
  TNode y = idl_assertion.getY();
  Integer c = idl_assertion.getC();
  TNodePair xy = std::make_pair(x, y);
  TNodePair yx = std::make_pair(y, x);



  std::vector<TNode> valid_vars;
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair yz = std::make_pair(y, z);
    TNodePair xz = std::make_pair(x, z); // TODO: eliminate double lookups
    if ( (graph.count(yz) > 0) && ((graph.count(xz) == 0) || (((c + graph[yz]) < graph[xz])))) {
      valid_vars.push_back(z);
    }
  }
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair zx = std::make_pair(z, x);
    TNodePair zy = std::make_pair(z, y);
    if((graph.count(zx) > 0)
      && ((graph.count(zy) == 0) || ((c + graph[zx]) < graph[zy]))) {
        for (unsigned j = 0; j < valid_vars.size(); ++j) {
          TNode v = valid_vars[j];
          TNodePair yv = std::make_pair(y, v);
          TNodePair zv = std::make_pair(z, v);
          Integer dist = c + graph[zx] + graph[yv];
          if ((graph.count(zv) == 0) || (dist < graph[zv])) {
            graph[zv] = dist;
            next[zv] = idl_assertion.getTNode();
          }
        }
    }
  }


  }

  std::vector<TNode> reasonslist;
  Node explanation;
  IDLAssertion idl_assertion = IDLAssertion(n);
  getPath(next, reasonslist, idl_assertion.getX(), idl_assertion.getY());
  // cout << "PROP explanation " << reasonslist << " for " << n << endl;
  // cout << "PROP eager explanation " << d_explanations[n].get() << endl;
  // reasonslist = d_explanations[n].get();
  if (reasonslist.size() > 1) {
    explanation = NodeManager::currentNM()->mkNode(kind::AND, reasonslist);    
  } else {
    explanation = reasonslist[0];
  }
  // cout << "explanation " << explanation << endl;

  return explanation;
}

void TheoryIdl::check(Effort level) {
  if (done() && !fullEffort(level)) {
    return;
  }

  // cout << "check! at level " << getSatContext()->getLevel() << " and current is " << d_currentLevel << endl;
  if(getSatContext()->getLevel() != d_currentLevel) {
    // cout << "jump from lvl " << d_currentLevel << " to " << getSatContext()->getLevel() << endl;
    d_lastLevelJumpIdx = d_assertions.size();
    d_currentLevel = getSatContext()->getLevel();
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  while(!done()) {
    // Get the next assertion
    Assertion assertion = get();
    Debug("theory::idl") << "TheoryIdl::check(): processing " << assertion.assertion << std::endl;
    IDLAssertion idl_assertion(assertion);
    // cout << "doing assertion " << assertion << endl;
    bool ok = processAssertion(idl_assertion);
    Debug("theory::idl") << "assertion " << assertion << endl;
    if (!ok) {
      // cout << "conflict! " << endl;
      // d_propagationQueue.clear();
      std::vector<TNode> reasonslist;
      bool valgp = getPath(d_pathEdges, reasonslist, idl_assertion.getY(), idl_assertion.getX());
      // cout << "CONFLICT was " << valgp << " and size = " << reasonslist.size() << endl;
      reasonslist.push_back(idl_assertion.getTNode());
      Node conflict = NodeManager::currentNM()->mkNode(kind::AND, reasonslist);
      // cout << "CONFLICT " << conflict << endl;
      d_out->conflict(conflict);
      return;
    }
  }
}

bool TheoryIdl::processAssertion(const IDLAssertion& assertion) {
  Assert(assertion.ok());

  TNode x = assertion.getX();
  TNode y = assertion.getY();
  Integer c = assertion.getC();
  TNodePair xy = std::make_pair(x, y);
  TNodePair yx = std::make_pair(y, x);

  // Check whether we introduce a negative cycle.
  if( d_distances.contains(yx) && ((d_distances[yx].get() + c) < 0) ) {
    return false;
  }

  d_assertions.push_back(assertion.getTNode()); // Add assertion to list!!!

  // Find shortest paths incrementally
  std::vector<TNode> valid_vars;
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair yz = std::make_pair(y, z);
    TNodePair xz = std::make_pair(x, z); // TODO: eliminate double lookups
    if ( d_distances.contains(yz) && ((!d_distances.contains(xz)) || ((c + d_distances[yz].get()) < d_distances[xz].get())) ) {
      valid_vars.push_back(z);
    }
  }
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair zx = std::make_pair(z, x);
    TNodePair zy = std::make_pair(z, y);
    if(d_distances.contains(zx)
      && ((!d_distances.contains(zy)) || ((c + d_distances[zx].get()) < d_distances[zy].get()))) {
        for (unsigned j = 0; j < valid_vars.size(); ++j) {
          TNode v = valid_vars[j];
          TNodePair yv = std::make_pair(y, v);
          TNodePair zv = std::make_pair(z, v);
          Integer dist = c + d_distances[zx].get() + d_distances[yv].get();
          if ((!d_distances.contains(zv)) || (dist < d_distances[zv].get())) {
            if (!d_distances.contains(zv)) {
              d_distSetLevels[zv] = getSatContext()->getLevel();
            }
            d_distances[zv] = dist;
            d_pathEdges[zv] = assertion.getTNode();
            // Propagate anything implied by the new shortest path
            if (d_propagationEdges.contains(zv)) {
              const std::vector<TNode>& prop_assertions = d_propagationEdges[zv].get();
              for (unsigned k = 0; k < prop_assertions.size(); ++k) {
                IDLAssertion propagation_assertion = IDLAssertion(prop_assertions[k]);
                bool value;
                if (!d_valuation.isSatLiteral(propagation_assertion.getTNode())) {
                  // cout << "PROPAGATION ERROR" << endl;
                }
                if ((dist <= propagation_assertion.getC()) && !d_valuation.hasSatValue(propagation_assertion.getTNode(), value)) {
                  d_propagatedLevels[propagation_assertion.getTNode()] = getSatContext()->getLevel();
                  d_propagationIndices[propagation_assertion.getTNode()] = std::make_pair(d_lastLevelJumpIdx, d_assertions.size());
                  // cout << "adding " << propagation_assertion.getTNode() << " to prop queue at " << getSatContext()->getLevel() << endl;
                  // std::vector<TNode> bunchaedges;
                  // getPath(d_pathEdges, getSatContext()->getLevel(), bunchaedges,
                  //   propagation_assertion.getX(), propagation_assertion.getY());
                  // d_explanations[propagation_assertion.getTNode()] = bunchaedges;
                  // cout << "propagating! " << propagation_assertion.getTNode() << " at level " << (d_pathEdges[zv]).getLevel() << endl;
                  d_out->propagate(propagation_assertion.getTNode());
                }
              }
            }
          }
        }
    }
  }

  return true;
}

bool TheoryIdl::getPath(TNodePairToTNodeCDMap& pathedges, std::vector<TNode>& edges, TNode s, TNode t) {
  if (s != t) {
    TNodePair st = std::make_pair(s, t);
    if (!(pathedges.contains(st))) {
      return false;
    }
    TNode n = (pathedges[st]).get();
    IDLAssertion assertion = IDLAssertion(n);
    getPath(pathedges, edges, s, assertion.getX());
    edges.push_back(assertion.getTNode());
    getPath(pathedges, edges, assertion.getY(), t);
  }
  return true;
}

bool TheoryIdl::getPath(HashGraphEdgesType& nextArray, std::vector<TNode>& edges, TNode s, TNode t) {
  if (s != t) {
    TNodePair st = std::make_pair(s, t);
    if (nextArray.count(st) == 0) {
      return false;
    }
    TNode n = nextArray[st];
    IDLAssertion assertion = IDLAssertion(n);
    getPath(nextArray, edges, s, assertion.getX());
    edges.push_back(assertion.getTNode());
    getPath(nextArray, edges, assertion.getY(), t);
  }
  return true;
}

} /* namepsace CVC4::theory::idl */
} /* namepsace CVC4::theory */
} /* namepsace CVC4 */

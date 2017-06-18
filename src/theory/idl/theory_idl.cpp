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
  d_propagationNegEdges(c),
  d_pathEdges(c),
  d_varList(c),
  d_propagatedLevels(c),
  d_explanations(c),
  d_distSetLevels(c),
  d_assertions(c),
  d_propagationIndices(c),
  d_valid(c),
  d_enteredLevelIdx(c)
{
  // cout << "theory IDL constructed" << endl;
}

void TheoryIdl::preRegisterTerm(TNode node) {
  Assert(node.getKind() != kind::NOT);
  if (node.isVar()) {
    d_varList.push_back(node);
    d_distances.insertAtContextLevelZero(std::make_pair(node, node), 0);
    d_valid.insertAtContextLevelZero(std::make_pair(node, node));
    d_distSetLevels.insertAtContextLevelZero(std::make_pair(node, node), 0);
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
      
      Node neg = NodeManager::currentNM()->mkNode(kind::NOT, node);
      IDLAssertion neg_idl_assertion(neg);
      TNodePair xyneg = std::make_pair(neg_idl_assertion.getX(), neg_idl_assertion.getY());
      std::vector<TNode> neg_prop_edge;
      if(d_propagationEdges.contains(xyneg)) {
	neg_prop_edge = d_propagationEdges[xyneg].get();
      }
      neg_prop_edge.push_back(neg);
      d_propagationEdges[xyneg] = neg_prop_edge;

      // cout << "registered " << node << " with corresponding neg " << neg << endl;      
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

  Assert(firstAssertionIdx < assertionIdx);

  HashGraphType graph;
  HashGraphEdgesType next;

  // level = 1;
  // firstAssertionIdx = 0;
  
  if (level > 1) {
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode x = d_varList[i];
    for (unsigned j = 0; j < d_varList.size(); ++j) {
      TNode y = d_varList[j];
      TNodePair xy = std::make_pair(x, y);
      if(d_distSetLevels.contains(xy) && d_distSetLevels[xy] < level) {
      graph[xy] = ((context::CDOhash_map<TNodePair, Integer, TNodePairHashFunction>*)((d_distances[xy]).getAtLevel(level - 1)))->get();
      next[xy] = ((context::CDOhash_map<TNodePair, TNode, TNodePairHashFunction>*)((d_pathEdges[xy]).getAtLevel(level - 1)))->get();
      }
    }
  }
  // The following are all TRUE
  // for (unsigned i = 0; i < d_varList.size(); ++i) {
  //   TNode x = d_varList[i];
  //   for (unsigned j = 0; j < d_varList.size(); ++j) {
  //     TNode y = d_varList[j];
  //     Assert(graph.count(std::make_pair(x, y)) == 1);
  //   }
  // }
  } else {
    Assert(level == 1);
    for (unsigned i = 0; i < d_varList.size(); ++i) {
      graph[std::make_pair(d_varList[i], d_varList[i])] = 0;
    }


    // These end up TRUE too
    
    //   for (unsigned i = 0; i < d_varList.size(); ++i) {
    // TNode x = d_varList[i];
    // for (unsigned j = 0; j < d_varList.size(); ++j) {
    //   TNode y = d_varList[j];
    //   Assert((x == y) ? (graph.count(std::make_pair(x, y)) == 1) : (graph.count(std::make_pair(x, y)) == 0));
    // }
    //   }

  }

  IDLAssertion orig_idl_assertion = IDLAssertion(n);

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
	  if (z == v) {
	    continue;
	  }
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

  // Assert(done);

  std::vector<TNode> reasonslist;
  Node explanation;
  bool valgp = getPath(next, reasonslist, orig_idl_assertion.getX(), orig_idl_assertion.getY());
  Assert(valgp);
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

  if (!d_enteredLevelIdx.contains(getSatContext()->getLevel())) {
    d_enteredLevelIdx.insert(getSatContext()->getLevel(), d_assertions.size());
  }
  
  // if(getSatContext()->getLevel() > d_currentLevel) {
  //   Assert(!d_enteredLevelIdx.contains(getSatContext()->getLevel()));
  //   cout << "inserting level entered " << getSatContext()->getLevel() << " with as " << d_assertions.size() << endl;

  //   // cout << "jump from lvl " << d_currentLevel << " to " << getSatContext()->getLevel() << " now assertions size is " << d_lastLeveld_JumpIdx << endl;
  //   // if (d_assertions.size() > 0) {
  //   //   cout << "the last assertion is " << d_assertions[d_assertions.size() - 1] << endl;
  //   // }
  //   d_currentLevel = getSatContext()->getLevel();
  // } else if (getSatContext()->getLevel() < d_currentLevel) {

  // }

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
      // cout << "conflict! " << assertion << endl;
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
  if( d_valid.contains(yx) && ((d_distances[yx].get() + c) < 0) ) {
    return false;
  }

  // Check whether assertion is redundant
  if (d_valid.contains(xy) && (d_distances[xy].get() <= c)) {
    return true;
  }
  
  d_assertions.push_back(assertion.getTNode()); // Add assertion to list!!!
  // cout << "pushing back assertion " << assertion.getTNode() << " now size is " << d_assertions.size() << endl;  

  // Find shortest paths incrementally
  std::vector<TNode> valid_vars;
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair yz = std::make_pair(y, z);
    TNodePair xz = std::make_pair(x, z); // TODO: eliminate double lookups
    if ( d_valid.contains(yz) && ((!d_valid.contains(xz)) || ((c + d_distances[yz].get()) < d_distances[xz].get())) ) {
      valid_vars.push_back(z);
    }
  }
  for (unsigned i = 0; i < d_varList.size(); ++i) {
    TNode z = d_varList[i];
    TNodePair zx = std::make_pair(z, x);
    TNodePair zy = std::make_pair(z, y);
    if(d_valid.contains(zx)
      && ((!d_valid.contains(zy)) || ((c + d_distances[zx].get()) < d_distances[zy].get()))) {
        for (unsigned j = 0; j < valid_vars.size(); ++j) {
          TNode v = valid_vars[j];
	  if (v == z) {
	    continue;
	  }
          TNodePair yv = std::make_pair(y, v);
          TNodePair zv = std::make_pair(z, v);
          Integer dist = c + d_distances[zx].get() + d_distances[yv].get();
          if ((!d_valid.contains(zv)) || (dist < d_distances[zv].get())) {
            if (!d_valid.contains(zv)) {
	      Assert(!d_distSetLevels.contains(zv));
              d_distSetLevels.insert(zv, getSatContext()->getLevel());
	      d_distances[zv] = dist;
	      d_valid.insert(zv);
            } else {
	      d_distances[zv] = dist;
	      
	      // cout << "updated distance " << z << " " << v << " at level" << getSatContext()->getLevel() << endl;
	      // for (unsigned lvlc = 1; lvlc <= getSatContext()->getLevel(); ++lvlc) {
	      //   cout << "\t at lvl " << lvlc << " its value was " << ((context::CDOhash_map<TNodePair, Integer, TNodePairHashFunction>*)((d_distances[zv]).getAtLevel(lvlc)))->get() << endl;
	      // }
	    }
            d_pathEdges[zv] = assertion.getTNode();
	      // for (unsigned lvlc = 1; lvlc <= getSatContext()->getLevel(); ++lvlc) {
	      //   cout << "\t at lvl " << lvlc << " pathEdges value was " << ((context::CDOhash_map<TNodePair, TNode, TNodePairHashFunction>*)((d_pathEdges[zv]).getAtLevel(lvlc)))->get() << endl;
	      // }
            // Propagate anything implied by the new shortest path
            if (d_propagationEdges.contains(zv)) {
              const std::vector<TNode>& prop_assertions = d_propagationEdges[zv].get();
              for (unsigned k = 0; k < prop_assertions.size(); ++k) {
                IDLAssertion propagation_assertion = IDLAssertion(prop_assertions[k]);
                bool value;
                if ((dist <= propagation_assertion.getC()) && !d_valuation.hasSatValue(propagation_assertion.getTNode(), value)) {
		  //		  cout << "vars are " << z << " and " << v << endl;
		  // cout << "propagating " << prop_assertions[k] << " because dist= " << dist << " <= " << propagation_assertion.getC() << endl;	  
                  d_propagatedLevels[propagation_assertion.getTNode()] = getSatContext()->getLevel();
		  // cout << "propagating at level " << getSatContext()->getLevel() << endl;
		  Assert(d_enteredLevelIdx.contains(getSatContext()->getLevel()));
		  unsigned jumpidx = d_enteredLevelIdx[getSatContext()->getLevel()];
                  d_propagationIndices[propagation_assertion.getTNode()] = std::make_pair(jumpidx, d_assertions.size());
		  // cout << "propagating a node at level " << getSatContext()->getLevel() << " with last jump index " << d_lastLevelJumpIdx << " and current idx " << d_assertions.size() << endl;
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
	    // TNodePair vz = std::make_pair(v, z);
	    // if(d_propagationNegEdges.contains(vz)) {
	    //   const std::vector<TNode>& prop_neg_assertions = d_propagationNegEdges[vz].get();
	    //   for (unsigned k = 0; k < prop_neg_assertions.size(); ++k) {
            //     IDLAssertion propagation_neg_assertion = IDLAssertion(prop_neg_assertions[k]);
            //     bool value;
	    // 	// Propagate negation!
            //     if ((propagation_neg_assertion.getC() <= dist) && !d_valuation.hasSatValue(propagation_neg_assertion.getTNode(), value)) {
	    // 	  TNode neg = prop_neg_assertions[k];
	    // 	  cout << "propagating a neg " << neg << " idlass is " << propagation_neg_assertion << endl;
            //       d_propagatedLevels[neg] = getSatContext()->getLevel();
	    // 	  Assert(d_enteredLevelIdx.contains(getSatContext()->getLevel()));
	    // 	  unsigned jumpidx = d_enteredLevelIdx[getSatContext()->getLevel()];
            //       d_propagationIndices[neg] = std::make_pair(jumpidx, d_assertions.size());
	    // 	  // cout << "propagating a node at level " << getSatContext()->getLevel() << " with last jump index " << d_lastLevelJumpIdx << " and current idx " << d_assertions.size() << endl;
            //       // cout << "adding " << propagation_assertion.getTNode() << " to prop queue at " << getSatContext()->getLevel() << endl;
            //       // std::vector<TNode> bunchaedges;
            //       // getPath(d_pathEdges, getSatContext()->getLevel(), bunchaedges,
            //       //   propagation_assertion.getX(), propagation_assertion.getY());
            //       // d_explanations[propagation_assertion.getTNode()] = bunchaedges;
            //       // cout << "propagating! " << propagation_assertion.getTNode() << " at level " << (d_pathEdges[zv]).getLevel() << endl;
            //       d_out->propagate(neg);
	    // 	}}
	    // }

	    
	  }}}}
	    

  // below ISNT true
  
  // for(unsigned i = 0; i < d_varList.size(); ++i ) {
  //   TNode x = d_varList[i];
  //   for (unsigned j = 0; j < d_varList.size(); ++j) {
  //     TNode y = d_varList[j];
  //     TNodePair xy = std::make_pair(x, y);
  //     Assert(d_valid.contains(xy));
  //   }
  // }

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

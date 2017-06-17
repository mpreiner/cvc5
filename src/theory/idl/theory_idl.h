#pragma once

#include "cvc4_private.h"

#include "theory/theory.h"

#include "idl_assertion.h"

#include "context/cdvector.h"

namespace CVC4 {
namespace theory {
namespace idl {

/**
 * Handles integer difference logic (IDL) constraints.
 */
class TheoryIdl : public Theory {

  /** Process a new assertion */
  bool processAssertion(const IDLAssertion& assertion);

  typedef std::pair<TNode, TNode> TNodePair;

  typedef context::CDHashMap<TNode, int, TNodeHashFunction> TNodeToIntCDMap;
  typedef context::CDHashMap<TNodePair, int, TNodePairHashFunction> TNodePairToIntCDMap;
  typedef context::CDHashMap<TNodePair, Integer, TNodePairHashFunction> TNodePairToIntegerCDMap;
  typedef context::CDHashMap<TNodePair, TNode, TNodePairHashFunction> TNodePairToTNodeCDMap;
  typedef context::CDHashMap<TNodePair, std::vector<TNode>, TNodePairHashFunction> TNodePairToTNodeVectorCDMap;
  typedef context::CDHashMap<TNode, std::vector<TNode>, TNodeHashFunction> TNodeToTNodeVectorCDMap;
  typedef context::CDHashMap<TNode, std::pair<unsigned, unsigned>, TNodeHashFunction> TNodeToUnsignedPairCDMap;

  typedef __gnu_cxx::hash_map<TNodePair, Integer, TNodePairHashFunction> HashGraphType;
  typedef __gnu_cxx::hash_map<TNodePair, TNode, TNodePairHashFunction> HashGraphEdgesType;
  typedef __gnu_cxx::hash_map<TNodePair, int, TNodePairHashFunction> HashGraphEdgeIdxType;

  TNodePairToTNodeCDMap d_pathEdges;
  TNodePairToIntegerCDMap d_distances;
  TNodePairToIntCDMap d_distSetLevels;

  TNodePairToTNodeVectorCDMap d_propagationEdges;
  TNodeToIntCDMap d_propagatedLevels;
  TNodeToTNodeVectorCDMap d_explanations;

  context::CDVector<TNode> d_varList;

  context::CDList<TNode> d_assertions;
  TNodeToUnsignedPairCDMap d_propagationIndices;

  bool d_levelJumped = false;
  int d_currentLevel = 0;
  int d_lastLevelJumpIdx;


  bool getPath(TNodePairToTNodeCDMap& pathedges, std::vector<TNode>& edges, TNode s, TNode t);

  bool getPath(HashGraphEdgesType& nextArray, std::vector<TNode>& edges, TNode s, TNode t);

  size_t numprops = 0;

public:

  /** Theory constructor. */
  TheoryIdl(context::Context* c, context::UserContext* u, OutputChannel& out,
            Valuation valuation, const LogicInfo& logicInfo);

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  /** Set up the solving data structures */
  void presolve();

  /** Clean up the solving data structures */
  void postsolve();
  
  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom);

  /** Check the assertions for satisfiability */
  void check(Effort effort);

  void propagate(Effort level);

  Node explain(TNode n);

  /** Identity string */
  std::string identify() const { return "THEORY_IDL"; }

};/* class TheoryIdl */

}/* CVC4::theory::idl namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

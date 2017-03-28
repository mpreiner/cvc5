/*********************                                                        */
/*! \file nl_alg.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include <map>
#include <queue>
#include <stdint.h>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/theory_arith.h"

namespace CVC4 {
namespace theory {
namespace arith {

class NonlinearExtension {
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

//monomial information (context-independent)
private:
  class MonomialIndex {
  public:
    std::map< TNode, MonomialIndex > d_data;
    std::vector< Node > d_monos;
    //status 0 : n equal, -1 : n superset, 1 : n subset
    void addTerm( TNode n, std::vector< TNode >& reps, NonlinearExtension * nla, int status = 0, unsigned argIndex = 0 ) {
      if( status==0 ){
        if( argIndex==reps.size() ){
          d_monos.push_back( n );
        }else{
          d_data[reps[argIndex]].addTerm( n, reps, nla, status, argIndex+1 );
        }
      }
      for( std::map< TNode, MonomialIndex >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
        if( status!=0 || argIndex==reps.size() || it->first!=reps[argIndex] ){
          //if we do not contain this variable, then if we were a superset, fail (-2), otherwise we are subset.
          //if we do contain this variable, then if we were equal, we are superset since variables are ordered, otherwise we remain the same.
          int new_status = std::find( reps.begin(), reps.end(), it->first )==reps.end() ? ( status>=0 ? 1 : -2 ) : ( status==0 ? -1 : status );
          if( new_status!=-2 ){
            it->second.addTerm( n, reps, nla, new_status, argIndex );
          }
        }
      }
      //compare for subsets
      for( unsigned i=0; i<d_monos.size(); i++ ){
        Node m = d_monos[i];
        if( m!=n ){
          //we are superset if we are equal and haven't traversed all variables
          int cstatus = status==0 ? ( argIndex==reps.size() ? 0 : -1 ) : status;
          Trace("nl-alg-mindex-debug") << "  compare " << n << " and " << m << ", status = " << cstatus << std::endl;
          if( cstatus<=0 && nla->isMonomialSubset( m, n ) ){
            Trace("nl-alg-mindex-debug") << "...success" << std::endl;
          }else if( cstatus>=0 && nla->isMonomialSubset( n, m ) ){
            Trace("nl-alg-mindex-debug") << "...success (rev)" << std::endl;
          }        
        }
      }
    }
  };
  std::map< Node, std::map< TNode, unsigned > > d_m_exp;
  std::map< Node, std::vector< TNode > > d_m_vlist;
  std::map< Node, unsigned > d_m_degree;
  //monomial index, by sorted variables
  MonomialIndex d_m_index;
  //list of all monomials
  std::vector< Node > d_monomials;
  //containment ordering
  std::map< Node, std::vector< Node > > d_m_contain_children;
  std::map< Node, std::vector< Node > > d_m_contain_parent;
  std::map< Node, std::map< Node, Node > > d_m_contain_mult;
  std::map< Node, std::map< Node, Node > > d_m_contain_umult;
  // ( x*y, x*z, y ) for each pair of monomials ( x*y, x*z ) with common factors
  std::map< Node, std::map< Node, Node > > d_mono_diff;
  //register monomial
  void registerMonomial( Node n );
  void setMonomialFactor( Node a, Node b, std::map< TNode, unsigned >& common );
public:
  bool isMonomialSubset( Node a, Node b );

//constraint information (context-independent)
private:
  struct ConstraintInfo {
  public:
    Node d_rhs;
    Node d_coeff;
    Kind d_type;
  };
  // if d_c_info[lit][x] = ( r, coeff, k ), then ( lit <=>  (coeff * x) <k> r ) 
  std::map< Node, std::map< Node, ConstraintInfo > > d_c_info;
  std::map< Node, std::map< Node, bool > > d_c_info_maxm;
  std::vector< Node > d_constraints;
  void registerConstraint( Node atom );

//model values/orderings
private:
  //model values
  std::map< Node, Node > d_mv[2];
  // ordering, stores variables and 0,1,-1
  std::map< unsigned, std::map< Node, unsigned > > d_order_vars;
  std::vector< Node > d_order_points;
  // index = 0 : concrete, 1 : abstract
  Node computeModelValue( Node n, unsigned index = 0 );
private:
  //cache of all lemmas sent
  NodeSet d_lemmas;
  NodeSet d_zero_split;
  bool isEntailed( Node n, bool pol );
  bool flushLemma( Node lem );
  int flushLemmas( std::vector< Node >& lemmas );
private:  //utilities
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_true;
  Node d_false;
  bool isArithKind( Kind k );
  Node mkAnd( std::vector< Node >& a );
  Node mkLit( Node a, Node b, int status, int orderType = 0 );  
  Node mkAbs( Node a );
  Kind joinKinds( Kind k1, Kind k2 );
  Kind transKinds( Kind k1, Kind k2 );
  bool hasNewMonomials( Node n, std::vector< Node >& existing, std::map< Node, bool >& visited );
  Node mkMonomialRemFactor( Node n, std::map< TNode, unsigned >& n_exp_rem );
private:
  TheoryArith& d_containing;
  //pointer to used equality engine
  eq::EqualityEngine * d_ee;
  //needs last call effort
  bool d_needsLastCall;
private:
  Node get_compare_value( Node i, unsigned orderType );
  void assignOrderIds( std::vector< Node >& vars, std::map< Node, unsigned >& d_order, unsigned orderType );
  //status 
  // 0 : equal
  // 1 : greater than or equal
  // 2 : greater than
  // -X : (less)
  //in these functions we are iterating over variables of monomials
  // initially : exp => ( oa = a ^ ob = b )
  int compareSign( Node oa, Node a, unsigned a_index, int status, std::vector< Node >& exp, std::vector< Node >& lem );
  bool compareMonomial( Node oa, Node a, std::map< TNode, unsigned >& a_exp_proc, 
                        Node ob, Node b, std::map< TNode, unsigned >& b_exp_proc, 
                        std::vector< Node >& exp, std::vector< Node >& lem,
                        std::map< int, std::map< Node, std::map< Node, Node > > >& cmp_infers );
  bool compareMonomial( Node oa, Node a, unsigned a_index, std::map< TNode, unsigned >& a_exp_proc, 
                        Node ob, Node b, unsigned b_index, std::map< TNode, unsigned >& b_exp_proc, 
                        int status, std::vector< Node >& exp, std::vector< Node >& lem,
                        std::map< int, std::map< Node, std::map< Node, Node > > >& cmp_infers );
  bool cmp_holds( Node x, Node y, std::map< Node, std::map< Node, Node > >& cmp_infers, std::vector< Node >& exp, std::map< Node, bool >& visited );
  //void traverseAndCount( std::vector< Node >& xs, Node y, std::map< Node, std::map< Node, Node > >& cmp_infers, std::map< Node, std::map< Node, unsigned > >& infer_count );
private:
  Node getSubstitutionConst( Node n, std::vector< Node >& sum, std::vector< Node >& rep_sum, Node& v,
                             std::map< Node, Node >& rep_to_const, std::map< Node, Node >& rep_to_const_exp, 
                             std::map< Node, Node >& rep_to_const_base, std::vector< Node >& r_c_exp );
  void setSubstitutionConst( Node r, Node r_c, Node r_cb, std::vector< Node >& r_c_exp, 
                             std::map< Node, std::vector< int > >& rep_to_subs_index, std::vector< Node >& vars, std::vector< Node >& subs, 
                             std::map< Node, std::vector< Node > >& exp, bool& retVal, std::map< Node, std::vector< Node > > reps_to_terms,
                             std::map< Node, int >& term_to_nconst_rep_count, std::map< Node, std::vector< Node > > reps_to_parent_terms,
                             std::map< Node, std::vector< Node > > term_to_sum, std::map< Node, std::vector< Node > > term_to_rep_sum,
                             std::map< Node, Node >& rep_to_const, std::map< Node, Node >& rep_to_const_exp, 
                             std::map< Node, Node >& rep_to_const_base );
public:
  NonlinearExtension( TheoryArith& containing, eq::EqualityEngine * ee );
  ~NonlinearExtension();
  bool getCurrentSubstitution( int effort, std::vector< Node >& vars, std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp );
  bool isExtfReduced( int effort, Node n, Node on, std::vector< Node >& exp );
  void check(Theory::Effort e);
  bool needsCheckLastEffort() { return d_needsLastCall; }
  int compare( Node i, Node j, unsigned orderType );
  int compare_value( Node i, Node j, unsigned orderType );
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

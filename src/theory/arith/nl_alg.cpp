/*********************                                                        */
/*! \file nl_alg.cpp
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

#include "theory/arith/nl_alg.h"

#include "theory/arith/theory_arith.h"
#include "theory/arith/arith_utilities.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory_model.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

void debugPrintBound( const char * c, Node coeff, Node x, Kind type, Node rhs ){
  Node t = QuantArith::mkCoeffTerm( coeff, x );
  Trace(c) << t << " " << type <<  " " << rhs;
}

struct sortNlAlg {
  sortNlAlg() : d_nla(NULL),d_order_type(0),d_reverse_order(false){}
  NlAlg * d_nla;
  unsigned d_order_type;
  bool d_reverse_order;
  bool operator() (Node i, Node j) {
    int cv = d_nla->compare( i, j, d_order_type );
    if( cv==0 ){
      return i<j;
    }else{
      return d_reverse_order ? cv<0 : cv>0;
    }
  }
};

NlAlg::NlAlg( TheoryArith& containing, eq::EqualityEngine * ee ) : 
d_lemmas( containing.getUserContext() ), d_zero_split( containing.getUserContext() ),  d_containing( containing ),  d_ee( ee ), d_needsLastCall( false ) {
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  d_neg_one = NodeManager::currentNM()->mkConst( Rational( -1 ) );
  d_order_points.push_back( d_neg_one );
  d_order_points.push_back( d_zero );
  d_order_points.push_back( d_one );
}

NlAlg::~NlAlg() {

}

bool NlAlg::isMonomialSubset( Node a, Node b ) {  
  std::map< Node, std::map< TNode, unsigned > >::iterator ita = d_m_exp.find( a );
  std::map< Node, std::map< TNode, unsigned > >::iterator itb = d_m_exp.find( b );
  Assert( ita!=d_m_exp.end() );
  Assert( itb!=d_m_exp.end() );
  for( std::map< TNode, unsigned >::iterator ita2 = ita->second.begin(); ita2 != ita->second.end(); ++ita2 ){
    std::map< TNode, unsigned >::iterator itb2 = itb->second.find( ita2->first );
    if( itb2==itb->second.end() ){
      return false;
    }else if( ita2->second>itb2->second ){
      return false;
    }
  }
  std::vector< Node > diff_children;
  for( std::map< TNode, unsigned >::iterator itb2 = itb->second.begin(); itb2 != itb->second.end(); ++itb2 ){
    std::map< TNode, unsigned >::iterator ita2 = ita->second.find( itb2->first );
    unsigned diff = itb2->second - ( ita2==ita->second.end() ? 0 : ita2->second );
    for( unsigned j=0; j<diff; j++ ){
      diff_children.push_back( itb2->first );
    }
  }
  Assert( !diff_children.empty() );
  d_m_contain_parent[a].push_back( b );
  d_m_contain_children[b].push_back( a );
  Node dterm = diff_children.size()==1 ? diff_children[0] : NodeManager::currentNM()->mkNode( kind::MULT, diff_children );
  d_m_contain_mult[a][b] = dterm;
  d_m_contain_umult[a][b] = diff_children.size()==1 ? diff_children[0] : NodeManager::currentNM()->mkNode( kind::UMULT, diff_children );
  Trace("nl-alg-mindex") << "..." << a << " is a subset of " << b << ", difference is " << dterm << std::endl;
  return true;
}

Node NlAlg::getSubstitutionConst( Node n, std::vector< Node >& sum, std::vector< Node >& rep_sum, Node& v,
                                  std::map< Node, Node >& rep_to_const, std::map< Node, Node >& rep_to_const_exp, 
                                  std::map< Node, Node >& rep_to_const_base, std::vector< Node >& r_c_exp ){
  std::vector< Node > vars;
  std::vector< Node > subs;
  std::map< Node, bool > rep_exp_proc;
  for( unsigned i=0; i<rep_sum.size(); i++ ){
    Node cr = rep_sum[i];
    std::map< Node, Node >::iterator it = rep_to_const.find( cr );
    if( it!=rep_to_const.end() ){
      if( rep_to_const_base[cr]!=sum[i] ){
        r_c_exp.push_back( rep_to_const_base[cr].eqNode( sum[i] ) );
      }
      if( rep_exp_proc.find( cr )==rep_exp_proc.end() ){
        rep_exp_proc[cr] = true;
        std::map< Node, Node >::iterator itx = rep_to_const_exp.find( cr );
        if( itx!=rep_to_const_exp.end() ){
          r_c_exp.push_back( itx->second );
        }
      }
      vars.push_back( sum[i] );
      subs.push_back( it->second );
    }else{
      v = sum[i];
    }
  }
  Node ns = n.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
  ns = Rewriter::rewrite( ns );
  return ns; 
}

void NlAlg::setSubstitutionConst( Node r, Node r_c, Node r_cb, std::vector< Node >& r_c_exp, 
                                  std::map< Node, std::vector< int > >& rep_to_subs_index, std::vector< Node >& vars, std::vector< Node >& subs, 
                                  std::map< Node, std::vector< Node > >& exp, bool& retVal, std::map< Node, std::vector< Node > > reps_to_terms,
                                  std::map< Node, int >& term_to_nconst_rep_count, std::map< Node, std::vector< Node > > reps_to_parent_terms,
                                  std::map< Node, std::vector< Node > > term_to_sum, std::map< Node, std::vector< Node > > term_to_rep_sum,
                                  std::map< Node, Node >& rep_to_const, std::map< Node, Node >& rep_to_const_exp, 
                                  std::map< Node, Node >& rep_to_const_base ){
  Trace("nl-subs-debug") << "Set constant equivalence class : " << r << " -> " << r_c << std::endl;
  rep_to_const[r] = r_c;
  Node expn;
  if( !r_c_exp.empty() ){
    expn = r_c_exp.size()==1 ? r_c_exp[0] : NodeManager::currentNM()->mkNode( kind::AND, r_c_exp );
    Trace("nl-subs-debug") << "...explanation is " << expn << std::endl;
    rep_to_const_exp[r] = expn;
  }
  rep_to_const_base[r] = r_cb;
  
  std::map< Node, std::vector< int > >::iterator iti = rep_to_subs_index.find( r );
  if( iti!=rep_to_subs_index.end() ){
    for( unsigned i=0; i<iti->second.size(); i++ ){
      int ii = iti->second[i];
      subs[ii] = r_c;
      exp[vars[ii]].clear();
      if( !expn.isNull() ){
        exp[vars[ii]].push_back( expn );
      }
      if( vars[ii]!=r_cb ){
        exp[vars[ii]].push_back( vars[ii].eqNode( r_cb ) );
      }
    }
    retVal = true;
    rep_to_subs_index.erase( r );
    if( rep_to_subs_index.empty() ){
      return;
    }
  }
  
  //new inferred constants
  std::map< Node, Node > new_const;
  std::map< Node, std::vector< Node > > new_const_exp;
  
  //parent terms now evaluate to constants
  std::map< Node, std::vector< Node > >::iterator itrp = reps_to_parent_terms.find( r );
  if( itrp!=reps_to_parent_terms.end() ){
    //Trace("nl-subs-debug") << "Look at " << itrp->second.size() << " parent terms." << std::endl;
    for( unsigned i=0; i<itrp->second.size(); i++ ){
      Node m = itrp->second[i];
      term_to_nconst_rep_count[m]--;
      Node r = d_ee->getRepresentative( m );
      if( term_to_nconst_rep_count[m]==0 ){
        if( rep_to_const.find( r )==rep_to_const.end() ){
          Trace("nl-subs-debug") << "...parent term " << m << " evaluates to constant." << std::endl;
          if( new_const.find( m )==new_const.end() ){
            Node v;
            Node m_c = getSubstitutionConst( m, term_to_sum[m], term_to_rep_sum[m], v, rep_to_const, rep_to_const_exp, rep_to_const_base, new_const_exp[m] );
            //count should be accurate
            Assert( v.isNull() );
            Assert( m_c.isConst() );
            new_const[m] = m_c;
          }
        }
      }else if( term_to_nconst_rep_count[m]==1 ){
        //check if it is now univariate solved
        std::map< Node, Node >::iterator itr = rep_to_const.find( r );
        if( itr!=rep_to_const.end() ){
          Trace("nl-subs-debug") << "...parent term " << m << " is univariate solved." << std::endl;
          std::vector< Node > const_exp;
          Node v;
          Node m_t = getSubstitutionConst( m, term_to_sum[m], term_to_rep_sum[m], v, rep_to_const, rep_to_const_exp, rep_to_const_base, const_exp );
          Node eq = m_t.eqNode( itr->second );
          Node v_c = QuantArith::solveEqualityFor( eq, v );
          if( !v_c.isNull() ){
            Assert( v_c.isConst() );
            if( new_const.find( v )==new_const.end() ){
              new_const[v] = v_c;
              new_const_exp[v].insert( new_const_exp[v].end(), const_exp.begin(), const_exp.end() );
              if( m!=rep_to_const_base[r] ){
                new_const_exp[v].push_back( m.eqNode( rep_to_const_base[r] ) ); 
              }
            }
          }
        }
      }
    }
  }
  
  
  //equal univariate terms now solved
  std::map< Node, std::vector< Node > >::iterator itt = reps_to_terms.find( r );
  if( itt!=reps_to_terms.end() ){
    for( unsigned i=0; i<itt->second.size(); i++ ){
      Node m = itt->second[i];
      if( term_to_nconst_rep_count[m]==1 ){
        Trace("nl-subs-debug") << "...term " << m << " is univariate solved." << std::endl;
        std::vector< Node > const_exp;
        Node v;
        Node m_t = getSubstitutionConst( m, term_to_sum[m], term_to_rep_sum[m], v, rep_to_const, rep_to_const_exp, rep_to_const_base, const_exp );
        Node eq = m_t.eqNode( r_c );
        Node v_c = QuantArith::solveEqualityFor( eq, v );
        if( !v_c.isNull() ){
          Assert( v_c.isConst() );
          if( new_const.find( v )==new_const.end() ){
            new_const[v] = v_c;
            new_const_exp[v].insert( new_const_exp[v].end(), const_exp.begin(), const_exp.end() );
            if( m!=r_cb ){
              new_const_exp[v].push_back( m.eqNode( r_cb ) ); 
            }
          }
        }
      }
    }
  }
  
  
  //now, process new inferred constants
  for( std::map< Node, Node >::iterator itn = new_const.begin(); itn != new_const.end(); ++itn ){
    Node m = itn->first;
    Node r = d_ee->getRepresentative( m );
    if( rep_to_const.find( r )==rep_to_const.end() ){
      setSubstitutionConst( r, itn->second, m, new_const_exp[m], 
                            rep_to_subs_index, vars, subs, exp, retVal, reps_to_terms,
                            term_to_nconst_rep_count, reps_to_parent_terms, 
                            term_to_sum, term_to_rep_sum, rep_to_const, rep_to_const_exp, rep_to_const_base );
    }
  }
}

bool NlAlg::getCurrentSubstitution( int effort, std::vector< Node >& vars, std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp ) {
  //get the constant equivalence classes
  std::map< Node, std::vector< int > > rep_to_subs_index;

  bool retVal = false;
  for( unsigned i=0; i<vars.size(); i++ ){
    Node n = vars[i];
    if( d_ee->hasTerm( n ) ){
      Node nr = d_ee->getRepresentative( n );
      if( nr.isConst() ){
        subs.push_back( nr );
        Trace("nl-subs") << "Basic substitution : " << n << " -> " << nr << std::endl;
        exp[n].push_back( n.eqNode( nr ) );
        retVal = true;
      }else{
        rep_to_subs_index[nr].push_back( i );
        subs.push_back( n );
      }
    }else{
      subs.push_back( n );
    }
  }
  
  if( options::nlAlgSolveSubs() ){
    std::map< Node, Node > rep_to_const;
    std::map< Node, Node > rep_to_const_exp;
    std::map< Node, Node > rep_to_const_base;
    
    std::map< Node, std::vector< Node > > term_to_sum;
    std::map< Node, std::vector< Node > > term_to_rep_sum;
    std::map< Node, int > term_to_nconst_rep_count;
    std::map< Node, std::vector< Node > > reps_to_parent_terms; 
    std::map< Node, std::vector< Node > > reps_to_terms; 
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( d_ee );
    while( !eqcs_i.isFinished() && !rep_to_subs_index.empty() ){
      Node r = (*eqcs_i);
      if( r.getType().isReal() ){
        Trace("nl-subs-debug") << "Process equivalence class " << r << "..." << std::endl;
        Node r_c;
        Node r_cb;
        std::vector< Node > r_c_exp;
        if( r.isConst() ){
          r_c = r;
          r_cb = r;
        }
        //scan the class
        eq::EqClassIterator eqc_i = eq::EqClassIterator( r, d_ee );
        while( !eqc_i.isFinished() ){
          Node n = (*eqc_i);
          if( !n.isConst() ){
            Trace("nl-subs-debug") << "Look at term : " << n << std::endl;
            std::map< Node, Node > msum;
            if( QuantArith::getMonomialSum( n, msum ) ){
              int nconst_count = 0;
              bool evaluatable = true;
              for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
                if( !itm->first.isNull() ){
                  if( d_ee->hasTerm( itm->first ) ){
                    Trace("nl-subs-debug") << "      ...monomial " << itm->first << std::endl;
                    Node cr = d_ee->getRepresentative( itm->first );
                    term_to_sum[n].push_back( itm->first );
                    term_to_rep_sum[n].push_back( cr );
                    if( rep_to_const.find( cr )==rep_to_const.end() ){
                      if( std::find( reps_to_parent_terms[cr].begin(), reps_to_parent_terms[cr].end(), n )==reps_to_parent_terms[cr].end() ){
                        reps_to_parent_terms[cr].push_back( n );
                        nconst_count++;
                      }
                    }
                  }else{
                    Trace("nl-subs-debug") << "...is not evaluatable due to monomial " << itm->first << std::endl;
                    evaluatable = false;
                    break;
                  }
                }
              }
              if( evaluatable ){
                Trace("nl-subs-debug") << "  ...term has " << nconst_count << " unique non-constant represenative children." << std::endl;
                if( nconst_count==0 ){
                  if( r_c.isNull() ){
                    Node v;
                    r_c = getSubstitutionConst( n, term_to_sum[n], term_to_rep_sum[n], v, rep_to_const, rep_to_const_exp, rep_to_const_base, r_c_exp );
                    r_cb = n;
                    Assert( v.isNull() );
                    Assert( r_c.isConst() );
                  }
                }else{
                  reps_to_terms[r].push_back( n );
                  term_to_nconst_rep_count[n] = nconst_count;
                }
              }
            }else{
              Trace("nl-subs-debug") << "...could not get monomial sum " << std::endl;
            }
          }
          ++eqc_i;
        }
        if( !r_c.isNull() ){
          setSubstitutionConst( r, r_c, r_cb, r_c_exp, 
                                rep_to_subs_index, vars, subs, exp, retVal, reps_to_terms,
                                term_to_nconst_rep_count, reps_to_parent_terms, term_to_sum, term_to_rep_sum, rep_to_const, rep_to_const_exp, rep_to_const_base );
        }
      }
      ++eqcs_i;
    }
  }
    
  
  //return true if the substitution is non-trivial
  return retVal;
  
  //d_containing.getValuation().getModel()->getRepresentative( n );
}

bool NlAlg::isExtfReduced( int effort, Node n, Node on, std::vector< Node >& exp ) {
/*
  if( n.isConst() ){
    return true;
  }else{
    return false;
  }
*/
  if( n==d_zero ){
    Trace("nl-alg-zero-exp") << "Infer zero : " << on << " == " << n << std::endl;
    //minimize explanation
    std::map< Node, bool > vars;
    for( unsigned i=0; i<on.getNumChildren(); i++ ){
      vars[on[i]] = true;
    }
    for( unsigned i=0; i<exp.size(); i++ ){
      Trace("nl-alg-zero-exp") << "  exp[" << i << "] = " << exp[i] << std::endl;
      std::vector< Node > eqs;
      if( exp[i].getKind()==kind::EQUAL ){
        eqs.push_back( exp[i] );
      }else if( exp[i].getKind()==kind::AND ){
        for( unsigned j=0; j<exp[i].getNumChildren(); j++ ){
          if( exp[i][j].getKind()==kind::EQUAL ){
            eqs.push_back( exp[i][j] );
          }
        }
      }
      
      for( unsigned j=0; j<eqs.size(); j++ ){
        for( unsigned r=0; r<2; r++ ){
          if( eqs[j][r]==d_zero && vars.find( eqs[j][1-r] )!=vars.end() ){
            Trace("nl-alg-zero-exp") << "...single exp : " << eqs[j] << std::endl;
            exp.clear();
            exp.push_back( eqs[j] );
            return true;
          }
        }
      }
    }
  }

  //return n!=on;
  return n.getKind()!=kind::UMULT;
}

Node NlAlg::computeModelValue( Node n, unsigned index ) {
  std::map< Node, Node >::iterator it = d_mv[index].find( n );
  if( it!=d_mv[index].end() ){
    return it->second;
  }else{
    Trace("nl-alg-debug") << "computeModelValue " << n << std::endl;
    Node ret;
    if( n.isConst() ){
      ret = n;
    }else{
      if( n.getNumChildren()==0 ){
        ret = d_containing.getValuation().getModel()->getValue( n ); 
      }else{
        if( index==1 && n.getKind()==kind::UMULT ){
          if( d_containing.getValuation().getModel()->hasTerm( n ) ){
            //use model value for abstraction
            ret = d_containing.getValuation().getModel()->getRepresentative( n );
          }else{
            //abstraction does not exist, use concrete
            ret = computeModelValue( n, 0 );
          }
        }else{
          //otherwise, compute true value
          std::vector< Node > children;
          if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
            children.push_back( n.getOperator() );
          }
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            Node mc = computeModelValue( n[i], index );
            children.push_back( mc );
          }
          ret = Rewriter::rewrite( NodeManager::currentNM()->mkNode( n.getKind(), children ) );    
          if( !ret.isConst() ){
            Trace("nl-alg-debug") << "...got non-constant : " << ret << " for " << n << ", ask model directly." << std::endl;
            ret = d_containing.getValuation().getModel()->getValue( ret );
          }
        }
      }
      if( ret.getType().isReal() && !isArithKind( n.getKind() ) ){
        //Trace("nl-alg-mv-debug") << ( index==0 ? "M" : "M_A" ) << "[ " << n << " ] -> " << ret << std::endl;
        Assert( ret.isConst() );
      }
    }
    Trace("nl-alg-debug") << "computed " << ( index==0 ? "M" : "M_A" ) << "[" << n << "] = " << ret << std::endl;
    d_mv[index][n] = ret;
    return ret;
  }
}

void NlAlg::registerMonomial( Node n ) {
  if( std::find( d_monomials.begin(), d_monomials.end(), n )==d_monomials.end() ){
    d_monomials.push_back( n );
    Trace("nl-alg-debug") << "Register monomial : " << n << std::endl;
    if( n.getKind()==kind::UMULT ){
      //get exponent count
      for( unsigned k=0; k<n.getNumChildren(); k++ ){
        d_m_exp[n][n[k]]++;
        if( k==0 || n[k]!=n[k-1] ){
          d_m_vlist[n].push_back( n[k] );
        }
      }
      d_m_degree[n] = n.getNumChildren();
    }else if( n==d_one ){
      d_m_exp[n].clear();
      d_m_vlist[n].clear();
      d_m_degree[n] = 0;
    }else{
      Assert( !isArithKind( n.getKind() ) );
      d_m_exp[n][n] = 1;
      d_m_vlist[n].push_back( n );
      d_m_degree[n] = 1;
    }
    //TODO: sort necessary here?
    std::sort( d_m_vlist[n].begin(), d_m_vlist[n].end() );
    Trace("nl-alg-mindex") << "Add monomial to index : " << n << std::endl;
    d_m_index.addTerm( n, d_m_vlist[n], this );
  }
}

void NlAlg::setMonomialFactor( Node a, Node b, std::map< TNode, unsigned >& common ) {
  if( d_mono_diff[a].find( b )==d_mono_diff[a].end() ){
    Trace("nl-alg-mono-factor") << "Set monomial factor for " << a << "/" << b << std::endl;
    d_mono_diff[a][b] = mkMonomialRemFactor( a, common );
  }
}

void NlAlg::registerConstraint( Node atom ) {
  if( std::find( d_constraints.begin(), d_constraints.end(), atom )==d_constraints.end() ){
    d_constraints.push_back( atom );
    Trace("nl-alg-debug") << "Register constraint : " << atom << std::endl;
    std::map< Node, Node > msum;
    if( QuantArith::getMonomialSumLit( atom, msum ) ){
      Trace("nl-alg-debug") << "got monomial sum: " << std::endl;
      if( Trace.isOn("nl-alg-debug") ){
        QuantArith::debugPrintMonomialSum( msum, "nl-alg-debug" );
      }
      unsigned max_degree = 0;
      std::vector< Node > all_m;
      std::vector< Node > max_deg_m;
      for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
        if( !itm->first.isNull() ){
          all_m.push_back( itm->first );
          registerMonomial( itm->first );
          Trace("nl-alg-debug2") << "...process monomial " << itm->first << std::endl;
          Assert( d_m_degree.find( itm->first )!=d_m_degree.end() );
          unsigned d = d_m_degree[itm->first];
          if( d>max_degree ){
            max_degree = d;
            max_deg_m.clear();
          }
          if( d>=max_degree ){
            max_deg_m.push_back( itm->first );
          }
        }
      }
      //isolate for each maximal degree monomial
      for( unsigned i=0; i<all_m.size(); i++ ){
        Node m = all_m[i];
        Node rhs, coeff;
        int res = QuantArith::isolate( m, msum, coeff, rhs, atom.getKind() );
        if( res!=0 ){
          Kind type = atom.getKind();
          if( res==-1 ){
            type = reverseRelationKind( type );
          }
          Trace("nl-alg-constraint") << "Constraint : " << atom << " <=> ";
          if( !coeff.isNull() ){
            Trace("nl-alg-constraint") << coeff << " * ";
          }
          Trace("nl-alg-constraint") << m << " " << type << " " << rhs << std::endl;
          d_c_info[atom][m].d_rhs = rhs;
          d_c_info[atom][m].d_coeff = coeff;
          d_c_info[atom][m].d_type = type;
        }
      }
      for( unsigned i=0; i<max_deg_m.size(); i++ ){
        Node m = max_deg_m[i];
        d_c_info_maxm[atom][m] = true;
      }
    }else{
      Trace("nl-alg-debug") << "...failed to get monomial sum." << std::endl;
    }
  }
}

bool NlAlg::isArithKind( Kind k ) {
  return k==kind::PLUS || k==kind::MULT || k==kind::UMULT;
}

Node NlAlg::mkAnd( std::vector< Node >& a ) {
  if( a.empty() ) {
    return d_true;
  } else if( a.size() == 1 ) {
    return a[0];
  } else {
    return NodeManager::currentNM()->mkNode( kind::AND, a );
  }
}

Node NlAlg::mkLit( Node a, Node b, int status, int orderType ){
  if( status==0 ){
    if( orderType==0 ){
      return a.eqNode( b );
    }else{
      //return mkAbs( a ).eqNode( mkAbs( b ) );
      return NodeManager::currentNM()->mkNode( kind::OR, a.eqNode( b ), a.eqNode( NodeManager::currentNM()->mkNode( kind::UMINUS, b ) ) );
    }
  }else if( status<0 ){
    return mkLit( b, a, -status );
  }else{
    Assert( status==1 || status==2 );
    if( orderType==0 ){
      return NodeManager::currentNM()->mkNode( status==1 ? kind::GEQ : kind::GT, a, b );
    }else{
      //return NodeManager::currentNM()->mkNode( status==1 ? kind::GEQ : kind::GT, mkAbs( a ), mkAbs( b ) );
      return NodeManager::currentNM()->mkNode( kind::ITE, NodeManager::currentNM()->mkNode( kind::GEQ, a, d_zero ),
               NodeManager::currentNM()->mkNode( kind::ITE, NodeManager::currentNM()->mkNode( kind::GEQ, b, d_zero ),
                 NodeManager::currentNM()->mkNode( status==1 ? kind::GEQ : kind::GT, a, b ),
                 NodeManager::currentNM()->mkNode( status==1 ? kind::GEQ : kind::GT, a, NodeManager::currentNM()->mkNode( kind::UMINUS, b ) ) ),
               NodeManager::currentNM()->mkNode( kind::ITE, NodeManager::currentNM()->mkNode( kind::GEQ, b, d_zero ),
                 NodeManager::currentNM()->mkNode( status==1 ? kind::GEQ : kind::GT, NodeManager::currentNM()->mkNode( kind::UMINUS, a ), b ),
                 NodeManager::currentNM()->mkNode( status==1 ? kind::GEQ : kind::LT, a, b ) ) );
                 
    }
  }
}

Node NlAlg::mkAbs( Node a ) {
  if( a.isConst() ){
    if( a==d_one || a==d_zero ){
      return a;
    }else{
      return NodeManager::currentNM()->mkConst( a.getConst<Rational>().abs() );
    }
  }else{
    return NodeManager::currentNM()->mkNode( kind::ITE, NodeManager::currentNM()->mkNode( kind::GEQ, a, d_zero ), a, NodeManager::currentNM()->mkNode( kind::UMINUS, a ) );
  }
}

// by a <k1> b, a <k2> b, we know a <ret> b
Kind NlAlg::joinKinds( Kind k1, Kind k2 ) {
  if( k2<k1 ){
    return joinKinds( k2, k1 );
  }else if( k1==k2 ){
    return k1;
  }else{
    Assert( k1==kind::EQUAL || k1==kind::LT || k1==kind::LEQ || k1==kind::GT || k1==kind::GEQ );
    Assert( k2==kind::EQUAL || k2==kind::LT || k2==kind::LEQ || k2==kind::GT || k2==kind::GEQ );
    if( k1==kind::EQUAL ){
      if( k2==kind::LEQ || k2==kind::GEQ ){
        return k1;
      }
    }else if( k1==kind::LT ){
      if( k2==kind::LEQ ){
        return k1;
      }
    }else if( k1==kind::LEQ ){
      if( k2==kind::GEQ ){
        return kind::EQUAL;
      }
    }else if( k1==kind::GT ){
      if( k2==kind::GEQ ){
        return k1;
      }
    }
    return UNDEFINED_KIND;
  }
}

// by a <k1> b, b <k2> c, we know a <ret> c
Kind NlAlg::transKinds( Kind k1, Kind k2 ) {
  if( k2<k1 ){
    return transKinds( k2, k1 );
  }else if( k1==k2 ){
    return k1;
  }else{
    Assert( k1==kind::EQUAL || k1==kind::LT || k1==kind::LEQ || k1==kind::GT || k1==kind::GEQ );
    Assert( k2==kind::EQUAL || k2==kind::LT || k2==kind::LEQ || k2==kind::GT || k2==kind::GEQ );
    if( k1==kind::EQUAL ){
      return k2;
    }else if( k1==kind::LT ){
      if( k2==kind::LEQ ){
        return k1;
      }
    }else if( k1==kind::GT ){
      if( k2==kind::GEQ ){
        return k1;
      }
    }
    return UNDEFINED_KIND;
  }
}

bool NlAlg::hasNewMonomials( Node n, std::vector< Node >& existing, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==kind::UMULT ){
      return std::find( existing.begin(), existing.end(), n )==existing.end();
    }else{
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( hasNewMonomials( n[i], existing, visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}

Node NlAlg::mkMonomialRemFactor( Node n, std::map< TNode, unsigned >& n_exp_rem ) {
  std::vector< Node > children;  
  std::map< Node, std::map< TNode, unsigned > >::iterator itme = d_m_exp.find( n );
  Assert( itme!=d_m_exp.end() );
  for( std::map< TNode, unsigned >::iterator itme2 = itme->second.begin(); itme2 != itme->second.end(); ++itme2 ){
    unsigned inc = itme2->second;
    Node v = itme2->first;
    Trace("nl-alg-mono-factor") << "..." << inc << " factors of " << v << std::endl;
    std::map< TNode, unsigned >::iterator itr = n_exp_rem.find( v );
    if( itr!=n_exp_rem.end() ){
      Assert( itr->second<=inc );
      inc = inc - itr->second;
      Trace("nl-alg-mono-factor") << "......rem, now " << inc << " factors of " << v << std::endl;
    }
    for( unsigned j=0; j<inc; j++ ){
      children.push_back( v );
    }
  }
  Node ret = children.empty() ? d_one : ( children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::MULT, children ) );
  ret = Rewriter::rewrite( ret );
  Trace("nl-alg-mono-factor") << "...return : " << ret << std::endl;
  return ret;
}
 
bool NlAlg::flushLemma( Node lem ) {
  Trace("nl-alg-lemma-debug") << "NlAlg::Lemma pre-rewrite : " << lem << std::endl;
  lem = Rewriter::rewrite( lem );
  if( d_lemmas.find( lem )==d_lemmas.end() ){
    d_lemmas.insert( lem );
    Trace("nl-alg-lemma") << "NlAlg::Lemma : " << lem << std::endl;
    d_containing.getOutputChannel().lemma( lem );
    return true;
  }else{
    Trace("nl-alg-lemma-debug") << "NlAlg::Lemma duplicate : " << lem << std::endl;
    //should not generate duplicates
    //Assert( false );
    return false;
  }
}

int NlAlg::flushLemmas( std::vector< Node >& lemmas ) {
  if( options::nlAlgEntailConflicts() ){
    //check if any are entailed to be false
    for( unsigned i=0; i<lemmas.size(); i++ ){
      Node ch_lemma = lemmas[i].negate();
      ch_lemma = Rewriter::rewrite( ch_lemma );
      Trace("nl-alg-et-debug") << "Check entailment of " << ch_lemma << "..." << std::endl;
      std::pair<bool, Node> et = d_containing.getValuation().entailmentCheck(THEORY_OF_TYPE_BASED, ch_lemma );
      Trace("nl-alg-et-debug") << "entailment test result : " << et.first << " " << et.second << std::endl;
      if( et.first ){
        Trace("nl-alg-et") << "*** Lemma entailed to be in conflict : " << lemmas[i] << std::endl;
        //return just this lemma
        if( flushLemma( lemmas[i] ) ){
          lemmas.clear();
          return 1;
        }
      }
    }
  }

  int sum = 0;
  for( unsigned i=0; i<lemmas.size(); i++ ){
    if( flushLemma( lemmas[i] ) ){
      sum++;
    }
  }
  lemmas.clear();
  return sum;
}

void NlAlg::check(Theory::Effort e) {
  Trace("nl-alg") << std::endl;
  Trace("nl-alg") << "NlAlg::check, effort = " << e << std::endl;
  if( e==Theory::EFFORT_FULL ){
    d_containing.getExtTheory()->clearCache();
    d_needsLastCall = true;
    if( options::nlAlgRewrites() ){
      std::vector< Node > nred;
      if( !d_containing.getExtTheory()->doInferences( 0, nred ) ){
        Trace("nl-alg") << "...sent no lemmas, # extf to reduce = " << nred.size() << std::endl;
        if( nred.empty() ){
          d_needsLastCall = false;
        }
      }else{
        Trace("nl-alg") << "...sent lemmas." << std::endl;
      }
    }
  }else{
    d_mv[0].clear();
    d_mv[1].clear();
    Assert( e==Theory::EFFORT_LAST_CALL );
    bool setIncomplete = false;
    Trace("nl-alg-mv") << "Getting model values... check for [model-false]" << std::endl;
    std::vector< Node > asserts;
    std::map< Node, bool > false_asserts;
    for( context::CDList<Assertion>::const_iterator it = d_containing.facts_begin(); it != d_containing.facts_end(); ++ it) {
      Node lit = (*it).assertion;
      asserts.push_back( lit );
      Node litv = computeModelValue( lit );
      Trace("nl-alg-mv") << "M[[ " << lit << " ]] -> " << litv;
      if( litv!=d_true ){
        Trace("nl-alg-mv") << " [model-false]" << std::endl;
        Assert( litv==d_false );
        setIncomplete = true;
        Trace("nl-alg-mv") << "...will set incomplete." << std::endl;
        false_asserts[lit] = true;
      }else{
        Trace("nl-alg-mv") << std::endl;
      }
    }
    if( setIncomplete ){
      //processed monomials
      std::map< Node, bool > ms_proc;
    
      //list of monomials
      std::vector< Node > ms;
      d_containing.getExtTheory()->getTerms( ms );
      //list of variables occurring in monomials
      std::vector< Node > ms_vars;
      
      //register monomials
      Trace("nl-alg-mv") << "Monomials : " << std::endl;
      for( unsigned j=0; j<ms.size(); j++ ){
        Node a = ms[j];
        registerMonomial( a );
        computeModelValue( a, 0 );
        computeModelValue( a, 1 );
        Assert( d_mv[1][ a ].isConst() );
        Assert( d_mv[0][ a ].isConst() );
        Trace("nl-alg-mv") << "  " << a << " -> " << d_mv[1][ a ] << " [" << d_mv[0][ a ] << "]" << std::endl;
        
        std::map< Node, std::vector< TNode > >::iterator itvl = d_m_vlist.find( a );
        Assert( itvl!=d_m_vlist.end() );
        for( unsigned k=0; k<itvl->second.size(); k++ ){
          if( std::find( ms_vars.begin(), ms_vars.end(), itvl->second[k] )==ms_vars.end() ){
            ms_vars.push_back( itvl->second[k] );
          }
        }
        /*
        //mark processed if has a "one" factor (will look at reduced monomial)
        std::map< Node, std::map< TNode, unsigned > >::iterator itme = d_m_exp.find( a );
        Assert( itme!=d_m_exp.end() );
        for( std::map< TNode, unsigned >::iterator itme2 = itme->second.begin(); itme2 != itme->second.end(); ++itme2 ){
          Node v = itme->first;
          Assert( d_mv[0].find( v )!=d_mv[0].end() );
          Node mvv = d_mv[0][ v ];
          if( mvv==d_one || mvv==d_neg_one ){
            ms_proc[ a ] = true;
            Trace("nl-alg-mv") << "...mark " << a << " reduced since has 1 factor." << std::endl;
            break;
          }
        }
        */
      }
    
      //register constants
      registerMonomial( d_one );
      for( unsigned j=0; j<d_order_points.size(); j++ ){
        Node c = d_order_points[j];
        computeModelValue( c, 0 );
        computeModelValue( c, 1 );
      }

      int lemmas_proc;
      std::vector< Node > lemmas;
      
      //register variables (possibly do zero splits)
      Trace("nl-alg-mv") << "Variables : " << std::endl;
      Trace("nl-alg") << "Get zero split lemmas..." << std::endl;
      for( unsigned i=0; i<ms_vars.size(); i++ ){
        Node v = ms_vars[i];
        registerMonomial( v );
        computeModelValue( v, 0 );
        computeModelValue( v, 1 );
        Trace("nl-alg-mv") << "  " << v << " -> " << d_mv[0][ v ] << std::endl;
        if( options::nlAlgSplitZero() ){
          //split on zero?  
          if( d_zero_split.find( v )==d_zero_split.end() ){
            d_zero_split.insert( v );
            Node lem = v.eqNode( d_zero );
            lem = Rewriter::rewrite( lem );
            d_containing.getValuation().ensureLiteral( lem );
            d_containing.getOutputChannel().requirePhase( lem, true );
            lem = NodeManager::currentNM()->mkNode( kind::OR, lem, lem.negate() );
            lemmas.push_back( lem );
          }
        }
      }
      lemmas_proc = flushLemmas( lemmas );
      if( lemmas_proc>0 ){
        Trace("nl-alg") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
        return;
      }

            
      //------------------------------------------------------------------------lemmas based on sign (comparison to zero)
      std::map< Node, int > signs;
      Trace("nl-alg") << "Get sign lemmas..." << std::endl;
      for( unsigned j=0; j<ms.size(); j++ ){
        Node a = ms[j];
        if( ms_proc.find( a )==ms_proc.end() ){
          std::vector< Node > exp;
          Trace("nl-alg-debug") << "  process " << a << "..." << std::endl;
          signs[a] = compareSign( a, a, 0, 1, exp, lemmas );
          if( signs[a]==0 ){
            ms_proc[a] = true;
            Trace("nl-alg-mv") << "...mark " << a << " reduced since its value is 0." << std::endl;
          }
        }
      }
      lemmas_proc = flushLemmas( lemmas );
      if( lemmas_proc>0 ){
        Trace("nl-alg") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
        return;
      }
      
      //---------------------------------------------------------------------lemmas based on magnitude of non-zero monomials
      for( unsigned r=1; r<=1; r++ ){
        assignOrderIds( ms_vars, d_order_vars[r], r );
       
        //sort individual variable lists
        sortNlAlg smv;
        smv.d_nla = this;
        smv.d_order_type = r;
        smv.d_reverse_order = true;
        for( unsigned j=0; j<ms.size(); j++ ){
          std::sort( d_m_vlist[ ms[j] ].begin(), d_m_vlist[ ms[j] ].end(), smv );
        }
        for( unsigned c=0; c<3; c++ ){
          //if (x,y,L) in cmp_infers, then x > y inferred as conclusion of L in lemmas
          std::map< int, std::map< Node, std::map< Node, Node > > > cmp_infers;
          Trace("nl-alg") << "Get comparison lemmas (order=" << r << ", compare=" << c << ")..." << std::endl;
          for( unsigned j=0; j<ms.size(); j++ ){
            Node a = ms[j];
            if( ms_proc.find( a )==ms_proc.end() ){
              if( c==0 ){
                //compare magnitude against 1
                std::vector< Node > exp;
                std::map< TNode, unsigned > a_exp_proc;
                std::map< TNode, unsigned > b_exp_proc;
                compareMonomial( a, a, a_exp_proc, d_one, d_one, b_exp_proc, exp, lemmas, cmp_infers );
              }else{
                std::map< Node, std::map< TNode, unsigned > >::iterator itmea = d_m_exp.find( a );
                Assert( itmea!=d_m_exp.end() );
                if( c==1 ){
                  //TODO : not just against containing variables?
                  //compare magnitude against variables
                  for( unsigned k=0; k<ms_vars.size(); k++ ){
                    Node v = ms_vars[k];
                    std::vector< Node > exp;
                    std::map< TNode, unsigned > a_exp_proc;
                    std::map< TNode, unsigned > b_exp_proc;
                    if( itmea->second.find( v )!=itmea->second.end() ){
                      a_exp_proc[v] = 1;
                      b_exp_proc[v] = 1;
                      setMonomialFactor( a, v, a_exp_proc );
                      setMonomialFactor( v, a, b_exp_proc );
                      compareMonomial( a, a, a_exp_proc, v, v, b_exp_proc, exp, lemmas, cmp_infers );
                    }
                  }
                }else{
                  //compare magnitude against other non-linear monomials
                  for( unsigned k=(j+1); k<ms.size(); k++ ){
                    Node b = ms[k];
                    //(signs[a]==signs[b])==(r==0)
                    if( ms_proc.find( b )==ms_proc.end() ){
                      std::map< Node, std::map< TNode, unsigned > >::iterator itmeb = d_m_exp.find( b );
                      Assert( itmeb!=d_m_exp.end() );
                      
                      std::vector< Node > exp;
                      //take common factors of monomials, set minimum of common exponents as processed
                      std::map< TNode, unsigned > a_exp_proc;
                      std::map< TNode, unsigned > b_exp_proc;
                      for( std::map< TNode, unsigned >::iterator itmea2 = itmea->second.begin(); itmea2 != itmea->second.end(); ++itmea2 ){
                        std::map< TNode, unsigned >::iterator itmeb2 = itmeb->second.find( itmea2->first );
                        if( itmeb2!=itmeb->second.end() ){
                          unsigned min_exp = itmea2->second>itmeb2->second ? itmeb2->second : itmea2->second;
                          a_exp_proc[ itmea2->first ] = min_exp;
                          b_exp_proc[ itmea2->first ] = min_exp;
                          Trace("nl-alg-comp") << "Common exponent : " << itmea2->first << " : " << min_exp << std::endl;
                        }
                      }
                      if( !a_exp_proc.empty() ){
                        setMonomialFactor( a, b, a_exp_proc );
                        setMonomialFactor( b, a, b_exp_proc );
                      }
                      /*
                      if( !a_exp_proc.empty() ){
                        //reduction based on common exponents a > 0 => ( a * b <> a * c <=> b <> c ), a < 0 => ( a * b <> a * c <=> b !<> c )  ?
                      }else{
                        compareMonomial( a, a, a_exp_proc, b, b, b_exp_proc, exp, lemmas );
                      }
                      */
                      compareMonomial( a, a, a_exp_proc, b, b, b_exp_proc, exp, lemmas, cmp_infers );
                    }
                  }
                }
              }
            }
          }
          //remove redundant lemmas, e.g. if a > b, b > c, a > c were inferred, discard lemma with conclusion a > c
          Trace("nl-alg-comp") << "Compute redundancies for " << lemmas.size() << " lemmas." << std::endl;
          //naive          
          std::vector< Node > r_lemmas;
          for( std::map< int, std::map< Node, std::map< Node, Node > > >::iterator itb = cmp_infers.begin(); itb != cmp_infers.end(); ++itb ){
            for( std::map< Node, std::map< Node, Node > >::iterator itc = itb->second.begin(); itc != itb->second.end(); ++itc ){
              for( std::map< Node, Node >::iterator itc2 = itc->second.begin(); itc2 != itc->second.end(); ++itc2 ){
                std::map< Node, bool > visited;
                for( std::map< Node, Node >::iterator itc3 = itc->second.begin(); itc3 != itc->second.end(); ++itc3 ){
                  if( itc3->first!=itc2->first ){
                    std::vector< Node > exp;
                    if( cmp_holds( itc3->first, itc2->first, itb->second, exp, visited ) ){
                      r_lemmas.push_back( itc2->second );
                      Trace("nl-alg-comp") << "...inference of " << itc->first << " > " << itc2->first << " was redundant." << std::endl;
                      break;
                    }
                  }
                }
              }
            }
          }
          std::vector< Node > nr_lemmas;
          for( unsigned i=0; i<lemmas.size(); i++ ){
            if( std::find( r_lemmas.begin(), r_lemmas.end(), lemmas[i] )==r_lemmas.end() ){
              nr_lemmas.push_back( lemmas[i] );
            }
          }
          //TODO: only take maximal lower/minimial lower bounds?
          
          
          
          Trace("nl-alg-comp") << nr_lemmas.size() << " / " << lemmas.size() << " were non-redundant." << std::endl;
          lemmas_proc = flushLemmas( nr_lemmas );
          if( lemmas_proc>0 ){
            Trace("nl-alg") << "  ...finished with " << lemmas_proc << " new lemmas (out of possible " << lemmas.size() << ")." << std::endl;
            return;
          }
          
        }
      }

      //sort monomials by degree
      sortNlAlg snlad;
      snlad.d_nla = this;
      snlad.d_order_type = 4;
      snlad.d_reverse_order = false;
      std::sort( ms.begin(), ms.end(), snlad );
      //all monomials
      std::vector< Node > terms;
      terms.insert( terms.end(), ms_vars.begin(), ms_vars.end() );
      terms.insert( terms.end(), ms.begin(), ms.end() );

      // term -> coeff -> rhs -> ( status, exp, b ), 
      //   where we have that : exp =>  ( coeff * term <status> rhs )
      //   b is true if degree( term ) >= degree( rhs )
      std::map< Node, std::map< Node, std::map< Node, Kind > > > ci;
      std::map< Node, std::map< Node, std::map< Node, Node > > > ci_exp;
      std::map< Node, std::map< Node, std::map< Node, bool > > > ci_max;
      
      // If ( m, p1, true ), then it would help satisfiability if m were ( > if p1=true, < if p1=false )
      std::map< Node, std::map< bool, bool > > tplane_refine_dir;

      //register constraints
      Trace("nl-alg-debug") << "Register bound constraints..." << std::endl;
      for( context::CDList<Assertion>::const_iterator it = d_containing.facts_begin(); it != d_containing.facts_end(); ++ it) {
        Node lit = (*it).assertion;
        bool polarity = lit.getKind()!=kind::NOT;
        Node atom = lit.getKind()==kind::NOT ? lit[0] : lit;
        registerConstraint( atom );
        bool is_false_lit = false_asserts.find( lit )!=false_asserts.end();
        //add information about bounds to variables
        std::map< Node, std::map< Node, ConstraintInfo > >::iterator itc = d_c_info.find( atom );
        std::map< Node, std::map< Node, bool > >::iterator itcm = d_c_info_maxm.find( atom );
        if( itc!=d_c_info.end() ) {
          Assert( itcm!=d_c_info_maxm.end() );
          for( std::map< Node, ConstraintInfo >::iterator itcc = itc->second.begin(); itcc != itc->second.end(); ++itcc ){
            Node x = itcc->first;
            Node coeff = itcc->second.d_coeff;
            Node rhs = itcc->second.d_rhs;
            Kind type = itcc->second.d_type;
            Node exp = lit;
            if( !polarity ){
              //reverse 
              if( type==kind::EQUAL ){
                //we will take the strict inequality in the direction of the model
                Node lhs = QuantArith::mkCoeffTerm( coeff, x );
                Node query = NodeManager::currentNM()->mkNode( kind::GT, lhs, rhs );
                Node query_mv = computeModelValue( query, 1 );
                if( query_mv==d_true ){
                  exp = query;
                  type = kind::GT;
                }else{
                  Assert( query_mv==d_false );
                  exp = NodeManager::currentNM()->mkNode( kind::LT, lhs, rhs );
                  type = kind::LT;
                }
              }else{
                type = negateKind( type );
              }
            }
            //add to status if maximal degree
            ci_max[x][coeff][rhs] = itcm->second.find( x )!=itcm->second.end();
            if( Trace.isOn("nl-alg-bound-debug2") ){
              Node t = QuantArith::mkCoeffTerm( coeff, x );
              Trace("nl-alg-bound-debug2") << "Add Bound: " << t << " " << type <<  " " << rhs << " by " << exp << std::endl;
            }
            bool updated = true;
            std::map< Node, Kind >::iterator its = ci[x][coeff].find( rhs );
            if( its==ci[x][coeff].end() ){
              ci[x][coeff][rhs] = type;
              ci_exp[x][coeff][rhs] = exp;
            }else if( type!=its->second ){
              Trace("nl-alg-bound-debug2") << "Joining kinds : " << type << " " << its->second << std::endl;
              Kind jk = joinKinds( type, its->second );
              if( jk==kind::UNDEFINED_KIND ){
                updated = false;
              }else if( jk!=its->second ){
                if( jk==type ){
                  ci[x][coeff][rhs] = type;
                  ci_exp[x][coeff][rhs] = exp;
                }else{
                  ci[x][coeff][rhs] = jk;
                  ci_exp[x][coeff][rhs] = NodeManager::currentNM()->mkNode( kind::AND, ci_exp[x][coeff][rhs], exp );
                }
              }else{
                updated = false;
              }
            }
            if( Trace.isOn("nl-alg-bound") ){
              if( updated ){
                Trace("nl-alg-bound") << "Bound: ";
                debugPrintBound( "nl-alg-bound", coeff, x, ci[x][coeff][rhs], rhs );
                Trace("nl-alg-bound") << " by " << ci_exp[x][coeff][rhs];
                if( ci_max[x][coeff][rhs] ){
                  Trace("nl-alg-bound") << ", is max degree";
                }
                Trace("nl-alg-bound") << std::endl;
              }
            }
            //compute if bound is not satisfied, and store what is required for a possible refinement
            if( options::nlAlgTangentPlanes() ){
              if( is_false_lit ){
                Node rhs_v = computeModelValue( rhs, 0 );
                Node x_v = computeModelValue( x, 0 );
                bool needsRefine = false;
                bool refineDir;
                if( rhs_v==x_v ){
                  if( type==kind::GT ){
                    needsRefine = true;refineDir = true;
                  }else if( type==kind::LT ){
                    needsRefine = true;refineDir = false;
                  }
                }else if( x_v.getConst<Rational>()>rhs_v.getConst<Rational>() ){
                  if( type!=kind::GT && type!=kind::GEQ ){
                    needsRefine = true;refineDir = false;
                  }
                }else{
                  if( type!=kind::LT && type!=kind::LEQ ){
                    needsRefine = true;refineDir = true;
                  }
                }
                Trace("nl-alg-tplanes-cons-debug") << "...compute if bound corresponds to a required refinement" << std::endl;
                Trace("nl-alg-tplanes-cons-debug") << "...M[" << x << "] = " << x_v << ", M[" << rhs << "] = " << rhs_v << std::endl;
                Trace("nl-alg-tplanes-cons-debug") << "...refine = " << needsRefine << "/" << refineDir << std::endl;
                if( needsRefine ){
                  Trace("nl-alg-tplanes-cons") << "---> By " << lit << " and since M[" << x << "] = " << x_v << ", M[" << rhs << "] = " << rhs_v << ", ";
                  Trace("nl-alg-tplanes-cons") << "monomial " << x << " should be " << ( refineDir ? "larger" : "smaller" ) << std::endl;
                  tplane_refine_dir[x][refineDir] = true;
                }
              }
            }
          }
        }
      }
      //reflexive constraints
      Node null_coeff;
      for( unsigned j=0; j<terms.size(); j++ ){
        Node n = terms[j];
        ci[n][null_coeff][n] = kind::EQUAL;
        ci_exp[n][null_coeff][n] = d_true;
        ci_max[n][null_coeff][n] = false;
      }
      
      //-----------------------------------------------------------------------------------------inferred bounds lemmas, e.g. x >= t => y*x >= y*t
      Trace("nl-alg") << "Get inferred bound lemmas..." << std::endl;
      
      std::vector< Node > nt_lemmas;
      for( unsigned k=0; k<terms.size(); k++ ){
        Node x = terms[k];
        Trace("nl-alg-bound-debug") << "Process bounds for " << x << " : " << std::endl;
        std::map< Node, std::vector< Node > >::iterator itm = d_m_contain_parent.find( x );
        if( itm!=d_m_contain_parent.end() ){
          Trace("nl-alg-bound-debug") << "...has " << itm->second.size() << " parent monomials." << std::endl;
          //check derived bounds
          std::map< Node, std::map< Node, std::map< Node, Kind > > >::iterator itc = ci.find( x );
          if( itc!=ci.end() ){
            for( std::map< Node, std::map< Node, Kind > >::iterator itcc = itc->second.begin(); itcc != itc->second.end(); ++itcc ){
              Node coeff = itcc->first;
              Node t = QuantArith::mkCoeffTerm( coeff, x );
              for( std::map< Node, Kind >::iterator itcr = itcc->second.begin(); itcr != itcc->second.end(); ++itcr ){
                Node rhs = itcr->first;
                // only consider this bound if maximal degree
                if( ci_max[x][coeff][rhs] ){
                  Kind type = itcr->second;
                  for( unsigned j=0; j<itm->second.size(); j++ ){
                    Node y = itm->second[j];
                    Assert( d_m_contain_mult[x].find( y )!=d_m_contain_mult[x].end() );
                    Node mult = d_m_contain_mult[x][y];
                    // x <k> t => m*x <k'> t  where y = m*x
                    // get the sign of mult
                    Node mmv = computeModelValue( mult );
                    Trace("nl-alg-bound-debug2") << "Model value of " << mult << " is " << mmv << std::endl;
                    Assert( mmv.isConst() );
                    int mmv_sign = mmv.getConst<Rational>().sgn();
                    Trace("nl-alg-bound-debug2") << "  sign of " << mmv << " is " << mmv_sign << std::endl;
                    if( mmv_sign!=0 ){
                      Trace("nl-alg-bound-debug") << "  from " << x << " * " << mult << " = " << y << " and " << t << " " << type << " " << rhs << ", infer : " << std::endl;
                      Kind infer_type = mmv_sign==-1 ? reverseRelationKind( type ) : type;  
                      Node infer_lhs = NodeManager::currentNM()->mkNode( kind::MULT, mult, t );
                      Node infer_rhs = NodeManager::currentNM()->mkNode( kind::MULT, mult, rhs );
                      Node infer = NodeManager::currentNM()->mkNode( infer_type, infer_lhs, infer_rhs );
                      Trace("nl-alg-bound-debug") << "     " << infer << std::endl;
                      infer = Rewriter::rewrite( infer );
                      Trace("nl-alg-bound-debug2") << "     ...rewritten : " << infer << std::endl;
                      //check whether it is false in model for abstraction
                      Node infer_mv = computeModelValue( infer, 1 );
                      Trace("nl-alg-bound-debug") << "       ...infer model value is " << infer_mv << std::endl;
                      if( infer_mv==d_false ){
                        Node exp = NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode( mmv_sign==1 ? kind::GT : kind::LT, mult, d_zero ), ci_exp[x][coeff][rhs] );
                        Node iblem = NodeManager::currentNM()->mkNode( kind::IMPLIES, exp, infer );
                        Node pr_iblem = iblem;
                        iblem = Rewriter::rewrite( iblem );
                        std::map< Node, bool > visited;
                        bool introNewTerms = hasNewMonomials( iblem, ms, visited );
                        Trace("nl-alg-bound-lemma") << "*** Bound inference lemma : " << iblem << " (pre-rewrite : " << pr_iblem << ")" << std::endl;
                        //Trace("nl-alg-bound-lemma") << "       intro new monomials = " << introNewTerms << std::endl;
                        if( !introNewTerms ){
                          lemmas.push_back( iblem );
                        }else{
                          nt_lemmas.push_back( iblem );
                        }
                      }
                    }else{
                      Trace("nl-alg-bound-debug") << "     ...coefficient " << mult << " is zero." << std::endl;
                    }
                  }
                }
              }
            }
          }
        }else{
          Trace("nl-alg-bound-debug") << "...has no parent monomials." << std::endl;
        }
      }
      //Trace("nl-alg") << "Bound lemmas : " << lemmas.size() << ", " << nt_lemmas.size() << std::endl;
      //prioritize lemmas that do not introduce new monomials 
      lemmas_proc = flushLemmas( lemmas );
      if( lemmas_proc>0 ){
        Trace("nl-alg") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
        return;
      }
      
      //------------------------------------resolution bound inferences, e.g.  ( y>=0 ^ s <= x*z ^ x*y <= t ) => y*s <= z*t
      if( options::nlAlgResBound() ){
        Trace("nl-alg") << "Get resolution inferred bound lemmas..." << std::endl;
        for( unsigned j=0; j<terms.size(); j++ ){
          Node a = terms[j];
          std::map< Node, std::map< Node, std::map< Node, Kind > > >::iterator itca = ci.find( a );
          if( itca!=ci.end() ){
            for( unsigned k=(j+1); k<terms.size(); k++ ){
              Node b = terms[k];
              std::map< Node, std::map< Node, std::map< Node, Kind > > >::iterator itcb = ci.find( b );
              if( itcb!=ci.end() ){
                Trace("nl-alg-rbound-debug") << "resolution inferences : compare " << a << " and " << b << std::endl;
                //if they have common factors
                std::map< Node, Node >::iterator ita = d_mono_diff[a].find( b );
                if( ita!=d_mono_diff[a].end() ){
                  std::map< Node, Node >::iterator itb = d_mono_diff[b].find( a );
                  Assert( itb!=d_mono_diff[b].end() );
                  Node mv_a = computeModelValue( ita->second, 1 );
                  Assert( mv_a.isConst() );
                  int mv_a_sgn = mv_a.getConst<Rational>().sgn();
                  Assert( mv_a_sgn!=0 );
                  Node mv_b = computeModelValue( itb->second, 1 );
                  Assert( mv_b.isConst() );
                  int mv_b_sgn = mv_b.getConst<Rational>().sgn();
                  Assert( mv_b_sgn!=0 );
                  Trace("nl-alg-rbound") << "Get resolution inferences for [a] " << a << " vs [b] " << b << std::endl;
                  Trace("nl-alg-rbound") << "  [a] factor is " << ita->second << ", sign in model = " << mv_a_sgn << std::endl;
                  Trace("nl-alg-rbound") << "  [b] factor is " << itb->second << ", sign in model = " << mv_b_sgn << std::endl;
                  
                  std::vector< Node > exp;
                  //bounds of a
                  for( std::map< Node, std::map< Node, Kind > >::iterator itcac = itca->second.begin(); itcac != itca->second.end(); ++itcac ){
                    Node coeff_a = itcac->first;
                    for( std::map< Node, Kind >::iterator itcar = itcac->second.begin(); itcar != itcac->second.end(); ++itcar ){
                      Node rhs_a = itcar->first;
                      Node rhs_a_res_base = NodeManager::currentNM()->mkNode( kind::MULT, itb->second, rhs_a );
                      rhs_a_res_base = Rewriter::rewrite( rhs_a_res_base );
                      std::map< Node, bool > visited_a;
                      if( !hasNewMonomials( rhs_a_res_base, ms, visited_a ) ){
                        Kind type_a = itcar->second;
                        exp.push_back( ci_exp[a][coeff_a][rhs_a] );
                      
                        //bounds of b
                        for( std::map< Node, std::map< Node, Kind > >::iterator itcbc = itcb->second.begin(); itcbc != itcb->second.end(); ++itcbc ){
                          Node coeff_b = itcbc->first;
                          Node rhs_a_res = QuantArith::mkCoeffTerm( coeff_b, rhs_a_res_base );
                          for( std::map< Node, Kind >::iterator itcbr = itcbc->second.begin(); itcbr != itcbc->second.end(); ++itcbr ){
                            Node rhs_b = itcbr->first;
                            Node rhs_b_res = NodeManager::currentNM()->mkNode( kind::MULT, ita->second, rhs_b );
                            rhs_b_res = QuantArith::mkCoeffTerm( coeff_a, rhs_b_res );
                            rhs_b_res = Rewriter::rewrite( rhs_b_res );
                            std::map< Node, bool > visited_b;
                            if( !hasNewMonomials( rhs_b_res, ms, visited_b ) ){
                              Kind type_b = itcbr->second;
                              exp.push_back( ci_exp[b][coeff_b][rhs_b] );
                              if( Trace.isOn("nl-alg-rbound") ){
                                Trace("nl-alg-rbound") << "* try bounds : ";
                                debugPrintBound( "nl-alg-rbound", coeff_a, a, type_a, rhs_a );
                                Trace("nl-alg-rbound") << std::endl;
                                Trace("nl-alg-rbound") << "               ";
                                debugPrintBound( "nl-alg-rbound", coeff_b, b, type_b, rhs_b );
                                Trace("nl-alg-rbound") << std::endl;
                              }
                              Kind types[2];
                              for( unsigned r=0; r<2; r++ ){
                                Node pivot_factor = r==0 ? itb->second : ita->second;
                                int pivot_factor_sign = r==0 ? mv_b_sgn : mv_a_sgn;
                                types[r] = r==0 ? type_a : type_b;
                                if( pivot_factor_sign==( r==0 ? 1 : -1 ) ){
                                  types[r] = reverseRelationKind( types[r] );
                                }
                                if( pivot_factor_sign==1 ){
                                  exp.push_back( NodeManager::currentNM()->mkNode( kind::GT, pivot_factor, d_zero ) );
                                }else{
                                  exp.push_back( NodeManager::currentNM()->mkNode( kind::LT, pivot_factor, d_zero ) );
                                }
                              }
                              Kind jk = transKinds( types[0], types[1] );
                              Trace("nl-alg-rbound-debug") << "trans kind : " << types[0] << " + " << types[1] << " = " << jk << std::endl;
                              if( jk!=kind::UNDEFINED_KIND ){
                                Node conc = NodeManager::currentNM()->mkNode( jk, rhs_a_res, rhs_b_res );
                                Node conc_mv = computeModelValue( conc, 1 );
                                if( conc_mv==d_false ){
                                  Node rblem = NodeManager::currentNM()->mkNode( kind::IMPLIES, NodeManager::currentNM()->mkNode( kind::AND, exp ), conc );
                                  Trace("nl-alg-rbound-lemma-debug") << "Resolution bound lemma (pre-rewrite) : " << rblem << std::endl;
                                  rblem = Rewriter::rewrite( rblem );
                                  Trace("nl-alg-rbound-lemma") << "Resolution bound lemma : " << rblem << std::endl;
                                  lemmas.push_back( rblem );
                                }
                              }
                              exp.pop_back();
                              exp.pop_back();
                              exp.pop_back();
                            }
                          }
                        }
                        exp.pop_back();
                      }
                    }
                  }
                }
              }
            }
          }
        }
        lemmas_proc = flushLemmas( lemmas );
        if( lemmas_proc>0 ){
          Trace("nl-alg") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
          return;
        }
      }
      
      //from inferred bound inferences
      lemmas_proc = flushLemmas( nt_lemmas );
      if( lemmas_proc>0 ){
        Trace("nl-alg") << "  ...finished with " << lemmas_proc << " new (monomial-introducing) lemmas." << std::endl;
        return;
      }

      

      
      
      if( options::nlAlgTangentPlanes() ){
        Trace("nl-alg")  << "Get tangent plane lemmas..." << std::endl;
        unsigned kstart = ms_vars.size();
        for( unsigned k=kstart; k<terms.size(); k++ ){
          Node t = terms[k];
          //if this term requires a refinement
          if( tplane_refine_dir.find( t )!=tplane_refine_dir.end() ){
            Trace("nl-alg-tplanes") << "Look at monomial requiring refinement : " << t << std::endl;
            //get a decomposition
            std::map< Node, std::vector< Node > >::iterator it = d_m_contain_children.find( t );
            if( it!=d_m_contain_children.end() ){
              std::map< Node, std::map< Node, bool > > dproc;
              for( unsigned j=0; j<it->second.size(); j++ ){
                Node tc = it->second[j];
                if( tc!=d_one ){
                  Node tc_diff = d_m_contain_umult[tc][t];
                  Assert( !tc_diff.isNull() );
                  Node a = tc<tc_diff ? tc : tc_diff;
                  Node b = tc<tc_diff ? tc_diff : tc;
                  if( dproc[a].find( b )==dproc[a].end() ){
                    dproc[a][b] = true;
                    Trace("nl-alg-tplanes") << "  decomposable into : " << a << " * " << b << std::endl;
                    Node a_v = computeModelValue( a, 1 );
                    Node b_v = computeModelValue( b, 1 );
                    //tangent plane 
                    Node tplane = NodeManager::currentNM()->mkNode( kind::MINUS,
                                    NodeManager::currentNM()->mkNode( kind::PLUS,
                                      NodeManager::currentNM()->mkNode( kind::MULT, b_v, a ),
                                      NodeManager::currentNM()->mkNode( kind::MULT, a_v, b ) ),
                                    NodeManager::currentNM()->mkNode( kind::MULT, a_v, b_v ) );
                    for( unsigned d=0; d<4; d++ ){
                      Node aa = NodeManager::currentNM()->mkNode( d==0 || d==3 ? kind::GEQ : kind::LEQ, a, a_v );
                      Node ab = NodeManager::currentNM()->mkNode( d==1 || d==3 ? kind::GEQ : kind::LEQ, b, b_v );
                      Node conc = NodeManager::currentNM()->mkNode( d<=1 ? kind::LEQ : kind::GEQ, t, tplane );
                      Node tlem = NodeManager::currentNM()->mkNode( kind::OR, aa.negate(), ab.negate(), conc );
                      Trace("nl-alg-tplanes") << "Tangent plane lemma : " << tlem << std::endl;
                      lemmas.push_back( tlem );
                    }
                  }
                }
              }
            }
          }
        }
        Trace("nl-alg") << "...trying " << lemmas.size() << " tangent plane lemmas..." << std::endl;
        lemmas_proc = flushLemmas( lemmas );
        if( lemmas_proc>0 ){
          Trace("nl-alg") << "  ...finished with " << lemmas_proc << " new lemmas." << std::endl;
          return;
        }
      }
      
      Trace("nl-alg") << "...set incomplete" << std::endl;
      d_containing.getOutputChannel().setIncomplete();
    }
  }
}

void NlAlg::assignOrderIds( std::vector< Node >& vars, std::map< Node, unsigned >& order, unsigned orderType ) {
  sortNlAlg smv;
  smv.d_nla = this;
  smv.d_order_type = orderType;
  smv.d_reverse_order = false;
  std::sort( vars.begin(), vars.end(), smv );
  
  order.clear();
  //assign ordering id's
  unsigned counter = 0;
  unsigned order_index = ( orderType==0 || orderType==2 ) ? 0 : 1;
  Node prev;
  for( unsigned j=0; j<vars.size(); j++ ){
    Node x = vars[j];
    Node v = get_compare_value( x, orderType );
    Trace("nl-alg-mvo") << "  order " << x << " : " << v << std::endl;
    if( v!=prev ){
      //builtin points
      bool success;
      do{
        success = false;
        if( order_index<d_order_points.size() ){
          Node vv = get_compare_value( d_order_points[order_index], orderType );
          if( compare_value( v, vv, orderType )<=0 ){
            counter++;
            Trace("nl-alg-mvo") << "O_" << orderType << "[" << d_order_points[order_index] << "] = " << counter << std::endl;
            order[d_order_points[order_index]] = counter;
            prev = vv;
            order_index++;  
            success = true;
          }
        }
      }while( success );
    }
    if( prev.isNull() || compare_value( v, prev, orderType )!=0 ){
      counter++;
    }
    Trace("nl-alg-mvo") << "O_" << orderType << "[" << x << "] = " << counter << std::endl;
    order[x] = counter;
    prev = v;
  }
  while( order_index<d_order_points.size() ){
    counter++;
    Trace("nl-alg-mvo") << "O_" << orderType << "[" << d_order_points[order_index] << "] = " << counter << std::endl;
    order[d_order_points[order_index]] = counter;
    order_index++;  
  }
}

int NlAlg::compare( Node i, Node j, unsigned orderType ) {
  if( orderType>=0 && orderType<=3 ){
    return compare_value( get_compare_value( i, orderType ), get_compare_value( j, orderType ), orderType );
  //minimal degree
  }else if( orderType==4 ){
    std::map< Node, unsigned >::iterator iti = d_m_degree.find( i );
    Assert( iti!=d_m_degree.end() );
    std::map< Node, unsigned >::iterator itj = d_m_degree.find( j );
    Assert( itj!=d_m_degree.end() );
    return iti->second==itj->second ? 0 : ( iti->second<itj->second ? 1 : -1 );
  }else{
    return 0;
  }
}

int NlAlg::compare_value( Node i, Node j, unsigned orderType ) {
  Assert( orderType>=0 && orderType<=3 );
  Trace("nl-alg-debug") << "compare_value " << i << " " << j << ", o = " << orderType << std::endl;
  int ret;
  if( i==j ){
    ret = 0;
  }else if( orderType==0 || orderType==2 ){
    ret = i.getConst<Rational>()<j.getConst<Rational>() ? 1 : -1;
  }else{
    Trace("nl-alg-debug") << "vals : " << i.getConst<Rational>() << " " << j.getConst<Rational>() << std::endl;
    Trace("nl-alg-debug") << i.getConst<Rational>().abs() << " " << j.getConst<Rational>().abs() << std::endl;
    ret = ( i.getConst<Rational>().abs()==j.getConst<Rational>().abs() ? 0 : ( i.getConst<Rational>().abs()<j.getConst<Rational>().abs() ? 1 : -1 ) );
  }
  Trace("nl-alg-debug") << "...return " << ret << std::endl;
  return ret;
}

Node NlAlg::get_compare_value( Node i, unsigned orderType ) {
  Trace("nl-alg-debug") << "Compare variable " << i << " " << orderType << std::endl;
  Assert( orderType>=0 && orderType<=3 );
  std::map< Node, Node >::iterator iti;
  unsigned mindex = orderType<=1 ? 0 : 1;
  iti = d_mv[mindex].find( i );
  Assert( iti!=d_mv[mindex].end() );
  return iti->second;
}

// trying to show a <> 0 by inequalities between variables in monomial a w.r.t 0
int NlAlg::compareSign( Node oa, Node a, unsigned a_index, int status, std::vector< Node >& exp, std::vector< Node >& lem ) {
  Trace("nl-alg-debug") << "Process " << a << " at index " << a_index << ", status is " << status << std::endl;
  Assert( d_mv[1].find( oa )!=d_mv[1].end() );
  if( a_index==d_m_vlist[a].size() ){
    if( d_mv[1][oa].getConst<Rational>().sgn()!=status ){
      lem.push_back( NodeManager::currentNM()->mkNode( kind::IMPLIES, mkAnd( exp ), mkLit( oa, d_zero, status*2 ) ) );
    }
    return status;
  }else{
    Assert( a_index<d_m_vlist[a].size() );
    Node av = d_m_vlist[a][a_index];
    unsigned aexp = d_m_exp[a][av];
    //take current sign in model
    Assert( d_mv[0].find( av )!=d_mv[0].end() );
    int sgn = d_mv[0][av].getConst<Rational>().sgn();
    Trace("nl-alg-debug") << "Process var " << av << "^" << aexp << ", model sign = " << sgn << std::endl;
    if( sgn==0 ){
      if( d_mv[1][oa].getConst<Rational>().sgn()!=0 ){
        lem.push_back( NodeManager::currentNM()->mkNode( kind::IMPLIES, av.eqNode( d_zero ), oa.eqNode( d_zero ) ) );
      }
      return 0;
    }else{
      if( aexp%2==0 ){
        exp.push_back( av.eqNode( d_zero ).negate() );
        return compareSign( oa, a, a_index+1, status, exp, lem );
      }else{
        exp.push_back( NodeManager::currentNM()->mkNode( sgn==1 ? kind::GT : kind::LT, av, d_zero ) );
        return compareSign( oa, a, a_index+1, status*sgn, exp, lem );
      }
    }
  }
}

bool NlAlg::compareMonomial( Node oa, Node a, std::map< TNode, unsigned >& a_exp_proc, 
                             Node ob, Node b, std::map< TNode, unsigned >& b_exp_proc, 
                             std::vector< Node >& exp, std::vector< Node >& lem,
                             std::map< int, std::map< Node, std::map< Node, Node > > >& cmp_infers ) {
  Trace("nl-alg-comp-debug") << "Check |" << a << "| >= |" << b << "|" << std::endl;
  unsigned pexp_size = exp.size();
  if( compareMonomial( oa, a, 0, a_exp_proc, ob, b, 0, b_exp_proc, 0, exp, lem, cmp_infers ) ){
    return true;
  }else{
    exp.resize( pexp_size );
    Trace("nl-alg-comp-debug") << "Check |" << b << "| >= |" << a << "|" << std::endl;
    if( compareMonomial( ob, b, 0, b_exp_proc, oa, a, 0, a_exp_proc, 0, exp, lem, cmp_infers ) ){
      return true;
    }else{
      return false;
    }
  }
}
                   
bool NlAlg::cmp_holds( Node x, Node y, std::map< Node, std::map< Node, Node > >& cmp_infers, std::vector< Node >& exp, std::map< Node, bool >& visited ) {
  if( x==y ){
    return true;
  }else if( visited.find( x )==visited.end() ){
    visited[x] = true;
    std::map< Node, std::map< Node, Node > >::iterator it = cmp_infers.find( x );
    if( it!=cmp_infers.end() ){
      for( std::map< Node, Node >::iterator itc = it->second.begin(); itc != it->second.end(); ++itc ){
        exp.push_back( itc->second );
        if( cmp_holds( itc->first, y, cmp_infers, exp, visited ) ){
          return true;
        }
        exp.pop_back();
      }
    }
  }
  return false;
}

                      
// trying to show a ( >, = ) b   by inequalities between variables in monomials a,b
bool NlAlg::compareMonomial( Node oa, Node a, unsigned a_index, std::map< TNode, unsigned >& a_exp_proc, 
                             Node ob, Node b, unsigned b_index, std::map< TNode, unsigned >& b_exp_proc, 
                             int status, std::vector< Node >& exp, std::vector< Node >& lem,
                             std::map< int, std::map< Node, std::map< Node, Node > > >& cmp_infers ) {
  Trace("nl-alg-comp-debug") << "compareMonomial " << oa << " and " << ob << ", indices = " << a_index << " " << b_index << std::endl;
  Assert( status==0 || status==2 );
  if( a_index==d_m_vlist[a].size() && b_index==d_m_vlist[b].size() ){
    //finished, compare abstract values
    int modelStatus = compare( oa, ob, 3 )*-2;
    Trace("nl-alg-comp") << "...finished comparison with " << oa << " <" << status << "> " << ob << ", model status = " << modelStatus << std::endl;
    if( status!=modelStatus ){
      Trace("nl-alg-comp-infer") << "infer : " << oa << " <" << status << "> " << ob << std::endl;
      if( status==2 ){
        //must state that all variables are non-zero
        for( unsigned j=0; j<d_m_vlist[a].size(); j++ ){
          exp.push_back( d_m_vlist[a][j].eqNode( d_zero ).negate() );
        }
      }
      Node clem = NodeManager::currentNM()->mkNode( kind::IMPLIES, mkAnd( exp ), mkLit( oa, ob, status, 1 ) );
      Trace("nl-alg-comp-lemma") << "comparison lemma : " << clem << std::endl;
      lem.push_back( clem );
      cmp_infers[status][oa][ob] = clem;
    }
    return true;
  }else{
    //get a/b variable information
    Node av;
    unsigned aexp = 0;
    unsigned avo = 0;
    if( a_index<d_m_vlist[a].size() ){
      av = d_m_vlist[a][a_index];
      Assert( a_exp_proc[av] <= d_m_exp[a][av] );
      aexp = d_m_exp[a][av] - a_exp_proc[av];
      if( aexp==0 ){
        return compareMonomial( oa, a, a_index+1, a_exp_proc, ob, b, b_index, b_exp_proc, status, exp, lem, cmp_infers );
      }
      Assert( d_order_vars[1].find( av )!=d_order_vars[1].end() );
      avo = d_order_vars[1][av];
    }
    Node bv;
    unsigned bexp = 0;
    unsigned bvo = 0;
    if( b_index<d_m_vlist[b].size() ){ 
      bv = d_m_vlist[b][b_index];
      Assert( b_exp_proc[bv] <= d_m_exp[b][bv] );
      bexp = d_m_exp[b][bv] - b_exp_proc[bv];
      if( bexp==0 ){
        return compareMonomial( oa, a, a_index, a_exp_proc, ob, b, b_index+1, b_exp_proc, status, exp, lem, cmp_infers );
      }
      Assert( d_order_vars[1].find( bv )!=d_order_vars[1].end() );
      bvo = d_order_vars[1][bv];
    }
    //get "one" information
    Assert( d_order_vars[1].find( d_one )!=d_order_vars[1].end() );
    unsigned ovo = d_order_vars[1][d_one];
    Trace("nl-alg-comp-debug") << "....vars : " << av << "^" << aexp << " " << bv << "^" << bexp << std::endl;

    //--- cases
    if( av.isNull() ){
      if( bvo<=ovo ){
        Trace("nl-alg-comp-debug") << "...take leading " << bv << std::endl;
        //can multiply b by <=1
        exp.push_back( mkLit( d_one, bv, bvo==ovo ? 0 : 2, 1 ) );
        return compareMonomial( oa, a, a_index, a_exp_proc, ob, b, b_index+1, b_exp_proc, bvo==ovo ? status : 2, exp, lem, cmp_infers );
      }else{
        Trace("nl-alg-comp-debug") << "...failure, unmatched |b|>1 component." << std::endl;
        return false;
      }
    }else if( bv.isNull() ){
      if( avo>=ovo ){
        Trace("nl-alg-comp-debug") << "...take leading " << av << std::endl;
        //can multiply a by >=1
        exp.push_back( mkLit( av, d_one, avo==ovo ? 0 : 2, 1 ) );
        return compareMonomial( oa, a, a_index+1, a_exp_proc, ob, b, b_index, b_exp_proc, avo==ovo ? status : 2, exp, lem, cmp_infers );
      }else{
        Trace("nl-alg-comp-debug") << "...failure, unmatched |a|<1 component." << std::endl;
        return false;
      }
    }else{
      Assert( !av.isNull() && !bv.isNull() );
      if( avo>=bvo ){
        if( bvo<ovo && avo>=ovo ){
          Trace("nl-alg-comp-debug") << "...take leading " << av << std::endl;
          //do avo>=1 instead
          exp.push_back( mkLit( av, d_one, avo==ovo ? 0 : 2, 1 ) );
          return compareMonomial( oa, a, a_index+1, a_exp_proc, ob, b, b_index, b_exp_proc, avo==ovo ? status : 2, exp, lem, cmp_infers );
        }else{
          unsigned min_exp = aexp>bexp ? bexp : aexp;
          a_exp_proc[av] += min_exp;
          b_exp_proc[bv] += min_exp;
          Trace("nl-alg-comp-debug") << "...take leading " << min_exp << " from " << av << " and " << bv << std::endl;
          exp.push_back( mkLit( av, bv, avo==bvo ? 0 : 2, 1 ) );
          bool ret = compareMonomial( oa, a, a_index, a_exp_proc, ob, b, b_index, b_exp_proc, avo==bvo ? status : 2, exp, lem, cmp_infers );
          a_exp_proc[av] -= min_exp;
          b_exp_proc[bv] -= min_exp;
          return ret;
        }
      }else{
        if( bvo<=ovo ){
          Trace("nl-alg-comp-debug") << "...take leading " << bv << std::endl;
          //try multiply b <= 1
          exp.push_back( mkLit( d_one, bv, bvo==ovo ? 0 : 2, 1 ) );
          return compareMonomial( oa, a, a_index, a_exp_proc, ob, b, b_index+1, b_exp_proc, bvo==ovo ? status : 2, exp, lem, cmp_infers );
        }else{
          Trace("nl-alg-comp-debug") << "...failure, leading |b|>|a|>1 component." << std::endl;
          return false;
        }
      }
    }
  }
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

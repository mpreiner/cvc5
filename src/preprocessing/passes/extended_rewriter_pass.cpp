/*********************                                                        */
/*! \file extended_rewriter_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The ExtRewPre preprocessing pass
 **
 ** Applies the extended rewriter to assertions
 **/

#include "preprocessing/passes/extended_rewriter_pass.h"

#include "theory/quantifiers/extended_rewrite.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {
  
Node applyInternalBv(theory::quantifiers::ExtendedRewriter& extr, Node n )
{
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end()) {
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur) {
        visit.push_back(cn);
      }
    } else if (it->second.isNull()) {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur) {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged) {
        ret = nm->mkNode(cur.getKind(), children);
      }
      Node new_ret = ret;
      // apply extended rewriter if BV
      theory::TheoryId tid;
      if (ret.getKind() == kind::ITE)
      {
        tid = theory::Theory::theoryOf(ret.getType());
      }
      else
      {
        tid = theory::Theory::theoryOf(ret);
      }
      if( tid == theory::THEORY_BV )
      {
        Trace("ext-rew-bv") << "Apply bv ext rew preprocess to " << ret << std::endl;
        new_ret = extr.extendedRewriteBv(ret);
        if( new_ret.isNull() )
        {
          new_ret = ret;
        }
      }
      visited[cur] = new_ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

ExtRewPre::ExtRewPre(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ext-rew-pre"){};

PreprocessingPassResult ExtRewPre::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  theory::quantifiers::ExtendedRewriter extr(options::extRewPrepAgg());
  extr.configure(options::extRewBvRules());
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node res;
    if( options::extRewPrepBv() )
    {
      res = applyInternalBv(extr,(*assertionsToPreprocess)[i]);
    }
    else
    {
      res = extr.extendedRewrite((*assertionsToPreprocess)[i]);
    }
    assertionsToPreprocess->replace(
          i, res);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

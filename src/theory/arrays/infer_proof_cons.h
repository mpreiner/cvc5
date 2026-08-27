/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference to proof conversion for the AEXT array solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__INFER_PROOF_CONS_H
#define CVC5__THEORY__ARRAYS__INFER_PROOF_CONS_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"
#include "theory/arrays/path_edge.h"
#include "theory/inference_id.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * Converts between array inference information (conclusion, explanation,
 * inference id) and trustworthy proof steps.  Acts as a lazy proof generator:
 * inferences are registered via notifyFact and proofs are produced on demand
 * in getProofFor.
 *
 * The main method is convert(), which decomposes a single AEXT inference into
 * a chain of primitive proof steps (ARRAYS_READ_OVER_WRITE, CONG, TRANS, etc.)
 * added to a CDProof.
 */
class ArraysInferProofCons : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env the environment
   * @param c context for the lazy fact map; if null a dummy context is used
   */
  ArraysInferProofCons(Env& env, context::Context* c);
  ~ArraysInferProofCons() {}

  /**
   * Register an inference that may need a proof later.
   * Must be called before getProofFor(conc) in the same SAT context.
   */
  void notifyFact(Node conc, Node exp, InferenceId id);

  /**
   * Register an inference with path edge information.
   * Used for path-based inferences (CongR, AccessStore, AccessConstArray)
   * where the path edges are needed to build the fine-grained proof.
   *
   * @param paths vector of path edge vectors. For CongR, paths[0] and
   *   paths[1] are the paths for the two selects. For AccessStore and
   *   AccessConstArray, paths[0] is the single path.
   *   Each path is in target-to-start order (matching the condition order
   *   in the explanation).
   */
  void notifyFact(Node conc,
                  Node exp,
                  InferenceId id,
                  std::vector<std::vector<PathEdge>>&& paths);

  /** Lazy proof generation entry point. */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  std::string identify() const override;

 private:
  /** Stored inference information. */
  struct InferInfo
  {
    Node d_exp;
    InferenceId d_id;
    /** Path edges, indexed by path number (0 or 0+1 for CongR). */
    std::vector<std::vector<PathEdge>> d_paths;
  };

  /**
   * Convert an inference to proof steps in cdp.
   */
  void convert(const InferInfo& ii, TNode conc, CDProof* cdp);

  /**
   * Build a proof chain for propagating a select through a sequence of
   * stores.  Given a select on readArray at readIndex, and the path
   * edges (in target-to-start order), builds the chain of CONG + ROW
   * steps and returns the final select node reached.
   *
   * The per-edge conditions are read off the PathEdge entries themselves,
   * not scanned out of the explanation. expIdx is advanced by exactly the
   * number of literals these edges contributed, so the caller knows where
   * its own trailing conditions begin.
   *
   * @param cdp the proof to add steps to
   * @param sel the select term being traced (select(readArray, readIndex))
   * @param pathEdges the store edges in target-to-start order
   * @param expIdx[in,out] current position in the flattened explanation
   * @return the select node at the end of the path
   */
  Node addPathSelectProof(CDProof* cdp,
                          Node sel,
                          const std::vector<PathEdge>& pathEdges,
                          size_t& expIdx);

  /**
   * Add a CONG step proving `expected` from `premises` applied to `src`.
   *
   * expr::proveCong adds no step at all when its internal check fails, and
   * can return an equality other than the one the surrounding chain is built
   * around. In either case `expected` would remain an unproven leaf and hit
   * Unreachable() inside ProofNodeManager::mkScope -- an abort that
   * production builds reach too, since it is not behind an assertion. This
   * closes that hole with a trusted step over the supplied premises.
   *
   * @return `expected`, which is guaranteed to have a proof afterwards.
   */
  Node addCongStep(CDProof* cdp,
                   const Node& src,
                   const std::vector<Node>& premises,
                   const Node& expected);

  /** Proof conversion for CongR inferences. */
  void convertCongruence(const InferInfo& ii,
                         TNode conc,
                         const std::vector<Node>& expv,
                         CDProof* cdp);
  /** Proof conversion for AccessStore inferences. */
  void convertAccessStore(const InferInfo& ii,
                          TNode conc,
                          const std::vector<Node>& expv,
                          CDProof* cdp);
  /** Proof conversion for AccessConstArray inferences. */
  void convertAccessConstArray(const InferInfo& ii,
                               TNode conc,
                               const std::vector<Node>& expv,
                               CDProof* cdp);
  /** Proof conversion for RIntro2 inferences. */
  void convertRIntro2(TNode conc, const std::vector<Node>& expv, CDProof* cdp);

  /** A dummy context used if none is provided. */
  context::Context d_context;
  /** Map from conclusion -> stored inference info. */
  context::CDHashMap<Node, InferInfo> d_lazyFactMap;
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__INFER_PROOF_CONS_H */

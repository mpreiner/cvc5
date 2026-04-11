/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Path edge for AEXT array solver proof reconstruction.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__PATH_EDGE_H
#define CVC5__THEORY__ARRAYS__PATH_EDGE_H

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * One edge in a BFS path through the store graph.
 * Records the concrete nodes traversed so that the proof converter can
 * build the matching ROW/CONG steps.
 */
struct PathEdge
{
  TNode store; /**< the store traversed (null for the start node) */
  bool isRowU; /**< true if RowU (going up from child to store) */
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__PATH_EDGE_H */

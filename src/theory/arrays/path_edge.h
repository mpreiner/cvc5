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
 *
 * The explanation literals an edge contributed are carried on the edge
 * itself rather than recovered by position from the flattened explanation.
 * Positional recovery needed a heuristic to decide whether a leading array
 * equality opened this path's group or the next one, and mis-assigned it
 * whenever a path had no start guard and the following path's first literal
 * happened to mention the same array. Carrying the literals here makes the
 * association structural, and lets a consumer compute exactly how many
 * literals a path occupies.
 *
 * Any of the three literals may be null: an equality is only emitted when
 * its two sides differ syntactically, and the start node (null store) never
 * has an index disequality.
 */
struct PathEdge
{
  TNode store; /**< the store traversed (null for the start node) */
  bool isRowU; /**< true if RowU (going up from child to store) */
  /** entry array of this edge = representative of the class it arrives at */
  Node entryEq;
  /** previous entry array = this edge's store (RowD) or its base (RowU) */
  Node linkEq;
  /** read index differs from the store index (null for the start node) */
  Node indexDiseq;
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__PATH_EDGE_H */

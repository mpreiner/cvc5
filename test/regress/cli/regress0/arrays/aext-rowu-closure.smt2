; COMMAND-LINE: --arrays-solver=aext
; EXPECT: unsat
; Same shape as aext-rowu-required but two store levels deep, which exercises
; the downward closure in computeActiveArrays rather than just its seed. Only
; rep of the outer store has a non-singleton class; the closure has to walk
; down through the inner store to reach rep(a), and RowU then has to fire twice
; to carry the read at index i up to the constant array.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun v () Int)
(declare-fun w () Int)
(assert (= (store (store a j v) k w) ((as const (Array Int Int)) 7)))
(assert (distinct i j))
(assert (distinct i k))
(assert (not (= (select a i) 7)))
(check-sat)

; COMMAND-LINE: --arrays-solver=aext --produce-proofs --check-proofs
; EXPECT: unsat
; Exercises convertAccessConstArray: the read travels one RowD edge to a,
; whose class holds the constant array, so the proof needs the path chain plus
; the ARRAYS_SELECT_CONST theory rewrite.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= a ((as const (Array Int Int)) 3)))
(assert (distinct i j))
(assert (not (= (select (store a j 1) i) 3)))
(check-sat)

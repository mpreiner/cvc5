; COMMAND-LINE: --arrays-solver=aext --produce-proofs --check-proofs
; EXPECT: unsat
; Exercises the AEXT CongR proof reconstruction: the read on the outer store
; travels down two RowD edges to a, where it meets the read on a directly.
; The b = store(a,j,1) equality makes the second edge need an array-equality
; link condition, so the path proof has to emit a CONG bridge as well as ROW.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= b (store a j 1)))
(assert (distinct i j))
(assert (distinct i k))
(assert (not (= (select (store b k 2) i) (select a i))))
(check-sat)

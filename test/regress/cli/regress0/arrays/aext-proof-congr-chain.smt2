; COMMAND-LINE: --arrays-solver=aext --produce-proofs --check-proofs
; EXPECT: unsat
; AEXT CongR over a two-store chain with no array-equality links, so the path
; proof is a bare ROW/ROW chain closed by TRANS.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (distinct i j))
(assert (distinct i k))
(assert (not (= (select (store (store a j 1) k 2) i) (select a i))))
(check-sat)

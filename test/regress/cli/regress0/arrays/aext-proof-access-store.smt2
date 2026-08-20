; COMMAND-LINE: --arrays-solver=aext --produce-proofs --check-proofs
; EXPECT: unsat
; Covers convertAccessStore (ARRAYS_AEXT_ROW), together with CongR and
; AccessConstArray, in one proof. AccessStore resists a hand-written small
; reproducer: on tiny inputs the InitW virtual read select(store(a,i,v),i)
; lets RIntro2 or the rewriter settle the same conclusion first, so this was
; reduced from a random QF_AUFLIA instance instead (fuzz2.py seed 185).
(set-logic QF_AUFLIA)
(declare-fun a0 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(assert (= (store ((as const (Array Int Int)) 1) i3 (+ (select a0 (+ i2 2)) 1)) (store (store (store a2 (+ i3 0) 0) i1 3) (+ i3 1) 0)))
(check-sat)

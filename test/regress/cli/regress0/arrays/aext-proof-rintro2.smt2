; COMMAND-LINE: --arrays-solver=aext --produce-proofs --check-proofs
; EXPECT: unsat
; Exercises convertRIntro2, including its step-3 CONG across c = b: the
; conclusion's array is reached from the store's base only through that
; equality, which is the orientation-sensitive step in that converter.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(assert (= b (store a j v)))
(assert (= c b))
(assert (distinct i j))
(assert (not (= (select c i) (select a i))))
(check-sat)

; COMMAND-LINE: --arrays-solver=aext
; EXPECT: unsat
; RowU is load-bearing here. The only read at index i sits on a, and the value
; it must take comes from the constant array in the parent store's class, so
; the read has to travel *up* into store(a,j,v) to meet it -- nothing descends
; to a, since a constant array is not a store. computeActiveArrays must mark
; rep(a) active: rep(store(a,j,v)) has a two-member class, which seeds the set,
; and the downward closure then marks the store's base.
; If the RowU gate ever over-restricts, this answers sat.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(assert (= (store a j v) ((as const (Array Int Int)) 7)))
(assert (distinct i j))
(assert (not (= (select a i) 7)))
(check-sat)

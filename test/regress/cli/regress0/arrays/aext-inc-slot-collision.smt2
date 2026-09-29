; COMMAND-LINE: --arrays-solver=aext --arrays-aext-check-incremental
; EXPECT: unsat
; Two reads recorded at different classes that are merged later. Each read
; descends one store, to a and to b respectively, in the first check. With
; a = b their slots collide, and the incremental check must compare the two
; occupants (CongR). With a = (store b r z) nothing collides; instead the
; merge makes store(b r z) a second member of a's class, which opens the RowU
; gate at b and adds a RowD edge out of a, and resuming either read makes the
; two meet. Missing either answers sat.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun r () Int)
(declare-fun u () Int)
(declare-fun w () Int)
(declare-fun z () Int)
(assert (not (= i p)))
(assert (not (= i q)))
(assert (not (= i r)))
(assert (not (= (select (store a p w) i) (select (store b q u) i))))
(assert (or (= a b) (= a (store b r z))))
(check-sat)

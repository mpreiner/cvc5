; COMMAND-LINE: --arrays-solver=aext --arrays-aext-check-incremental
; EXPECT: sat
; An index merge that closes an edge a read has already crossed. With i and p
; undecided, the first check walks (select (store a p w) i) down to a, meets
; the other read there, and sends CongR guarded by (not (= i p)). The lemma
; propagates i = p, which closes that edge: the read no longer reaches a. The
; incremental check that follows must drop what the read recorded and walk it
; again. Keeping the stale entry leaves a slot the rebuild does not have, and
; any later CongR against it would fail to find a path.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun p () Int)
(declare-fun t () Int)
(declare-fun w () Int)
(declare-fun z () Int)
(assert (not (= i t)))
(assert (not (= (select (store a p w) i) (select (store a t z) i))))
(check-sat)

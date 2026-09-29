; COMMAND-LINE: --arrays-solver=aext --arrays-aext-check-incremental
; EXPECT: unsat
; An array merge after a read is already recorded. The read on the double
; store reaches a in the first check, two RowD steps down, where RIntro2 cannot
; see it. Deciding either disjunct then merges a with a store at index i, and
; the next check is incremental: it must move the read's slot into the merged
; class, check CongR against the store's InitW read found there, and resume
; the read to meet the store itself (AccessStore). If the merge handling
; misses either, the branch is not refuted and the answer is sat.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(declare-fun w () Int)
(assert (not (= i p)))
(assert (not (= i q)))
(assert (not (= (select (store (store a p w) q u) i) v)))
(assert (or (= a (store b i v)) (= a (store c i v))))
(check-sat)

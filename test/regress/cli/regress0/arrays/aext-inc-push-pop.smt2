; COMMAND-LINE: --arrays-solver=aext --arrays-aext-check-incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; The incremental AEXT check across user-level push and pop. Terms registered
; in a popped scope leave the equality engine while the propagation state,
; which is not context-dependent, may still mention them; the check has to
; notice that the state no longer describes the current context and rebuild
; before reading any of it. The scopes repeat the merge, AccessStore and
; index-merge scenarios of the other aext-inc-* regressions.
(set-option :incremental true)
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun t () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(declare-fun w () Int)
(declare-fun z () Int)
(assert (not (= j i)))
(assert (not (= j p)))
(assert (not (= j q)))
(assert (not (= (select (store b p w) j) (select (store a q u) j))))
(check-sat)
(push 1)
(assert (= a (store b i v)))
(check-sat)
(pop 1)
(push 1)
(assert (not (= i p)))
(assert (not (= i q)))
(assert (not (= (select (store (store a p w) q u) i) v)))
(assert (or (= a (store b i v)) (= a (store c i v))))
(check-sat)
(pop 1)
(push 1)
(assert (not (= i t)))
(assert (not (= (select (store a p w) i) (select (store a t z) i))))
(check-sat)
(push 1)
(assert (not (= i p)))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)

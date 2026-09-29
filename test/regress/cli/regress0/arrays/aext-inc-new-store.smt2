; COMMAND-LINE: --arrays-solver=aext --arrays-aext-check-incremental --preregister-mode=lazy
; EXPECT: unsat
; A store registered after reads are already recorded at both of its ends.
; With lazy preregistration, (store b i v) and (store c i v) only become terms
; when the disjunct mentioning them is asserted, so the check after that
; decision sees a new store whose base (b or c) and whose class (a's, after
; the merge) both hold recorded reads. The incremental check must resume the
; reads on both sides: the one at a descends through the new store (RowD) and
; the one at its base climbs through it (RowU), and either way they meet.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(declare-fun w () Int)
(assert (not (= j i)))
(assert (not (= j p)))
(assert (not (= j q)))
(assert (not (= (select (store b p w) j) (select (store a q u) j))))
(assert (not (= (select (store c p w) j) (select (store a q u) j))))
(assert (or (= a (store b i v)) (= a (store c i v))))
(check-sat)

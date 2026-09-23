; REQUIRES: unrestricted-mode
; COMMAND-LINE: --arrays-exp --produce-proofs --check-proofs
; EXPECT: unsat
; Runs the DEFAULT array solver, with proofs, over inferences whose ids the
; AEXT solver used to share: ARRAYS_CONST_ARRAY_DEFAULT (the read on the
; constant array) and ARRAYS_READ_OVER_WRITE (the Row propagation through the
; two stores). InferenceManager dispatches its proof path on the inference id
; alone, so a shared id sends the default solver's explanations to
; ArraysInferProofCons, which re-parses them against AEXT's shape. The
; assertion on isAextInference in InferenceManager catches that; this
; regression is what makes a debug build execute it.
(set-logic QF_ALIA)
(set-info :status unsat)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const k Int)
(assert (= a ((as const (Array Int Int)) 1)))
(assert (distinct i j))
(assert (distinct i k))
(assert (not (= (select (store (store a j 2) k 3) i) 1)))
(check-sat)

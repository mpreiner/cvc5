; REQUIRES: tracing
; COMMAND-LINE: --arrays-solver=aext --produce-proofs --check-proofs -t arrays::aext --dag-thresh=0
; SCRUBBER: grep -E "^(CongR: |unsat$)"
; EXPECT: CongR: (and (= (store (f 0) k 2) (f 1)) (= (store a j 1) (f 0)) (not (= i k)) (not (= i j))) => (= (select (f 1) i) (select a i))
; EXPECT: unsat
;
; Pins the guard set of an AEXT path lemma, which no answer-only test can do.
;
; findPathConditions may emit three kinds of literal per node on the path: the
; ROW side condition NOT(= readIndex store[1]), the link equality carrying the
; read onto the store this step traverses, and -- for the target node only --
; the equality tying the array the path arrives at to its class
; representative. That last one is dead weight on an intermediate node:
; addPathSelectProof never mentions a representative, so nothing consumes it,
; and it only weakens the lemma.
;
; The shape below makes the difference observable. The reads on (f 1) and a
; are joined by CongR over a two-store chain, and the arrays are produced by
; an uninterpreted function so that ppAssert cannot substitute the aliases
; away -- with plain array constants the chain is solved during preprocessing
; and the solver never sees a multi-edge path. (f 0) is then reached through
; the term (store a j 1) while its class representative is (f 0) itself, so an
; intermediate entryEq would be emitted -- and would duplicate the next edge's
; linkEq verbatim, giving a five-conjunct guard with (= (store a j 1) (f 0))
; in it twice. The four-conjunct guard expected above is the correct one.
;
; --dag-thresh=0 keeps the printed term flat, so the expectation does not
; depend on how the printer chooses let bindings. --produce-proofs exercises
; the matching assertion in ArraysInferProofCons::addPathSelectProof, which
; checks the same invariant structurally: only pathEdges[0] may carry an
; entryEq.
;
; If a deliberate change to the calculus alters this lemma, update the
; expectation -- but check first that no literal occurs twice in the guard.
(set-logic QF_AUFLIA)
(declare-fun f (Int) (Array Int Int))
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (f 0) (store a j 1)))
(assert (= (f 1) (store (f 0) k 2)))
(assert (distinct i j))
(assert (distinct i k))
(assert (not (= (select (f 1) i) (select a i))))
(check-sat)

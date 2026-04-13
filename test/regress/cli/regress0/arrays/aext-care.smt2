; COMMAND-LINE: --arrays-solver=aext --check-models
; EXPECT: sat
(set-logic QF_ALIA)
(declare-fun _1 () Int)
(declare-fun _5 () (Array Int Int))
(declare-fun _8 () Int)
(declare-fun _7 () (Array Int Int))
(assert (and (= 1 (select _5 _1)) (= 0 (select _5 0)) (= 0 (select _7 _1)) (= _7 (store _5 (select _7 _8) 0))))
(check-sat)

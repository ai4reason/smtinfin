(set-logic QF_UFLIA)
(declare-fun f (Int) Int)

(assert (< 0 (f 0)))
(assert (< 5 (f 5)))
(assert (< 6 (f 6)))
(assert (< 10 (f 10)))

(check-sat)
(get-model)
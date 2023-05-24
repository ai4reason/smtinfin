(set-logic UFLIA)
(declare-fun f (Int) Int)

; f unlimited
(declare-fun sk (Int) Int)
(assert (forall ((x Int)) (> (f (sk x)) x)))

(check-sat)

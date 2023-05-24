(set-logic UFLIA)
(declare-fun f (Int) Int)

(assert (forall ((x Int)) (>= (f x) x)))
(assert (> (f 10) 12))

(check-sat)
(get-model)

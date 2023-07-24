(set-logic UFLIA)
(declare-fun r (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (= (r x y) (= x y))))
(check-sat)

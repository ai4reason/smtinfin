(set-logic UFLIA)
(declare-fun f (Int) Bool)
; no 3 false's in a row
(assert (forall ((x Int)) (or (f x) (f (+ 1 x)) (f (+ 2 x)))))
; no 3 true's in a row
(assert (forall ((x Int)) (or (not (f x)) (not (f (+ 1 x))) (not (f (+ 2 x))))))
(check-sat)
(get-model)

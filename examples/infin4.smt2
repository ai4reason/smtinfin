(set-logic UFLIA)
(declare-sort S 0)
(declare-const a S)
(declare-const b S)
(declare-const c S)
(assert (distinct a b c))
(declare-fun f (Int) S)
; f(t) is an elevator request in time t, f(t) is the floor

; we assume only 3 distinct floors
(assert (forall ((x Int)) (or (= (f x) a) (= (f x) b) (= (f x) c))))

; we ignore repeated requests
(assert (forall ((x Int)) (not (= (f x) (f (- x 1))))))

; show that floor zero is never reached (starvation)
(assert (forall ((x Int)) (not (= (f x) a))))

(check-sat)
(get-model)

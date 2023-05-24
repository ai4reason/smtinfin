(set-logic UFLIA)

; atN elevator is at floor N
(declare-fun at0 (Int) Bool)
(declare-fun at1 (Int) Bool)
(declare-fun at2 (Int) Bool)

; elevator is at one and only one floor at any point in time
(assert (forall ((t Int)) (or (at0 t) (at1 t) (at2 t))))
(assert (forall ((t Int)) (not (and (at0 t) (at1 t)))))
(assert (forall ((t Int)) (not (and (at0 t) (at2 t)))))
(assert (forall ((t Int)) (not (and (at1 t) (at2 t)))))

; we ignore repeated requests
(assert (forall ((t Int)) (not (and (at0 t) (at0 (+ t 1))))))
(assert (forall ((t Int)) (not (and (at1 t) (at1 (+ t 1))))))
(assert (forall ((t Int)) (not (and (at2 t) (at2 (+ t 1))))))

; show that floor zero is never reached (starvation)
(assert (forall ((t Int)) (not (at0 t))))

(check-sat)
(get-model)

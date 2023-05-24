(set-logic UF)
(declare-sort S 0)
(declare-fun f (S) S)

; f injective
(assert (forall ((x S)(y S)) (=> (= (f x) (f y)) (= x y))))

; not surjective
(declare-fun out () S)
(assert (forall ((x S)) (not (= (f x) out))))

(check-sat)

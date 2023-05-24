(set-logic UF)
(declare-sort S 0)
(declare-fun R (S S) Bool)

; R transitive
(assert (forall ((x S)(y S)(z S)) (=> (and (R x y) (R y z)) (R x z))))

; R irreflexive
(assert (forall ((x S)) (not (R x x))))

; infinite chains
(declare-fun sk (S) S)
(assert (forall ((x S)) (R x (sk x))))

(check-sat)
(get-model)

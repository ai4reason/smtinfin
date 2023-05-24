(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unknown)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-sort S5 0)
(declare-sort S6 0)
(declare-sort S7 0)
(declare-sort S8 0)
(declare-sort S9 0)
(declare-sort S10 0)
(declare-sort S11 0)
(declare-sort S12 0)
(declare-sort S13 0)
(declare-sort S14 0)
(declare-sort S15 0)
(declare-sort S16 0)
(declare-sort S17 0)
(declare-sort S18 0)
(declare-sort S19 0)
(declare-sort S20 0)
(declare-sort S21 0)
(declare-sort S22 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S2) S2)
(declare-fun f6 (S4) S3)
(declare-fun f7 (S5 S6) S4)
(declare-fun f8 (S7 S8) S5)
(declare-fun f9 (S9 S6) S7)
(declare-fun f10 () S9)
(declare-fun f11 () S6)
(declare-fun f12 (S10 S11) S8)
(declare-fun f13 () S10)
(declare-fun f14 () S11)
(declare-fun f15 () S6)
(declare-fun f16 () S2)
(declare-fun f17 (S12 S13) S8)
(declare-fun f18 () S12)
(declare-fun f19 (S11) S13)
(declare-fun f20 (S16 S15) S1)
(declare-fun f21 (S6 S14) S16)
(declare-fun f22 (S2 S4) S1)
(declare-fun f23 (S17) S2)
(declare-fun f24 (S18 Int) S17)
(declare-fun f25 () S18)
(declare-fun f26 (S19 S17) Int)
(declare-fun f27 () S19)
(declare-fun f28 (S4 S2) S1)
(declare-fun f29 (S21 S4) S17)
(declare-fun f30 (S22 S20) S21)
(declare-fun f31 () S22)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 (f7 (f8 (f9 f10 f11) (f12 f13 f14)) f15)) f16)) f1)))
(assert (= (f3 f4 (f5 (f6 (f7 (f8 (f9 f10 f11) (f17 f18 (f19 f14))) f15)) f16)) f1))
(assert (forall ((?v0 S2)) (= (f3 ?v0 f16) f1)))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f7 (f8 (f9 f10 ?v0) ?v1) ?v2) (f7 (f8 (f9 f10 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 ?v0) f1) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S2)) (let ((?v_0 (f6 ?v1))) (=> (= (f3 ?v0 (f5 ?v_0 f16)) f1) (=> (= (f3 ?v0 ?v2) f1) (= (f3 ?v0 (f5 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S6) (?v1 S11) (?v2 S6) (?v3 S2)) (let ((?v_0 (f9 f10 ?v0))) (let ((?v_1 (f6 (f7 (f8 ?v_0 (f12 f13 ?v1)) ?v2)))) (=> (= (f3 (f5 ?v_1 ?v3) (f5 (f6 (f7 (f8 ?v_0 (f17 f18 (f19 ?v1))) ?v2)) f16)) f1) (= (f3 ?v3 (f5 ?v_1 f16)) f1))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (let ((?v_0 (f8 (f9 f10 ?v1) ?v2))) (=> (= (f3 ?v0 (f5 (f6 (f7 ?v_0 ?v3)) f16)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f20 (f21 ?v3 ?v5) ?v6) f1) (= (f20 (f21 ?v4 ?v5) ?v6) f1))) (= (f3 ?v0 (f5 (f6 (f7 ?v_0 ?v4)) f16)) f1))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (=> (= (f3 ?v0 (f5 (f6 (f7 (f8 (f9 f10 ?v1) ?v2) ?v3)) f16)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f20 (f21 ?v4 ?v5) ?v6) f1) (= (f20 (f21 ?v1 ?v5) ?v6) f1))) (= (f3 ?v0 (f5 (f6 (f7 (f8 (f9 f10 ?v4) ?v2) ?v3)) f16)) f1)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6) (?v5 S6)) (=> (= (f3 ?v0 (f5 (f6 (f7 (f8 (f9 f10 ?v1) ?v2) ?v3)) f16)) f1) (=> (forall ((?v6 S14) (?v7 S15)) (=> (= (f20 (f21 ?v4 ?v6) ?v7) f1) (forall ((?v8 S15)) (=> (forall ((?v9 S14)) (=> (= (f20 (f21 ?v1 ?v9) ?v7) f1) (= (f20 (f21 ?v3 ?v9) ?v8) f1))) (= (f20 (f21 ?v5 ?v6) ?v8) f1))))) (= (f3 ?v0 (f5 (f6 (f7 (f8 (f9 f10 ?v4) ?v2) ?v5)) f16)) f1)))))
(assert (forall ((?v0 S17) (?v1 S6) (?v2 S11) (?v3 S6)) (let ((?v_0 (f9 f10 ?v1))) (= (= (f22 (f23 ?v0) (f7 (f8 ?v_0 (f17 f18 (f19 ?v2))) ?v3)) f1) (= (f22 (f23 (f24 f25 (+ (f26 f27 ?v0) 1))) (f7 (f8 ?v_0 (f12 f13 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (=> (= (f28 ?v0 (f5 (f6 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f28 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4)) (=> (=> (not (= (f28 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f28 ?v0 (f5 (f6 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4)) (=> (= (f28 ?v0 f16) f1) false)))
(assert (forall ((?v0 S20) (?v1 S6) (?v2 S8) (?v3 S6)) (= (f29 (f30 f31 ?v0) (f7 (f8 (f9 f10 ?v1) ?v2) ?v3)) (f24 f25 0))))
(assert (forall ((?v0 S4) (?v1 S2)) (not (= f16 (f5 (f6 ?v0) ?v1)))))
(assert (forall ((?v0 S17)) (= (f24 f25 (f26 f27 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f26 f27 (f24 f25 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f26 f27 (f24 f25 ?v0)) 0))))
(check-sat)
(exit)
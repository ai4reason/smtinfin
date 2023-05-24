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
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S3 S3) S1)
(declare-fun f6 () S3)
(declare-fun f7 (S4 S3) S3)
(declare-fun f8 (S2) S4)
(declare-fun f9 (S5 S6) S2)
(declare-fun f10 (S7 S8) S5)
(declare-fun f11 (S9 S6) S7)
(declare-fun f12 () S9)
(declare-fun f13 () S6)
(declare-fun f14 (S10 S11) S8)
(declare-fun f15 () S10)
(declare-fun f16 () S11)
(declare-fun f17 () S6)
(declare-fun f18 () S3)
(declare-fun f19 (S12 S13) S8)
(declare-fun f20 () S12)
(declare-fun f21 (S11) S13)
(declare-fun f22 (S16 S15) S1)
(declare-fun f23 (S6 S14) S16)
(declare-fun f24 (S17) S3)
(declare-fun f25 (S18 Int) S17)
(declare-fun f26 () S18)
(declare-fun f27 (S19 S17) Int)
(declare-fun f28 () S19)
(declare-fun f29 (S2 S3) S1)
(declare-fun f30 (S21 S2) S17)
(declare-fun f31 (S22 S20) S21)
(declare-fun f32 () S22)
(declare-fun f33 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) false)))
(assert (not (= (f5 f6 (f7 (f8 (f9 (f10 (f11 f12 f13) (f14 f15 f16)) f17)) f18)) f1)))
(assert (= (f5 f6 (f7 (f8 (f9 (f10 (f11 f12 f13) (f19 f20 (f21 f16))) f17)) f18)) f1))
(assert (forall ((?v0 S3)) (= (f5 ?v0 f18) f1)))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f9 (f10 (f11 f12 ?v0) ?v1) ?v2) (f9 (f10 (f11 f12 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f5 ?v0 ?v1) f1) (=> (= (f5 ?v2 ?v0) f1) (= (f5 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f8 ?v1))) (=> (= (f5 ?v0 (f7 ?v_0 f18)) f1) (=> (= (f5 ?v0 ?v2) f1) (= (f5 ?v0 (f7 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S6) (?v1 S11) (?v2 S6) (?v3 S3)) (let ((?v_0 (f11 f12 ?v0))) (let ((?v_1 (f8 (f9 (f10 ?v_0 (f14 f15 ?v1)) ?v2)))) (=> (= (f5 (f7 ?v_1 ?v3) (f7 (f8 (f9 (f10 ?v_0 (f19 f20 (f21 ?v1))) ?v2)) f18)) f1) (= (f5 ?v3 (f7 ?v_1 f18)) f1))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (let ((?v_0 (f10 (f11 f12 ?v1) ?v2))) (=> (= (f5 ?v0 (f7 (f8 (f9 ?v_0 ?v3)) f18)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f22 (f23 ?v3 ?v5) ?v6) f1) (= (f22 (f23 ?v4 ?v5) ?v6) f1))) (= (f5 ?v0 (f7 (f8 (f9 ?v_0 ?v4)) f18)) f1))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (=> (= (f5 ?v0 (f7 (f8 (f9 (f10 (f11 f12 ?v1) ?v2) ?v3)) f18)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f22 (f23 ?v4 ?v5) ?v6) f1) (= (f22 (f23 ?v1 ?v5) ?v6) f1))) (= (f5 ?v0 (f7 (f8 (f9 (f10 (f11 f12 ?v4) ?v2) ?v3)) f18)) f1)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6) (?v5 S6)) (=> (= (f5 ?v0 (f7 (f8 (f9 (f10 (f11 f12 ?v1) ?v2) ?v3)) f18)) f1) (=> (forall ((?v6 S14) (?v7 S15)) (=> (= (f22 (f23 ?v4 ?v6) ?v7) f1) (forall ((?v8 S15)) (=> (forall ((?v9 S14)) (=> (= (f22 (f23 ?v1 ?v9) ?v7) f1) (= (f22 (f23 ?v3 ?v9) ?v8) f1))) (= (f22 (f23 ?v5 ?v6) ?v8) f1))))) (= (f5 ?v0 (f7 (f8 (f9 (f10 (f11 f12 ?v4) ?v2) ?v5)) f18)) f1)))))
(assert (forall ((?v0 S17) (?v1 S6) (?v2 S11) (?v3 S6)) (let ((?v_0 (f11 f12 ?v1))) (= (= (f3 (f24 ?v0) (f9 (f10 ?v_0 (f19 f20 (f21 ?v2))) ?v3)) f1) (= (f3 (f24 (f25 f26 (+ (f27 f28 ?v0) 1))) (f9 (f10 ?v_0 (f14 f15 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f29 ?v0 (f7 (f8 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f29 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f29 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f29 ?v0 (f7 (f8 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2)) (=> (= (f29 ?v0 f18) f1) false)))
(assert (forall ((?v0 S20) (?v1 S6) (?v2 S8) (?v3 S6)) (= (f30 (f31 f32 ?v0) (f9 (f10 (f11 f12 ?v1) ?v2) ?v3)) (f25 f26 0))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f18 (f7 (f8 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f7 (f8 ?v0) ?v1) f18))))
(assert (forall ((?v0 S17) (?v1 S2)) (=> (= (f3 (f24 (f25 f26 (+ (f27 f28 ?v0) 1))) ?v1) f1) (= (f3 (f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S17)) (=> (forall ((?v2 S2)) (=> (= (f29 ?v2 ?v0) f1) (= (f3 (f24 (f25 f26 (+ (f27 f28 ?v1) 1))) ?v2) f1))) (forall ((?v2 S2)) (=> (= (f29 ?v2 ?v0) f1) (= (f3 (f24 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f18) (not (= (f29 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f33 ?v0) f18) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f29 ?v0 f18) f1) false)))
(assert (forall ((?v0 S3)) (= (= f18 (f33 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f29 ?v1 f18) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f29 ?v1 f18) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f29 ?v1 ?v0) f1)) (not (= ?v0 f18)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f29 ?v1 ?v0) f1))) (= ?v0 f18))))
(assert (= f18 (f33 f4)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f29 ?v0 ?v1) f1) (= (f7 (f8 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f29 ?v0 ?v1) f1) (= (f29 ?v0 (f7 (f8 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 ?v0))) (=> (not (= (f29 ?v0 ?v1) f1)) (=> (not (= (f29 ?v0 ?v2) f1)) (= (= (f7 ?v_0 ?v1) (f7 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f7 (f8 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S17)) (= (f25 f26 (f27 f28 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f27 f28 (f25 f26 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f27 f28 (f25 f26 ?v0)) 0))))
(check-sat)
(exit)

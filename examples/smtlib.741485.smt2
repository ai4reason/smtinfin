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
(declare-sort S23 0)
(declare-sort S24 0)
(declare-sort S25 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S4) S1)
(declare-fun f4 () S4)
(declare-fun f5 (S4 S3) S1)
(declare-fun f6 (S2) S4)
(declare-fun f7 (S7 S6) S1)
(declare-fun f8 (S5) S7)
(declare-fun f9 (S8 S2) S7)
(declare-fun f10 (S9 S6) S8)
(declare-fun f11 (S10) S9)
(declare-fun f12 (S11 S10) S10)
(declare-fun f13 (S12 S7) S11)
(declare-fun f14 () S12)
(declare-fun f15 () S7)
(declare-fun f16 () S10)
(declare-fun f17 (S13 Int) S2)
(declare-fun f18 () S13)
(declare-fun f19 (S14 S2) Int)
(declare-fun f20 () S14)
(declare-fun f21 (S4 S4) S1)
(declare-fun f22 (S16 S15) S3)
(declare-fun f23 (S17 S10) S16)
(declare-fun f24 (S18 S15) S17)
(declare-fun f25 () S18)
(declare-fun f26 (S15 S5) S7)
(declare-fun f27 () S10)
(declare-fun f28 (S20 S3) S2)
(declare-fun f29 (S21 S19) S20)
(declare-fun f30 () S21)
(declare-fun f31 () S20)
(declare-fun f32 (S23 S22) S10)
(declare-fun f33 () S23)
(declare-fun f34 (S24 S10) S2)
(declare-fun f35 () S24)
(declare-fun f36 () S24)
(declare-fun f37 (S25 S10) S11)
(declare-fun f38 () S25)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2)) (=> (forall ((?v1 S3)) (=> (= (f3 ?v1 f4) f1) (= (f5 (f6 ?v0) ?v1) f1))) (forall ((?v1 S5) (?v2 S6)) (=> (= (f7 (f8 ?v1) ?v2) f1) (forall ((?v3 S6)) (=> (= (f7 (f9 (f10 (f11 (f12 (f13 f14 f15) f16)) ?v2) ?v0) ?v3) f1) (and (= (f7 (f8 ?v1) ?v3) f1) (not (= (f7 f15 ?v3) f1)))))))))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S3)) (=> (= (f3 ?v1 f4) f1) (= (f5 (f6 ?v0) ?v1) f1))) (forall ((?v1 S5) (?v2 S6)) (=> (and (= (f7 (f8 ?v1) ?v2) f1) (= (f7 f15 ?v2) f1)) (forall ((?v3 S6)) (=> (= (f7 (f9 (f10 (f11 f16) ?v2) ?v0) ?v3) f1) (= (f7 (f8 ?v1) ?v3) f1))))))))
(assert (forall ((?v0 S4) (?v1 S2)) (=> (forall ((?v2 S3)) (=> (= (f3 ?v2 ?v0) f1) (= (f5 (f6 (f17 f18 (+ (f19 f20 ?v1) 1))) ?v2) f1))) (forall ((?v2 S3)) (=> (= (f3 ?v2 ?v0) f1) (= (f5 (f6 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f5 (f6 (f17 f18 (+ (f19 f20 ?v0) 1))) ?v1) f1) (= (f5 (f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S10) (?v3 S2)) (=> (not (= (f7 ?v0 ?v1) f1)) (= (f7 (f9 (f10 (f11 (f12 (f13 f14 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S10) (?v3 S2) (?v4 S6) (?v5 S6)) (let ((?v_0 (f11 (f12 (f13 f14 ?v0) ?v2)))) (=> (= (f7 ?v0 ?v1) f1) (=> (= (f7 (f9 (f10 (f11 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f7 (f9 (f10 ?v_0 ?v4) ?v3) ?v5) f1) (= (f7 (f9 (f10 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f21 ?v0 ?v1) f1) (forall ((?v2 S2)) (=> (forall ((?v3 S3)) (=> (= (f3 ?v3 ?v0) f1) (= (f5 (f6 ?v2) ?v3) f1))) (forall ((?v3 S3)) (=> (= (f3 ?v3 ?v1) f1) (= (f5 (f6 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S7) (?v1 S10) (?v2 S7) (?v3 S10)) (= (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S10) (?v2 S6) (?v3 S2) (?v4 S6)) (=> (= (f7 (f9 (f10 (f11 (f12 (f13 f14 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 ?v2) (=> (not (= (f7 ?v0 ?v2) f1)) false)) (=> (forall ((?v5 S6)) (=> (= (f7 ?v0 ?v2) f1) (=> (= (f7 (f9 (f10 (f11 ?v1) ?v2) ?v3) ?v5) f1) (=> (= (f7 (f9 (f10 (f11 (f12 (f13 f14 ?v0) ?v1)) ?v5) ?v3) ?v4) f1) false)))) false)))))
(assert (forall ((?v0 S10) (?v1 S6) (?v2 S2) (?v3 S6)) (let ((?v_0 (f10 (f11 ?v0) ?v1))) (=> (= (f7 (f9 ?v_0 ?v2) ?v3) f1) (= (f7 (f9 ?v_0 (f17 f18 (+ (f19 f20 ?v2) 1))) ?v3) f1)))))
(assert (forall ((?v0 S10) (?v1 S6) (?v2 S2) (?v3 S6) (?v4 S2)) (let ((?v_0 (f10 (f11 ?v0) ?v1))) (=> (= (f7 (f9 ?v_0 ?v2) ?v3) f1) (=> (<= (f19 f20 ?v2) (f19 f20 ?v4)) (= (f7 (f9 ?v_0 ?v4) ?v3) f1))))))
(assert (forall ((?v0 S2) (?v1 S15) (?v2 S10) (?v3 S15)) (= (= (f5 (f6 ?v0) (f22 (f23 (f24 f25 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S5) (?v5 S6)) (=> (= (f7 (f26 ?v1 ?v4) ?v5) f1) (forall ((?v6 S6)) (=> (= (f7 (f9 (f10 (f11 ?v2) ?v5) ?v0) ?v6) f1) (= (f7 (f26 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S10) (?v1 S6) (?v2 S2) (?v3 S6) (?v4 S10) (?v5 S6) (?v6 S2) (?v7 S6)) (=> (= (f7 (f9 (f10 (f11 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f7 (f9 (f10 (f11 ?v4) ?v5) ?v6) ?v7) f1) (exists ((?v8 S2)) (and (= (f7 (f9 (f10 (f11 ?v0) ?v1) ?v8) ?v3) f1) (= (f7 (f9 (f10 (f11 ?v4) ?v5) ?v8) ?v7) f1)))))))
(assert (forall ((?v0 S6) (?v1 S2)) (= (f7 (f9 (f10 (f11 f27) ?v0) ?v1) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (=> (= (f7 (f9 (f10 (f11 f27) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S15) (?v1 S10) (?v2 S15) (?v3 S15) (?v4 S10) (?v5 S15)) (= (= (f22 (f23 (f24 f25 ?v0) ?v1) ?v2) (f22 (f23 (f24 f25 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S7) (?v1 S10)) (not (= (f12 (f13 f14 ?v0) ?v1) f27))))
(assert (forall ((?v0 S7) (?v1 S10)) (not (= f27 (f12 (f13 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S19) (?v1 S15) (?v2 S10) (?v3 S15)) (= (f28 (f29 f30 ?v0) (f22 (f23 (f24 f25 ?v1) ?v2) ?v3)) (f17 f18 0))))
(assert (forall ((?v0 S15) (?v1 S10) (?v2 S15)) (= (f28 f31 (f22 (f23 (f24 f25 ?v0) ?v1) ?v2)) (f17 f18 0))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S15) (?v2 S10) (?v3 S15)) (=> (= ?v0 (f22 (f23 (f24 f25 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S15) (?v1 S22) (?v2 S15)) (= (f5 (f6 (f17 f18 0)) (f22 (f23 (f24 f25 ?v0) (f32 f33 ?v1)) ?v2)) f1)))
(assert (= (f34 f35 f27) (f17 f18 0)))
(assert (forall ((?v0 S7) (?v1 S10)) (= (f34 f35 (f12 (f13 f14 ?v0) ?v1)) (f17 f18 (+ (f19 f20 (f34 f35 ?v1)) (+ 0 1))))))
(assert (= (f34 f36 f27) (f17 f18 0)))
(assert (forall ((?v0 S10) (?v1 S6) (?v2 S2) (?v3 S6) (?v4 S10) (?v5 S6)) (=> (= (f7 (f9 (f10 (f11 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f7 (f9 (f10 (f11 ?v4) ?v3) ?v2) ?v5) f1) (= (f7 (f9 (f10 (f11 (f12 (f37 f38 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (forall ((?v0 S7) (?v1 S10)) (= (f34 f36 (f12 (f13 f14 ?v0) ?v1)) (f17 f18 (+ (f19 f20 (f34 f36 ?v1)) (+ 0 1))))))
(assert (forall ((?v0 S22) (?v1 S10) (?v2 S10)) (not (= (f32 f33 ?v0) (f12 (f37 f38 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S22)) (not (= (f12 (f37 f38 ?v0) ?v1) (f32 f33 ?v2)))))
(assert (forall ((?v0 S22)) (= (f34 f35 (f32 f33 ?v0)) (f17 f18 0))))
(assert (forall ((?v0 S2)) (= (f17 f18 (f19 f20 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f19 f20 (f17 f18 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f19 f20 (f17 f18 ?v0)) 0))))
(check-sat)
(exit)

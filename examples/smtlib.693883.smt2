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
(declare-sort S26 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 (S7 S8) S5)
(declare-fun f7 (S9 S6) S7)
(declare-fun f8 () S9)
(declare-fun f9 (S2) S6)
(declare-fun f10 (S10 S11) S8)
(declare-fun f11 () S10)
(declare-fun f12 (S2) S11)
(declare-fun f13 (S2) S6)
(declare-fun f14 () S3)
(declare-fun f15 (S12 S2) S8)
(declare-fun f16 () S12)
(declare-fun f17 (S13 S4) S1)
(declare-fun f18 (S13) S13)
(declare-fun f19 (S4 S13) S1)
(declare-fun f20 (S14 S2) S1)
(declare-fun f21 (S14) S14)
(declare-fun f22 (S2 S14) S1)
(declare-fun f23 (S16 S15) S3)
(declare-fun f24 (S17 S15) S16)
(declare-fun f25 () S17)
(declare-fun f26 (S15 S2) S6)
(declare-fun f27 () S17)
(declare-fun f28 (S18 S13) S13)
(declare-fun f29 (S13) S18)
(declare-fun f30 (S19 S14) S14)
(declare-fun f31 (S14) S19)
(declare-fun f32 (S13 S13) S1)
(declare-fun f33 () S13)
(declare-fun f34 (S20 S14) S13)
(declare-fun f35 (S3) S20)
(declare-fun f36 () S14)
(declare-fun f37 (S13) S18)
(declare-fun f38 () S13)
(declare-fun f39 (S13 S13) S1)
(declare-fun f40 (S14) S19)
(declare-fun f41 (S14 S14) S1)
(declare-fun f42 (S21) S13)
(declare-fun f43 (S22 Int) S21)
(declare-fun f44 () S22)
(declare-fun f45 (S23 S21) Int)
(declare-fun f46 () S23)
(declare-fun f47 (S25 S4) S21)
(declare-fun f48 (S26 S24) S25)
(declare-fun f49 () S26)
(declare-fun f50 (S13) S13)
(declare-fun f51 (S14) S14)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 (f9 ?v0)) (f10 f11 (f12 ?v0))) (f13 ?v0)))))
(assert (forall ((?v0 S2)) (= (f3 f14 ?v0) (f5 (f6 (f7 f8 (f9 ?v0)) (f15 f16 ?v0)) (f13 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S4)) (= (= (f17 (f18 ?v0) ?v1) f1) (= (f19 ?v1 ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S2)) (= (= (f20 (f21 ?v0) ?v1) f1) (= (f22 ?v1 ?v0) f1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S2)) (= (f3 (f23 (f24 f25 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f26 ?v0 ?v2)) (f10 f11 (f12 ?v2))) (f26 ?v1 ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S2)) (= (f3 (f23 (f24 f27 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f26 ?v0 ?v2)) (f15 f16 ?v2)) (f26 ?v1 ?v2)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f17 (f28 (f29 ?v0) ?v1) ?v2) f1) (or (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f20 (f30 (f31 ?v0) ?v1) ?v2) f1) (or (= (f22 ?v2 ?v0) f1) (= (f22 ?v2 ?v1) f1)))))
(assert (not (= (f32 f33 (f34 (f35 f14) f36)) f1)))
(assert (= (f32 (f28 (f37 f38) (f34 (f35 f14) f36)) (f34 (f35 f4) f36)) f1))
(assert (forall ((?v0 S13)) (=> (= (f39 (f28 (f37 f38) (f34 (f35 f14) f36)) ?v0) f1) (= (f32 ?v0 (f34 (f35 f4) f36)) f1))))
(assert (= (f39 f38 f33) f1))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f39 ?v0 ?v1) f1) (= (f32 ?v1 ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f39 ?v2 ?v1) f1) (= (f32 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f32 ?v2 ?v0) f1) (= (f32 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S15) (?v2 S15) (?v3 S14)) (let ((?v_0 (f34 (f35 (f23 (f24 f27 ?v1) ?v2)) ?v3))) (=> (= (f32 (f28 (f37 ?v0) ?v_0) (f34 (f35 (f23 (f24 f25 ?v1) ?v2)) ?v3)) f1) (= (f32 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f19 ?v0 (f28 (f37 ?v1) ?v2)) f1) (=> (=> (= (f19 ?v0 ?v1) f1) false) (=> (=> (= (f19 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f22 ?v0 (f30 (f40 ?v1) ?v2)) f1) (=> (=> (= (f22 ?v0 ?v1) f1) false) (=> (=> (= (f22 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (=> (= (f17 (f28 (f37 ?v0) ?v1) ?v2) f1) (=> (=> (= (f17 ?v0 ?v2) f1) false) (=> (=> (= (f17 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (=> (= (f20 (f30 (f40 ?v0) ?v1) ?v2) f1) (=> (=> (= (f20 ?v0 ?v2) f1) false) (=> (=> (= (f20 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (=> (not (= (f17 ?v0 ?v1) f1)) (= (f17 ?v2 ?v1) f1)) (= (f17 (f28 (f37 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (=> (not (= (f20 ?v0 ?v1) f1)) (= (f20 ?v2 ?v1) f1)) (= (f20 (f30 (f40 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (=> (not (= (f19 ?v0 ?v1) f1)) (= (f19 ?v0 ?v2) f1)) (= (f19 ?v0 (f28 (f37 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (=> (not (= (f22 ?v0 ?v1) f1)) (= (f22 ?v0 ?v2) f1)) (= (f22 ?v0 (f30 (f40 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S14)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f22 ?v2 ?v3) f1) (= (f19 ?v0 (f34 (f35 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f22 ?v2 ?v0) f1) (= (f22 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f39 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f41 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S21) (?v1 S6) (?v2 S2) (?v3 S6)) (let ((?v_0 (f7 f8 ?v1))) (= (= (f17 (f42 ?v0) (f5 (f6 ?v_0 (f10 f11 (f12 ?v2))) ?v3)) f1) (= (f17 (f42 (f43 f44 (+ (f45 f46 ?v0) 1))) (f5 (f6 ?v_0 (f15 f16 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S24) (?v1 S6) (?v2 S8) (?v3 S6)) (= (f47 (f48 f49 ?v0) (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) (f43 f44 0))))
(assert (forall ((?v0 S13)) (= (f39 ?v0 ?v0) f1)))
(assert (forall ((?v0 S14)) (= (f41 ?v0 ?v0) f1)))
(assert (forall ((?v0 S21) (?v1 S4)) (=> (= (f17 (f42 (f43 f44 (+ (f45 f46 ?v0) 1))) ?v1) f1) (= (f17 (f42 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S21)) (=> (forall ((?v2 S4)) (=> (= (f19 ?v2 ?v0) f1) (= (f17 (f42 (f43 f44 (+ (f45 f46 ?v1) 1))) ?v2) f1))) (forall ((?v2 S4)) (=> (= (f19 ?v2 ?v0) f1) (= (f17 (f42 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f39 ?v2 ?v0) f1) (= (f39 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f41 ?v2 ?v0) f1) (= (f41 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f39 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f41 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f39 ?v1 ?v2) f1) (= (f39 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f41 ?v1 ?v2) f1) (= (f41 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f39 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f41 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f39 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f41 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f39 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f41 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f39 ?v2 ?v1) f1) (= (f39 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= ?v0 ?v1) (=> (= (f41 ?v2 ?v1) f1) (= (f41 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f39 ?v1 ?v2) f1) (= (f39 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= ?v0 ?v1) (=> (= (f41 ?v1 ?v2) f1) (= (f41 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f39 ?v0 ?v1) f1) (= (= (f39 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f41 ?v0 ?v1) f1) (= (= (f41 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f39 ?v0 ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= ?v0 ?v1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= ?v0 ?v1) (and (= (f39 ?v0 ?v1) f1) (= (f39 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= ?v0 ?v1) (and (= (f41 ?v0 ?v1) f1) (= (f41 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (=> (=> (= (f39 ?v0 ?v1) f1) (=> (= (f39 ?v1 ?v0) f1) false)) false))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= ?v0 ?v1) (=> (=> (= (f41 ?v0 ?v1) f1) (=> (= (f41 ?v1 ?v0) f1) false)) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f39 ?v1 ?v2) f1) (= (f39 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f41 ?v1 ?v2) f1) (= (f41 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f22 ?v2 ?v0) f1) (= (f22 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f39 ?v1 ?v2) f1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f22 ?v0 ?v1) f1) (=> (= (f41 ?v1 ?v2) f1) (= (f22 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f17 ?v0 ?v2) f1) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f20 ?v0 ?v2) f1) (= (f20 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (=> (= (f39 ?v0 ?v1) f1) (=> (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f22 ?v2 ?v0) f1) (= (f22 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f39 ?v1 ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= ?v0 ?v1) (= (f41 ?v1 ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f39 ?v0 ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= ?v0 ?v1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f39 ?v0 ?v2) f1) (= (f17 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (= (f20 ?v0 ?v1) f1) (=> (= (f41 ?v0 ?v2) f1) (= (f20 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= ?v0 ?v1) (and (= (f39 ?v0 ?v1) f1) (= (f39 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= ?v0 ?v1) (and (= (f41 ?v0 ?v1) f1) (= (f41 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S13)) (= (f39 ?v0 ?v0) f1)))
(assert (forall ((?v0 S14)) (= (f41 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S4) (?v3 S3)) (=> (= (f22 ?v0 ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f19 ?v2 (f34 (f35 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S3)) (=> (= (f22 ?v0 ?v1) f1) (= (f19 (f3 ?v2 ?v0) (f34 (f35 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S14)) (= (= (f19 ?v0 (f34 (f35 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f22 ?v3 ?v2) f1) (= ?v0 (f3 ?v1 ?v3)))))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 (f28 (f37 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 (f30 (f40 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 (f28 (f37 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 (f30 (f40 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (= (f17 ?v0 ?v1) f1) (= (f17 (f28 (f37 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (= (f20 ?v0 ?v1) f1) (= (f20 (f30 (f40 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (= (f17 ?v0 ?v1) f1) (= (f17 (f28 (f37 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (= (f20 ?v0 ?v1) f1) (= (f20 (f30 (f40 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (= (forall ((?v3 S4)) (=> (= (f19 ?v3 (f28 (f37 ?v0) ?v1)) f1) (= (f17 ?v2 ?v3) f1))) (and (forall ((?v3 S4)) (=> (= (f19 ?v3 ?v0) f1) (= (f17 ?v2 ?v3) f1))) (forall ((?v3 S4)) (=> (= (f19 ?v3 ?v1) f1) (= (f17 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (forall ((?v3 S2)) (=> (= (f22 ?v3 (f30 (f40 ?v0) ?v1)) f1) (= (f20 ?v2 ?v3) f1))) (and (forall ((?v3 S2)) (=> (= (f22 ?v3 ?v0) f1) (= (f20 ?v2 ?v3) f1))) (forall ((?v3 S2)) (=> (= (f22 ?v3 ?v1) f1) (= (f20 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (= (exists ((?v3 S4)) (and (= (f19 ?v3 (f28 (f37 ?v0) ?v1)) f1) (= (f17 ?v2 ?v3) f1))) (or (exists ((?v3 S4)) (and (= (f19 ?v3 ?v0) f1) (= (f17 ?v2 ?v3) f1))) (exists ((?v3 S4)) (and (= (f19 ?v3 ?v1) f1) (= (f17 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (exists ((?v3 S2)) (and (= (f22 ?v3 (f30 (f40 ?v0) ?v1)) f1) (= (f20 ?v2 ?v3) f1))) (or (exists ((?v3 S2)) (and (= (f22 ?v3 ?v0) f1) (= (f20 ?v2 ?v3) f1))) (exists ((?v3 S2)) (and (= (f22 ?v3 ?v1) f1) (= (f20 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f37 ?v0))) (= (f28 (f37 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f37 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f40 ?v0))) (= (f30 (f40 (f30 ?v_0 ?v1)) ?v2) (f30 ?v_0 (f30 (f40 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (= (= (f19 ?v0 (f28 (f37 ?v1) ?v2)) f1) (or (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (= (= (f22 ?v0 (f30 (f40 ?v1) ?v2)) f1) (or (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_1 (f37 ?v0)) (?v_0 (f37 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f40 ?v0)) (?v_0 (f40 ?v1))) (= (f30 ?v_1 (f30 ?v_0 ?v2)) (f30 ?v_0 (f30 ?v_1 ?v2))))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f37 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f40 ?v0))) (let ((?v_1 (f30 ?v_0 ?v1))) (= (f30 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f28 (f37 ?v0) ?v1) (f28 (f37 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f30 (f40 ?v0) ?v1) (f30 (f40 ?v1) ?v0))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f28 (f37 ?v0) ?v1) (f50 (f28 (f29 ?v0) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f30 (f40 ?v0) ?v1) (f51 (f30 (f31 ?v0) ?v1)))))
(assert (forall ((?v0 S13)) (= (f28 (f37 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f30 (f40 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (= (f17 (f42 (f43 f44 0)) (f5 (f6 (f7 f8 ?v0) (f15 f16 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f39 (f18 ?v0) (f18 ?v1)) f1) (= (f39 ?v0 ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f41 (f21 ?v0) (f21 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S21)) (= (f43 f44 (f45 f46 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f45 f46 (f43 f44 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f45 f46 (f43 f44 ?v0)) 0))))
(check-sat)
(exit)

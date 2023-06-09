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
(declare-sort S27 0)
(declare-sort S28 0)
(declare-sort S29 0)
(declare-sort S30 0)
(declare-sort S31 0)
(declare-sort S32 0)
(declare-sort S33 0)
(declare-sort S34 0)
(declare-sort S35 0)
(declare-sort S36 0)
(declare-sort S37 0)
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
(declare-fun f15 () S6)
(declare-fun f16 (S8) S6)
(declare-fun f17 () S3)
(declare-fun f18 (S12 S2) S8)
(declare-fun f19 () S12)
(declare-fun f20 (S13 S4) S1)
(declare-fun f21 (S13) S13)
(declare-fun f22 (S4 S13) S1)
(declare-fun f23 (S14 S2) S1)
(declare-fun f24 (S14) S14)
(declare-fun f25 (S2 S14) S1)
(declare-fun f26 (S4) S13)
(declare-fun f27 (S16 S15) S1)
(declare-fun f28 (S6 S15) S16)
(declare-fun f29 (S2) S14)
(declare-fun f30 (S18 S17) S3)
(declare-fun f31 (S19 S17) S18)
(declare-fun f32 () S19)
(declare-fun f33 (S17 S2) S6)
(declare-fun f34 () S19)
(declare-fun f35 (S20 S13) S13)
(declare-fun f36 (S13) S20)
(declare-fun f37 (S21 S14) S14)
(declare-fun f38 (S14) S21)
(declare-fun f39 (S13) S20)
(declare-fun f40 (S14) S21)
(declare-fun f41 (S23 S2) S2)
(declare-fun f42 (S24 S3) S23)
(declare-fun f43 (S25 S22) S24)
(declare-fun f44 () S25)
(declare-fun f45 (S22 S4) S2)
(declare-fun f46 (S26 S4) S4)
(declare-fun f47 (S27 S22) S26)
(declare-fun f48 (S28 S3) S27)
(declare-fun f49 () S28)
(declare-fun f50 () S13)
(declare-fun f51 () S14)
(declare-fun f52 (S13 S13) S1)
(declare-fun f53 (S13) S20)
(declare-fun f54 () S13)
(declare-fun f55 (S29 S14) S13)
(declare-fun f56 (S3) S29)
(declare-fun f57 () S14)
(declare-fun f58 (S13 S13) S1)
(declare-fun f59 (S14) S21)
(declare-fun f60 (S30 S13) S14)
(declare-fun f61 (S22) S30)
(declare-fun f62 (S31) S13)
(declare-fun f63 (S32 Int) S31)
(declare-fun f64 () S32)
(declare-fun f65 (S33 S31) Int)
(declare-fun f66 () S33)
(declare-fun f67 (S35 S4) S31)
(declare-fun f68 (S36 S34) S35)
(declare-fun f69 () S36)
(declare-fun f70 (S14) S14)
(declare-fun f71 (S13) S13)
(declare-fun f72 (S23) S21)
(declare-fun f73 (S26) S20)
(declare-fun f74 (S1 S1) S1)
(declare-fun f75 (S37 S8) S4)
(declare-fun f76 () S37)
(declare-fun f77 () S35)
(declare-fun f78 (S8 S15 S31 S15) S1)
(declare-fun f79 (S4) S20)
(declare-fun f80 () S13)
(declare-fun f81 () S14)
(declare-fun f82 (S2) S21)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 (f9 ?v0)) (f10 f11 (f12 ?v0))) (f13 ?v0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f10 f11 (f12 ?v0)))) (= (f3 f14 ?v0) (f5 (f6 (f7 f8 f15) ?v_0) (f16 ?v_0))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f18 f19 ?v0))) (= (f3 f17 ?v0) (f5 (f6 (f7 f8 f15) ?v_0) (f16 ?v_0))))))
(assert (forall ((?v0 S13) (?v1 S4)) (= (= (f20 (f21 ?v0) ?v1) f1) (= (f22 ?v1 ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S2)) (= (= (f23 (f24 ?v0) ?v1) f1) (= (f25 ?v1 ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f20 (f26 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f27 (f28 f15 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f23 (f29 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S2)) (= (f3 (f30 (f31 f32 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f33 ?v0 ?v2)) (f10 f11 (f12 ?v2))) (f33 ?v1 ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S2)) (= (f3 (f30 (f31 f34 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f33 ?v0 ?v2)) (f18 f19 ?v2)) (f33 ?v1 ?v2)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f20 (f35 (f36 ?v0) ?v1) ?v2) f1) (or (= (f22 ?v2 ?v0) f1) (= (f22 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f23 (f37 (f38 ?v0) ?v1) ?v2) f1) (or (= (f25 ?v2 ?v0) f1) (= (f25 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f20 (f35 (f39 ?v0) ?v1) ?v2) f1) (or (= (f20 ?v0 ?v2) f1) (= (f20 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f23 (f37 (f40 ?v0) ?v1) ?v2) f1) (or (= (f23 ?v0 ?v2) f1) (= (f23 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S22) (?v1 S3) (?v2 S2)) (= (f41 (f42 (f43 f44 ?v0) ?v1) ?v2) (f45 ?v0 (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S22) (?v2 S4)) (= (f46 (f47 (f48 f49 ?v0) ?v1) ?v2) (f3 ?v0 (f45 ?v1 ?v2)))))
(assert (forall ((?v0 S4)) (= (= (f20 f50 ?v0) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f23 f51 ?v0) f1) false)))
(assert (not (= (f52 (f35 (f53 f54) (f55 (f56 f17) f57)) (f55 (f56 f4) f57)) f1)))
(assert (= (f52 (f35 (f53 f54) (f55 (f56 f17) f57)) (f55 (f56 f14) f57)) f1))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f52 ?v0 ?v1) f1) (=> (= (f52 ?v2 ?v0) f1) (= (f52 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S17) (?v2 S17) (?v3 S14)) (let ((?v_0 (f55 (f56 (f30 (f31 f34 ?v1) ?v2)) ?v3))) (=> (= (f52 (f35 (f53 ?v0) ?v_0) (f55 (f56 (f30 (f31 f32 ?v1) ?v2)) ?v3)) f1) (= (f52 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S2) (?v1 S15) (?v2 S15)) (=> (= (f27 (f28 (f16 (f18 f19 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f27 (f28 (f16 (f10 f11 (f12 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S15) (?v2 S15)) (=> (= (f27 (f28 (f16 (f10 f11 (f12 ?v0))) ?v1) ?v2) f1) (= (f27 (f28 (f16 (f18 f19 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S13) (?v1 S17) (?v2 S17) (?v3 S14)) (let ((?v_0 (f55 (f56 (f30 (f31 f34 ?v1) ?v2)) ?v3))) (=> (= (f58 (f35 (f53 ?v0) ?v_0) (f55 (f56 (f30 (f31 f32 ?v1) ?v2)) ?v3)) f1) (= (f58 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f25 ?v0 (f37 (f59 ?v1) ?v2)) f1) (=> (=> (= (f25 ?v0 ?v1) f1) false) (=> (=> (= (f25 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f22 ?v0 (f35 (f53 ?v1) ?v2)) f1) (=> (=> (= (f22 ?v0 ?v1) f1) false) (=> (=> (= (f22 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (=> (= (f20 (f35 (f53 ?v0) ?v1) ?v2) f1) (=> (=> (= (f20 ?v0 ?v2) f1) false) (=> (=> (= (f20 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (=> (= (f23 (f37 (f59 ?v0) ?v1) ?v2) f1) (=> (=> (= (f23 ?v0 ?v2) f1) false) (=> (=> (= (f23 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (=> (not (= (f20 ?v0 ?v1) f1)) (= (f20 ?v2 ?v1) f1)) (= (f20 (f35 (f53 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (=> (not (= (f23 ?v0 ?v1) f1)) (= (f23 ?v2 ?v1) f1)) (= (f23 (f37 (f59 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (=> (not (= (f25 ?v0 ?v1) f1)) (= (f25 ?v0 ?v2) f1)) (= (f25 ?v0 (f37 (f59 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (=> (not (= (f22 ?v0 ?v1) f1)) (= (f22 ?v0 ?v2) f1)) (= (f22 ?v0 (f35 (f53 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S14)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f25 ?v2 ?v3) f1) (= (f22 ?v0 (f55 (f56 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S22) (?v2 S4) (?v3 S13)) (=> (= ?v0 (f45 ?v1 ?v2)) (=> (= (f22 ?v2 ?v3) f1) (= (f25 ?v0 (f60 (f61 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S31) (?v1 S6) (?v2 S2) (?v3 S6)) (let ((?v_0 (f7 f8 ?v1))) (= (= (f20 (f62 ?v0) (f5 (f6 ?v_0 (f10 f11 (f12 ?v2))) ?v3)) f1) (= (f20 (f62 (f63 f64 (+ (f65 f66 ?v0) 1))) (f5 (f6 ?v_0 (f18 f19 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S34) (?v1 S6) (?v2 S8) (?v3 S6)) (= (f67 (f68 f69 ?v0) (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) (f63 f64 0))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f58 ?v0 ?v1) f1) (forall ((?v2 S31)) (=> (forall ((?v3 S4)) (=> (= (f22 ?v3 ?v0) f1) (= (f20 (f62 ?v2) ?v3) f1))) (forall ((?v3 S4)) (=> (= (f22 ?v3 ?v1) f1) (= (f20 (f62 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S31) (?v1 S4)) (=> (= (f20 (f62 (f63 f64 (+ (f65 f66 ?v0) 1))) ?v1) f1) (= (f20 (f62 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S31)) (=> (forall ((?v2 S4)) (=> (= (f22 ?v2 ?v0) f1) (= (f20 (f62 (f63 f64 (+ (f65 f66 ?v1) 1))) ?v2) f1))) (forall ((?v2 S4)) (=> (= (f22 ?v2 ?v0) f1) (= (f20 (f62 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f52 ?v0 ?v1) f1) (= (f58 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S4) (?v3 S3)) (=> (= (f25 ?v0 ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f22 ?v2 (f55 (f56 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S2) (?v3 S22)) (=> (= (f22 ?v0 ?v1) f1) (=> (= ?v2 (f45 ?v3 ?v0)) (= (f25 ?v2 (f60 (f61 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S3)) (=> (= (f25 ?v0 ?v1) f1) (= (f22 (f3 ?v2 ?v0) (f55 (f56 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S22)) (=> (= (f22 ?v0 ?v1) f1) (= (f25 (f45 ?v2 ?v0) (f60 (f61 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S14)) (= (= (f22 ?v0 (f55 (f56 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f25 ?v3 ?v2) f1) (= ?v0 (f3 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S22) (?v2 S13)) (= (= (f25 ?v0 (f60 (f61 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f22 ?v3 ?v2) f1) (= ?v0 (f45 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f25 ?v0 ?v1) f1) (= (f25 ?v0 (f37 (f59 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 (f35 (f53 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f25 ?v0 ?v1) f1) (= (f25 ?v0 (f37 (f59 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 (f35 (f53 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (= (f20 ?v0 ?v1) f1) (= (f20 (f35 (f53 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (= (f23 ?v0 ?v1) f1) (= (f23 (f37 (f59 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (= (f20 ?v0 ?v1) f1) (= (f20 (f35 (f53 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (= (f23 ?v0 ?v1) f1) (= (f23 (f37 (f59 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (forall ((?v3 S2)) (=> (= (f25 ?v3 (f37 (f59 ?v0) ?v1)) f1) (= (f23 ?v2 ?v3) f1))) (and (forall ((?v3 S2)) (=> (= (f25 ?v3 ?v0) f1) (= (f23 ?v2 ?v3) f1))) (forall ((?v3 S2)) (=> (= (f25 ?v3 ?v1) f1) (= (f23 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (= (forall ((?v3 S4)) (=> (= (f22 ?v3 (f35 (f53 ?v0) ?v1)) f1) (= (f20 ?v2 ?v3) f1))) (and (forall ((?v3 S4)) (=> (= (f22 ?v3 ?v0) f1) (= (f20 ?v2 ?v3) f1))) (forall ((?v3 S4)) (=> (= (f22 ?v3 ?v1) f1) (= (f20 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (exists ((?v3 S2)) (and (= (f25 ?v3 (f37 (f59 ?v0) ?v1)) f1) (= (f23 ?v2 ?v3) f1))) (or (exists ((?v3 S2)) (and (= (f25 ?v3 ?v0) f1) (= (f23 ?v2 ?v3) f1))) (exists ((?v3 S2)) (and (= (f25 ?v3 ?v1) f1) (= (f23 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (= (exists ((?v3 S4)) (and (= (f22 ?v3 (f35 (f53 ?v0) ?v1)) f1) (= (f20 ?v2 ?v3) f1))) (or (exists ((?v3 S4)) (and (= (f22 ?v3 ?v0) f1) (= (f20 ?v2 ?v3) f1))) (exists ((?v3 S4)) (and (= (f22 ?v3 ?v1) f1) (= (f20 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f53 ?v0))) (= (f35 (f53 (f35 ?v_0 ?v1)) ?v2) (f35 ?v_0 (f35 (f53 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f59 ?v0))) (= (f37 (f59 (f37 ?v_0 ?v1)) ?v2) (f37 ?v_0 (f37 (f59 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (= (= (f25 ?v0 (f37 (f59 ?v1) ?v2)) f1) (or (= (f25 ?v0 ?v1) f1) (= (f25 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (= (= (f22 ?v0 (f35 (f53 ?v1) ?v2)) f1) (or (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_1 (f53 ?v0)) (?v_0 (f53 ?v1))) (= (f35 ?v_1 (f35 ?v_0 ?v2)) (f35 ?v_0 (f35 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f59 ?v0)) (?v_0 (f59 ?v1))) (= (f37 ?v_1 (f37 ?v_0 ?v2)) (f37 ?v_0 (f37 ?v_1 ?v2))))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f53 ?v0))) (let ((?v_1 (f35 ?v_0 ?v1))) (= (f35 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f59 ?v0))) (let ((?v_1 (f37 ?v_0 ?v1))) (= (f37 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f35 (f53 ?v0) ?v1) (f35 (f53 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f37 (f59 ?v0) ?v1) (f37 (f59 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f37 (f59 ?v0) ?v1) (f70 (f37 (f38 ?v0) ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f35 (f53 ?v0) ?v1) (f71 (f35 (f36 ?v0) ?v1)))))
(assert (forall ((?v0 S13)) (= (f35 (f53 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f37 (f59 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S8) (?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_0 (f28 (f16 ?v0) ?v1))) (=> (= (f27 ?v_0 ?v2) f1) (=> (= (f27 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (= (f20 (f62 (f63 f64 0)) (f5 (f6 (f7 f8 ?v0) (f18 f19 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S22) (?v1 S3) (?v2 S14)) (= (f60 (f61 ?v0) (f55 (f56 ?v1) ?v2)) (f37 (f72 (f42 (f43 f44 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S22) (?v2 S13)) (= (f55 (f56 ?v0) (f60 (f61 ?v1) ?v2)) (f35 (f73 (f47 (f48 f49 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f23 (f37 (f59 (f24 ?v0)) (f24 ?v1)) ?v2) f1) (= (f25 ?v2 (f37 (f59 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f20 (f35 (f53 (f21 ?v0)) (f21 ?v1)) ?v2) f1) (= (f22 ?v2 (f35 (f53 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f71 (f35 (f39 ?v0) ?v1)) (f35 (f53 (f71 ?v0)) (f71 ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f70 (f37 (f40 ?v0) ?v1)) (f37 (f59 (f70 ?v0)) (f70 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S14) (?v2 S14)) (let ((?v_0 (f56 ?v0))) (= (f55 ?v_0 (f37 (f59 ?v1) ?v2)) (f35 (f53 (f55 ?v_0 ?v1)) (f55 ?v_0 ?v2))))))
(assert (forall ((?v0 S22) (?v1 S13) (?v2 S13)) (let ((?v_0 (f61 ?v0))) (= (f60 ?v_0 (f35 (f53 ?v1) ?v2)) (f37 (f59 (f60 ?v_0 ?v1)) (f60 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S14)) (=> (= (f22 ?v0 (f55 (f56 ?v1) ?v2)) f1) (=> (forall ((?v3 S2)) (=> (= ?v0 (f3 ?v1 ?v3)) (=> (= (f25 ?v3 ?v2) f1) false))) false))))
(assert (forall ((?v0 S2) (?v1 S22) (?v2 S13)) (=> (= (f25 ?v0 (f60 (f61 ?v1) ?v2)) f1) (=> (forall ((?v3 S4)) (=> (= ?v0 (f45 ?v1 ?v3)) (=> (= (f22 ?v3 ?v2) f1) false))) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f20 (f35 (f53 ?v0) ?v1) ?v2) f1) (= (f74 (f20 ?v0 ?v2) (f20 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f23 (f37 (f59 ?v0) ?v1) ?v2) f1) (= (f74 (f23 ?v0 ?v2) (f23 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f20 (f35 (f53 ?v0) ?v1) ?v2) f1) (= (f74 (f20 ?v0 ?v2) (f20 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f23 (f37 (f59 ?v0) ?v1) ?v2) f1) (= (f74 (f23 ?v0 ?v2) (f23 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S8)) (= (f75 f76 ?v0) (f5 (f6 (f7 f8 f15) ?v0) (f16 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6)) (= (f67 f77 (f5 (f6 (f7 f8 ?v0) ?v1) ?v2)) (f63 f64 0))))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S6) (?v2 S8) (?v3 S6)) (=> (= ?v0 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S15) (?v2 S31) (?v3 S15)) (=> (= (f78 (f10 f11 (f12 ?v0)) ?v1 ?v2 ?v3) f1) (= (f78 (f18 f19 ?v0) ?v1 (f63 f64 (+ (f65 f66 ?v2) 1)) ?v3) f1))))
(assert (forall ((?v0 S13) (?v1 S17) (?v2 S17) (?v3 S14) (?v4 S2)) (=> (= (f52 (f35 (f53 ?v0) (f55 (f56 (f30 (f31 f34 ?v1) ?v2)) ?v3)) (f55 (f56 (f30 (f31 f32 ?v1) ?v2)) ?v3)) f1) (=> (= (f25 ?v4 ?v3) f1) (= (f52 ?v0 (f35 (f79 (f5 (f6 (f7 f8 (f33 ?v1 ?v4)) (f18 f19 ?v4)) (f33 ?v2 ?v4))) f80)) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S3) (?v3 S3)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f25 ?v4 ?v1) f1) (= (f3 ?v2 ?v4) (f3 ?v3 ?v4)))) (= (f55 (f56 ?v2) ?v0) (f55 (f56 ?v3) ?v1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22) (?v3 S22)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S4)) (=> (= (f22 ?v4 ?v1) f1) (= (f45 ?v2 ?v4) (f45 ?v3 ?v4)))) (= (f60 (f61 ?v2) ?v0) (f60 (f61 ?v3) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f18 f19 ?v0) (f18 f19 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (=> (= (f25 ?v0 f81) f1) false)))
(assert (forall ((?v0 S4)) (=> (= (f22 ?v0 f80) f1) false)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S14)) (=> (= (f25 ?v0 (f37 (f82 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f25 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S13)) (=> (= (f22 ?v0 (f35 (f79 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f22 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (=> (=> (not (= (f25 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f25 ?v0 (f37 (f82 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4)) (=> (=> (not (= (f22 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f22 ?v0 (f35 (f79 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13)) (not (= f80 (f35 (f79 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S14)) (not (= f81 (f37 (f82 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S13)) (not (= (f35 (f79 ?v0) ?v1) f80))))
(assert (forall ((?v0 S2) (?v1 S14)) (not (= (f37 (f82 ?v0) ?v1) f81))))
(assert (forall ((?v0 S2)) (= (= (f23 f81 ?v0) f1) (= (f25 ?v0 f81) f1))))
(assert (forall ((?v0 S4)) (= (= (f20 f80 ?v0) f1) (= (f22 ?v0 f80) f1))))
(assert (= f81 (f70 f51)))
(assert (= f80 (f71 f50)))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f25 ?v0 (f37 (f82 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f22 ?v0 (f35 (f79 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S2)) (not (= (f25 ?v1 ?v0) f1))) (= ?v0 f81))))
(assert (forall ((?v0 S13)) (= (forall ((?v1 S4)) (not (= (f22 ?v1 ?v0) f1))) (= ?v0 f80))))
(assert (forall ((?v0 S4)) (= (f71 (f26 ?v0)) (f35 (f79 ?v0) f80))))
(assert (forall ((?v0 S2)) (= (f70 (f29 ?v0)) (f37 (f82 ?v0) f81))))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S2)) (= (f25 ?v1 ?v0) f1)) (not (= ?v0 f81)))))
(assert (forall ((?v0 S13)) (= (exists ((?v1 S4)) (= (f22 ?v1 ?v0) f1)) (not (= ?v0 f80)))))
(assert (forall ((?v0 S31)) (= (f63 f64 (f65 f66 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f65 f66 (f63 f64 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f65 f66 (f63 f64 ?v0)) 0))))
(check-sat)
(exit)

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
(declare-sort S38 0)
(declare-sort S39 0)
(declare-sort S40 0)
(declare-sort S41 0)
(declare-sort S42 0)
(declare-sort S43 0)
(declare-sort S44 0)
(declare-sort S45 0)
(declare-sort S46 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S2 S3) S1)
(declare-fun f7 (S2) S4)
(declare-fun f8 () S3)
(declare-fun f9 (S5 S6) S1)
(declare-fun f10 (S7 S6) S5)
(declare-fun f11 (S2) S7)
(declare-fun f12 () S2)
(declare-fun f13 () S6)
(declare-fun f14 () S6)
(declare-fun f15 () S1)
(declare-fun f16 (S8 S6) S6)
(declare-fun f17 (S9 S6) S8)
(declare-fun f18 () S9)
(declare-fun f19 () S2)
(declare-fun f20 (S10 S2) S2)
(declare-fun f21 (S11 S2) S10)
(declare-fun f22 () S11)
(declare-fun f23 (S12 S5) S11)
(declare-fun f24 () S12)
(declare-fun f25 (S13 S5) S10)
(declare-fun f26 () S13)
(declare-fun f27 (S14 S2) S15)
(declare-fun f28 () S14)
(declare-fun f29 (S16 Int) S15)
(declare-fun f30 () S16)
(declare-fun f31 (S17 S15) Int)
(declare-fun f32 () S17)
(declare-fun f33 () S14)
(declare-fun f34 (S2) S1)
(declare-fun f35 (S20 S19) S2)
(declare-fun f36 (S21 S18) S20)
(declare-fun f37 () S21)
(declare-fun f38 (S23 S19) S10)
(declare-fun f39 (S24 S22) S23)
(declare-fun f40 () S24)
(declare-fun f41 (S25 S15) S5)
(declare-fun f42 (S26 S6) S25)
(declare-fun f43 (S2) S26)
(declare-fun f44 (S28 S27) S20)
(declare-fun f45 (S29 S18) S28)
(declare-fun f46 () S29)
(declare-fun f47 (S3) S3)
(declare-fun f48 (S30 S15) S6)
(declare-fun f49 (S31 S18) S30)
(declare-fun f50 (S32 S6) S31)
(declare-fun f51 () S32)
(declare-fun f52 (S19 S6) S15)
(declare-fun f53 (S33 S27) S2)
(declare-fun f54 () S33)
(declare-fun f55 (S34 S22) S18)
(declare-fun f56 () S34)
(declare-fun f57 (S35 S22) S15)
(declare-fun f58 (S36 S6) S35)
(declare-fun f59 () S36)
(declare-fun f60 (S37 S18) S15)
(declare-fun f61 () S37)
(declare-fun f62 () S37)
(declare-fun f63 (S39 S38) S18)
(declare-fun f64 () S39)
(declare-fun f65 (S40 S35) S6)
(declare-fun f66 (S41 S6) S40)
(declare-fun f67 () S41)
(declare-fun f68 () S35)
(declare-fun f69 () S22)
(declare-fun f70 () S22)
(declare-fun f71 (S42 S27) S43)
(declare-fun f72 () S42)
(declare-fun f73 () S43)
(declare-fun f74 (S44 S43) S2)
(declare-fun f75 () S44)
(declare-fun f76 (S45 S2) S43)
(declare-fun f77 () S45)
(declare-fun f78 () S1)
(declare-fun f79 (S43) S1)
(declare-fun f80 (S43) S3)
(declare-fun f81 () S3)
(declare-fun f82 () S1)
(declare-fun f83 (S2) S4)
(declare-fun f84 (S46 S3) S2)
(declare-fun f85 () S46)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f7 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f8 ?v0) f1) false)))
(assert (not (= (f9 (f10 (f11 f12) f13) f14) f1)))
(assert (= f15 f1))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S6)) (=> (= (f9 (f10 (f11 f12) f13) ?v1) f1) (= ?v0 ?v1))) (= ?v0 f14))))
(assert (exists ((?v0 S6)) (= (f9 (f10 (f11 f12) (f16 (f17 f18 f13) f14)) ?v0) f1)))
(assert (= (= f15 f1) (exists ((?v0 S6) (?v1 S6)) (not (= ?v0 ?v1)))))
(assert (=> (= f15 f1) (forall ((?v0 S6)) (=> (forall ((?v1 S6)) (= ?v1 ?v0)) false))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f10 (f11 ?v0) ?v1))) (=> (= (f9 ?v_0 ?v2) f1) (=> (= (f9 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S6)) (= (f9 (f10 (f11 f19) ?v0) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f9 (f10 (f11 f19) ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6) (?v3 S2) (?v4 S6)) (=> (= (f9 (f10 (f11 ?v0) ?v1) ?v2) f1) (=> (= (f9 (f10 (f11 ?v3) ?v2) ?v4) f1) (= (f9 (f10 (f11 (f20 (f21 f22 ?v0) ?v3)) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (not (= (f9 ?v0 ?v1) f1)) (=> (= (f9 (f10 (f11 ?v2) ?v1) ?v3) f1) (= (f9 (f10 (f11 (f20 (f21 (f23 f24 ?v0) ?v4) ?v2)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (= (f9 ?v0 ?v1) f1) (=> (= (f9 (f10 (f11 ?v2) ?v1) ?v3) f1) (= (f9 (f10 (f11 (f20 (f21 (f23 f24 ?v0) ?v2) ?v4)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S6) (?v4 S6)) (let ((?v_0 (= (f9 ?v0 ?v3) f1))) (=> (= (f9 (f10 (f11 (f20 (f21 (f23 f24 ?v0) ?v1) ?v2)) ?v3) ?v4) f1) (=> (=> ?v_0 (=> (= (f9 (f10 (f11 ?v1) ?v3) ?v4) f1) false)) (=> (=> (not ?v_0) (=> (= (f9 (f10 (f11 ?v2) ?v3) ?v4) f1) false)) false))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2)) (=> (not (= (f9 ?v0 ?v1) f1)) (= (f9 (f10 (f11 (f20 (f25 f26 ?v0) ?v2)) ?v1) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S6) (?v4 S6)) (let ((?v_0 (f11 (f20 (f25 f26 ?v0) ?v2)))) (=> (= (f9 ?v0 ?v1) f1) (=> (= (f9 (f10 (f11 ?v2) ?v1) ?v3) f1) (=> (= (f9 (f10 ?v_0 ?v3) ?v4) f1) (= (f9 (f10 ?v_0 ?v1) ?v4) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6) (?v3 S6)) (=> (= (f9 (f10 (f11 (f20 (f21 f22 ?v0) ?v1)) ?v2) ?v3) f1) (=> (forall ((?v4 S6)) (=> (= (f9 (f10 (f11 ?v0) ?v2) ?v4) f1) (=> (= (f9 (f10 (f11 ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S6) (?v3 S6)) (=> (= (f9 (f10 (f11 (f20 (f25 f26 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 ?v2) (=> (not (= (f9 ?v0 ?v2) f1)) false)) (=> (forall ((?v4 S6)) (=> (= (f9 ?v0 ?v2) f1) (=> (= (f9 (f10 (f11 ?v1) ?v2) ?v4) f1) (=> (= (f9 (f10 (f11 (f20 (f25 f26 ?v0) ?v1)) ?v4) ?v3) f1) false)))) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= f19 (f20 (f21 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= (f20 (f21 f22 ?v0) ?v1) f19))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (not (= f19 (f20 (f21 (f23 f24 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (not (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) f19))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5) (?v3 S2) (?v4 S2)) (not (= (f20 (f21 f22 ?v0) ?v1) (f20 (f21 (f23 f24 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (not (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) (f20 (f21 f22 ?v3) ?v4)))))
(assert (forall ((?v0 S5) (?v1 S2)) (not (= f19 (f20 (f25 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S2)) (not (= (f20 (f25 f26 ?v0) ?v1) f19))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5) (?v3 S2)) (not (= (f20 (f21 f22 ?v0) ?v1) (f20 (f25 f26 ?v2) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S2)) (not (= (f20 (f25 f26 ?v0) ?v1) (f20 (f21 f22 ?v2) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5) (?v3 S2)) (= (= (f20 (f25 f26 ?v0) ?v1) (f20 (f25 f26 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S5) (?v4 S2) (?v5 S2)) (= (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) (f20 (f21 (f23 f24 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f20 (f21 f22 ?v0) ?v1) (f20 (f21 f22 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S5) (?v4 S2)) (not (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) (f20 (f25 f26 ?v3) ?v4)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5) (?v3 S2) (?v4 S2)) (not (= (f20 (f25 f26 ?v0) ?v1) (f20 (f21 (f23 f24 ?v2) ?v3) ?v4)))))
(assert (= (f27 f28 f19) (f29 f30 0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f27 f28 (f20 (f21 f22 ?v0) ?v1)) (f29 f30 (+ (+ (f31 f32 (f27 f28 ?v0)) (f31 f32 (f27 f28 ?v1))) (+ 0 1))))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (= (f27 f28 (f20 (f21 (f23 f24 ?v0) ?v1) ?v2)) (f29 f30 (+ (+ (f31 f32 (f27 f28 ?v1)) (f31 f32 (f27 f28 ?v2))) (+ 0 1))))))
(assert (= (f27 f33 f19) (f29 f30 0)))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f27 f28 (f20 (f25 f26 ?v0) ?v1)) (f29 f30 (+ (f31 f32 (f27 f28 ?v1)) (+ 0 1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f27 f33 (f20 (f21 f22 ?v0) ?v1)) (f29 f30 (+ (+ (f31 f32 (f27 f33 ?v0)) (f31 f32 (f27 f33 ?v1))) (+ 0 1))))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f27 f33 (f20 (f25 f26 ?v0) ?v1)) (f29 f30 (+ (f31 f32 (f27 f33 ?v1)) (+ 0 1))))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (= (f27 f33 (f20 (f21 (f23 f24 ?v0) ?v1) ?v2)) (f29 f30 (+ (+ (f31 f32 (f27 f33 ?v1)) (f31 f32 (f27 f33 ?v2))) (+ 0 1))))))
(assert (=> (= (f34 f19) f1) (=> false false)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f34 (f20 (f21 f22 ?v0) ?v1)) f1) (=> (=> (= (f34 ?v0) f1) (=> (= (f34 ?v1) f1) false)) false))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (=> (= (f34 (f20 (f21 (f23 f24 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 ?v1) f1) (=> (= (f34 ?v2) f1) false)) false))))
(assert (forall ((?v0 S5) (?v1 S2)) (=> (= (f34 (f20 (f25 f26 ?v0) ?v1)) f1) (=> (=> (= (f34 ?v1) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S5)) (=> (= (f34 ?v0) f1) (= (f34 (f20 (f25 f26 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (=> (= (f34 ?v0) f1) (=> (= (f34 ?v1) f1) (= (f34 (f20 (f21 (f23 f24 ?v2) ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f34 ?v0) f1) (=> (= (f34 ?v1) f1) (= (f34 (f20 (f21 f22 ?v0) ?v1)) f1)))))
(assert (= (f34 f19) f1))
(assert (forall ((?v0 S18) (?v1 S19)) (=> (= (f34 (f35 (f36 f37 ?v0) ?v1)) f1) (=> false false))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2)) (=> (= (f34 (f20 (f38 (f39 f40 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 ?v2) f1) false) false))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6)) (=> (= (f9 (f41 (f42 (f43 f19) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S6) (?v1 S15)) (= (f9 (f41 (f42 (f43 f19) ?v0) ?v1) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S15) (?v3 S6) (?v4 S2) (?v5 S6)) (=> (= (f9 (f41 (f42 (f43 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f9 (f41 (f42 (f43 ?v4) ?v3) ?v2) ?v5) f1) (= (f9 (f41 (f42 (f43 (f20 (f21 f22 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S15)) (=> (not (= (f9 ?v0 ?v1) f1)) (= (f9 (f41 (f42 (f43 (f20 (f25 f26 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S15) (?v4 S6) (?v5 S6)) (let ((?v_0 (f43 (f20 (f25 f26 ?v0) ?v2)))) (=> (= (f9 ?v0 ?v1) f1) (=> (= (f9 (f41 (f42 (f43 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f9 (f41 (f42 ?v_0 ?v4) ?v3) ?v5) f1) (= (f9 (f41 (f42 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S15) (?v4 S6) (?v5 S2)) (=> (not (= (f9 ?v0 ?v1) f1)) (=> (= (f9 (f41 (f42 (f43 ?v2) ?v1) ?v3) ?v4) f1) (= (f9 (f41 (f42 (f43 (f20 (f21 (f23 f24 ?v0) ?v5) ?v2)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S15) (?v4 S6) (?v5 S2)) (=> (= (f9 ?v0 ?v1) f1) (=> (= (f9 (f41 (f42 (f43 ?v2) ?v1) ?v3) ?v4) f1) (= (f9 (f41 (f42 (f43 (f20 (f21 (f23 f24 ?v0) ?v2) ?v5)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S6) (?v4 S15) (?v5 S6)) (let ((?v_0 (= (f9 ?v0 ?v3) f1))) (=> (= (f9 (f41 (f42 (f43 (f20 (f21 (f23 f24 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (=> ?v_0 (=> (= (f9 (f41 (f42 (f43 ?v1) ?v3) ?v4) ?v5) f1) false)) (=> (=> (not ?v_0) (=> (= (f9 (f41 (f42 (f43 ?v2) ?v3) ?v4) ?v5) f1) false)) false))))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S22) (?v4 S19) (?v5 S2)) (= (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) (f20 (f38 (f39 f40 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S18) (?v4 S27) (?v5 S19)) (= (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) (f35 (f44 (f45 f46 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S18) (?v3 S19)) (= (= (f35 (f36 f37 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S18) (?v4 S27) (?v5 S19)) (not (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) (f35 (f44 (f45 f46 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S22) (?v4 S19) (?v5 S2)) (not (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) (f20 (f38 (f39 f40 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S18) (?v4 S19)) (not (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) (f35 (f36 f37 ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S18) (?v4 S19)) (not (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) (f35 (f36 f37 ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S22) (?v3 S19) (?v4 S2)) (not (= (f35 (f36 f37 ?v0) ?v1) (f20 (f38 (f39 f40 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S18) (?v3 S27) (?v4 S19)) (not (= (f35 (f36 f37 ?v0) ?v1) (f35 (f44 (f45 f46 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S15) (?v3 S6) (?v4 S15)) (let ((?v_0 (f42 (f43 ?v0) ?v1))) (=> (= (f9 (f41 ?v_0 ?v2) ?v3) f1) (=> (<= (f31 f32 ?v2) (f31 f32 ?v4)) (= (f9 (f41 ?v_0 ?v4) ?v3) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f6 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f47 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S15) (?v3 S6)) (let ((?v_0 (f42 (f43 ?v0) ?v1))) (=> (= (f9 (f41 ?v_0 ?v2) ?v3) f1) (= (f9 (f41 ?v_0 (f29 f30 (+ (f31 f32 ?v2) 1))) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S15) (?v3 S6)) (=> (= (f9 (f41 (f42 (f43 ?v0) ?v1) ?v2) ?v3) f1) (= (f9 (f10 (f11 ?v0) ?v1) ?v3) f1))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (= (= (f9 (f10 (f11 ?v0) ?v1) ?v2) f1) (exists ((?v3 S15)) (= (f9 (f41 (f42 (f43 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S22) (?v2 S19)) (=> (= (f34 ?v0) f1) (= (f34 (f20 (f38 (f39 f40 ?v1) ?v2) ?v0)) f1))))
(assert (forall ((?v0 S18) (?v1 S19)) (= (f34 (f35 (f36 f37 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S5) (?v3 S2)) (not (= (f35 (f36 f37 ?v0) ?v1) (f20 (f25 f26 ?v2) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S18) (?v3 S19)) (not (= (f20 (f25 f26 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S18) (?v3 S27) (?v4 S19)) (not (= (f20 (f25 f26 ?v0) ?v1) (f35 (f44 (f45 f46 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S22) (?v3 S19) (?v4 S2)) (not (= (f20 (f25 f26 ?v0) ?v1) (f20 (f38 (f39 f40 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S5) (?v4 S2)) (not (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) (f20 (f25 f26 ?v3) ?v4)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S5) (?v4 S2)) (not (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) (f20 (f25 f26 ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S5) (?v3 S2) (?v4 S2)) (not (= (f35 (f36 f37 ?v0) ?v1) (f20 (f21 (f23 f24 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S18) (?v4 S19)) (not (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) (f35 (f36 f37 ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S5) (?v4 S2) (?v5 S2)) (not (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) (f20 (f21 (f23 f24 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S18) (?v4 S27) (?v5 S19)) (not (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) (f35 (f44 (f45 f46 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S22) (?v4 S19) (?v5 S2)) (not (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) (f20 (f38 (f39 f40 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S5) (?v4 S2) (?v5 S2)) (not (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) (f20 (f21 (f23 f24 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S2) (?v3 S2)) (not (= (f35 (f36 f37 ?v0) ?v1) (f20 (f21 f22 ?v2) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S18) (?v3 S19)) (not (= (f20 (f21 f22 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S18) (?v3 S27) (?v4 S19)) (not (= (f20 (f21 f22 ?v0) ?v1) (f35 (f44 (f45 f46 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S22) (?v3 S19) (?v4 S2)) (not (= (f20 (f21 f22 ?v0) ?v1) (f20 (f38 (f39 f40 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S2) (?v4 S2)) (not (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) (f20 (f21 f22 ?v3) ?v4)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S2) (?v4 S2)) (not (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) (f20 (f21 f22 ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S19)) (not (= f19 (f35 (f36 f37 ?v0) ?v1)))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19)) (not (= f19 (f35 (f44 (f45 f46 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2)) (not (= f19 (f20 (f38 (f39 f40 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S19)) (not (= (f35 (f36 f37 ?v0) ?v1) f19))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19)) (not (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) f19))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2)) (not (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) f19))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2)) (= (f27 f33 (f20 (f38 (f39 f40 ?v0) ?v1) ?v2)) (f29 f30 (+ (f31 f32 (f27 f33 ?v2)) (+ 0 1))))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2)) (= (f27 f28 (f20 (f38 (f39 f40 ?v0) ?v1) ?v2)) (f29 f30 (+ (f31 f32 (f27 f28 ?v2)) (+ 0 1))))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19)) (= (f27 f33 (f35 (f44 (f45 f46 ?v0) ?v1) ?v2)) (f29 f30 0))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19)) (= (f27 f28 (f35 (f44 (f45 f46 ?v0) ?v1) ?v2)) (f29 f30 0))))
(assert (forall ((?v0 S18) (?v1 S19)) (= (f27 f33 (f35 (f36 f37 ?v0) ?v1)) (f29 f30 0))))
(assert (forall ((?v0 S18) (?v1 S19)) (= (f27 f28 (f35 (f36 f37 ?v0) ?v1)) (f29 f30 0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6) (?v3 S15) (?v4 S6)) (=> (= (f9 (f41 (f42 (f43 (f20 (f21 f22 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (forall ((?v5 S6)) (=> (= (f9 (f41 (f42 (f43 ?v0) ?v2) ?v3) ?v5) f1) (=> (= (f9 (f41 (f42 (f43 ?v1) ?v5) ?v3) ?v4) f1) false))) false))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S6) (?v3 S15) (?v4 S6)) (=> (= (f9 (f41 (f42 (f43 (f20 (f25 f26 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 ?v2) (=> (not (= (f9 ?v0 ?v2) f1)) false)) (=> (forall ((?v5 S6)) (=> (= (f9 ?v0 ?v2) f1) (=> (= (f9 (f41 (f42 (f43 ?v1) ?v2) ?v3) ?v5) f1) (=> (= (f9 (f41 (f42 (f43 (f20 (f25 f26 ?v0) ?v1)) ?v5) ?v3) ?v4) f1) false)))) false)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (=> (= (f9 (f10 (f11 ?v0) ?v1) ?v2) f1) (exists ((?v3 S15)) (= (f9 (f41 (f42 (f43 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S15) (?v3 S6) (?v4 S2) (?v5 S6) (?v6 S15) (?v7 S6)) (=> (= (f9 (f41 (f42 (f43 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f9 (f41 (f42 (f43 ?v4) ?v5) ?v6) ?v7) f1) (exists ((?v8 S15)) (and (= (f9 (f41 (f42 (f43 ?v0) ?v1) ?v8) ?v3) f1) (= (f9 (f41 (f42 (f43 ?v4) ?v5) ?v8) ?v7) f1)))))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S6) (?v3 S6)) (=> (= (f9 (f10 (f11 (f35 (f36 f37 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S6)) (= (f9 (f10 (f11 (f35 (f36 f37 ?v0) ?v1)) ?v2) (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S6) (?v3 S15) (?v4 S6)) (=> (= (f9 (f41 (f42 (f43 (f35 (f36 f37 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S6) (?v3 S15)) (= (f9 (f41 (f42 (f43 (f35 (f36 f37 ?v0) ?v1)) ?v2) ?v3) (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19)) (=> (= (f34 (f35 (f44 (f45 f46 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 (f53 f54 ?v1)) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S22) (?v3 S19) (?v4 S6)) (let ((?v_0 (f55 f56 ?v2))) (=> (= (f9 (f10 (f11 ?v0) (f48 (f49 (f50 f51 ?v1) ?v_0) (f52 ?v3 ?v1))) ?v4) f1) (= (f9 (f10 (f11 (f20 (f38 (f39 f40 ?v2) ?v3) ?v0)) ?v1) (f48 (f49 (f50 f51 ?v4) ?v_0) (f57 (f58 f59 ?v1) ?v2))) f1)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S22) (?v3 S19) (?v4 S15) (?v5 S6)) (let ((?v_0 (f55 f56 ?v2))) (=> (= (f9 (f41 (f42 (f43 ?v0) (f48 (f49 (f50 f51 ?v1) ?v_0) (f52 ?v3 ?v1))) ?v4) ?v5) f1) (= (f9 (f41 (f42 (f43 (f20 (f38 (f39 f40 ?v2) ?v3) ?v0)) ?v1) ?v4) (f48 (f49 (f50 f51 ?v5) ?v_0) (f57 (f58 f59 ?v1) ?v2))) f1)))))
(assert (forall ((?v0 S2)) (=> (=> (= ?v0 f19) false) (=> (forall ((?v1 S18) (?v2 S19)) (=> (= ?v0 (f35 (f36 f37 ?v1) ?v2)) false)) (=> (forall ((?v1 S22) (?v2 S19) (?v3 S2)) (=> (= ?v0 (f20 (f38 (f39 f40 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S2) (?v2 S2)) (=> (= ?v0 (f20 (f21 f22 ?v1) ?v2)) false)) (=> (forall ((?v1 S5) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f20 (f21 (f23 f24 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S5) (?v2 S2)) (=> (= ?v0 (f20 (f25 f26 ?v1) ?v2)) false)) (=> (forall ((?v1 S27)) (=> (= ?v0 (f53 f54 ?v1)) false)) (=> (forall ((?v1 S18) (?v2 S27) (?v3 S19)) (=> (= ?v0 (f35 (f44 (f45 f46 ?v1) ?v2) ?v3)) false)) false))))))))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= (f55 f56 ?v0) (f55 f56 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S27) (?v1 S27)) (= (= (f53 f54 ?v0) (f53 f54 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S27) (?v1 S5) (?v2 S2)) (not (= (f53 f54 ?v0) (f20 (f25 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S27)) (not (= (f20 (f25 f26 ?v0) ?v1) (f53 f54 ?v2)))))
(assert (forall ((?v0 S27) (?v1 S5) (?v2 S2) (?v3 S2)) (not (= (f53 f54 ?v0) (f20 (f21 (f23 f24 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2) (?v3 S27)) (not (= (f20 (f21 (f23 f24 ?v0) ?v1) ?v2) (f53 f54 ?v3)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S27)) (not (= (f20 (f38 (f39 f40 ?v0) ?v1) ?v2) (f53 f54 ?v3)))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S27)) (not (= (f35 (f44 (f45 f46 ?v0) ?v1) ?v2) (f53 f54 ?v3)))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S27)) (not (= (f35 (f36 f37 ?v0) ?v1) (f53 f54 ?v2)))))
(assert (forall ((?v0 S27) (?v1 S22) (?v2 S19) (?v3 S2)) (not (= (f53 f54 ?v0) (f20 (f38 (f39 f40 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S27) (?v1 S18) (?v2 S27) (?v3 S19)) (not (= (f53 f54 ?v0) (f35 (f44 (f45 f46 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S27) (?v1 S18) (?v2 S19)) (not (= (f53 f54 ?v0) (f35 (f36 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S27) (?v1 S2) (?v2 S2)) (not (= (f53 f54 ?v0) (f20 (f21 f22 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S27)) (not (= (f20 (f21 f22 ?v0) ?v1) (f53 f54 ?v2)))))
(assert (forall ((?v0 S27)) (not (= f19 (f53 f54 ?v0)))))
(assert (forall ((?v0 S27)) (not (= (f53 f54 ?v0) f19))))
(assert (forall ((?v0 S27)) (= (f27 f33 (f53 f54 ?v0)) (f29 f30 0))))
(assert (forall ((?v0 S27)) (= (f27 f28 (f53 f54 ?v0)) (f29 f30 0))))
(assert (forall ((?v0 S27) (?v1 S18) (?v2 S19)) (=> (= (f34 (f53 f54 ?v0)) f1) (= (f34 (f35 (f44 (f45 f46 ?v1) ?v0) ?v2)) f1))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S6) (?v4 S6)) (=> (= (f9 (f10 (f11 (f20 (f38 (f39 f40 ?v0) ?v1) ?v2)) ?v3) ?v4) f1) (=> (forall ((?v5 S6)) (let ((?v_0 (f55 f56 ?v0))) (=> (= ?v4 (f48 (f49 (f50 f51 ?v5) ?v_0) (f57 (f58 f59 ?v3) ?v0))) (=> (= (f9 (f10 (f11 ?v2) (f48 (f49 (f50 f51 ?v3) ?v_0) (f52 ?v1 ?v3))) ?v5) f1) false)))) false))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S2) (?v3 S6) (?v4 S15) (?v5 S6)) (=> (= (f9 (f41 (f42 (f43 (f20 (f38 (f39 f40 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (forall ((?v6 S6)) (let ((?v_0 (f55 f56 ?v0))) (=> (= ?v5 (f48 (f49 (f50 f51 ?v6) ?v_0) (f57 (f58 f59 ?v3) ?v0))) (=> (= (f9 (f41 (f42 (f43 ?v2) (f48 (f49 (f50 f51 ?v3) ?v_0) (f52 ?v1 ?v3))) ?v4) ?v6) f1) false)))) false))))
(assert (forall ((?v0 S22)) (= (f60 f61 (f55 f56 ?v0)) (f29 f30 0))))
(assert (forall ((?v0 S22)) (= (f60 f62 (f55 f56 ?v0)) (f29 f30 0))))
(assert (forall ((?v0 S38)) (= (f60 f61 (f63 f64 ?v0)) (f29 f30 0))))
(assert (forall ((?v0 S38) (?v1 S38)) (= (= (f63 f64 ?v0) (f63 f64 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S38)) (= (f60 f62 (f63 f64 ?v0)) (f29 f30 0))))
(assert (forall ((?v0 S22) (?v1 S38)) (not (= (f55 f56 ?v0) (f63 f64 ?v1)))))
(assert (forall ((?v0 S38) (?v1 S22)) (not (= (f63 f64 ?v0) (f55 f56 ?v1)))))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S38)) (=> (= ?v0 (f63 f64 ?v1)) false)) (=> (forall ((?v1 S22)) (=> (= ?v0 (f55 f56 ?v1)) false)) false))))
(assert (forall ((?v0 S27) (?v1 S6) (?v2 S19) (?v3 S6) (?v4 S18)) (=> (= (f9 (f10 (f11 (f53 f54 ?v0)) (f48 (f49 (f50 f51 (f65 (f66 f67 ?v1) f68)) (f55 f56 f69)) (f52 ?v2 ?v1))) ?v3) f1) (= (f9 (f10 (f11 (f35 (f44 (f45 f46 ?v4) ?v0) ?v2)) ?v1) (f48 (f49 (f50 f51 (f65 (f66 f67 ?v3) (f58 f59 ?v1))) ?v4) (f57 (f58 f59 ?v3) f70))) f1))))
(assert (forall ((?v0 S27) (?v1 S6) (?v2 S19) (?v3 S15) (?v4 S6) (?v5 S18)) (=> (= (f9 (f41 (f42 (f43 (f53 f54 ?v0)) (f48 (f49 (f50 f51 (f65 (f66 f67 ?v1) f68)) (f55 f56 f69)) (f52 ?v2 ?v1))) ?v3) ?v4) f1) (= (f9 (f41 (f42 (f43 (f35 (f44 (f45 f46 ?v5) ?v0) ?v2)) ?v1) ?v3) (f48 (f49 (f50 f51 (f65 (f66 f67 ?v4) (f58 f59 ?v1))) ?v5) (f57 (f58 f59 ?v4) f70))) f1))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S6) (?v4 S6)) (=> (= (f9 (f10 (f11 (f35 (f44 (f45 f46 ?v0) ?v1) ?v2)) ?v3) ?v4) f1) (=> (forall ((?v5 S6)) (=> (= ?v4 (f48 (f49 (f50 f51 (f65 (f66 f67 ?v5) (f58 f59 ?v3))) ?v0) (f57 (f58 f59 ?v5) f70))) (=> (= (f9 (f10 (f11 (f53 f54 ?v1)) (f48 (f49 (f50 f51 (f65 (f66 f67 ?v3) f68)) (f55 f56 f69)) (f52 ?v2 ?v3))) ?v5) f1) false))) false))))
(assert (forall ((?v0 S18) (?v1 S27) (?v2 S19) (?v3 S6) (?v4 S15) (?v5 S6)) (=> (= (f9 (f41 (f42 (f43 (f35 (f44 (f45 f46 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (forall ((?v6 S6)) (=> (= ?v5 (f48 (f49 (f50 f51 (f65 (f66 f67 ?v6) (f58 f59 ?v3))) ?v0) (f57 (f58 f59 ?v6) f70))) (=> (= (f9 (f41 (f42 (f43 (f53 f54 ?v1)) (f48 (f49 (f50 f51 (f65 (f66 f67 ?v3) f68)) (f55 f56 f69)) (f52 ?v2 ?v3))) ?v4) ?v6) f1) false))) false))))
(assert (forall ((?v0 S2)) (= (= (f34 ?v0) f1) (or (= ?v0 f19) (or (exists ((?v1 S18) (?v2 S19)) (= ?v0 (f35 (f36 f37 ?v1) ?v2))) (or (exists ((?v1 S2) (?v2 S22) (?v3 S19)) (and (= ?v0 (f20 (f38 (f39 f40 ?v2) ?v3) ?v1)) (= (f34 ?v1) f1))) (or (exists ((?v1 S2) (?v2 S2)) (and (= ?v0 (f20 (f21 f22 ?v1) ?v2)) (and (= (f34 ?v1) f1) (= (f34 ?v2) f1)))) (or (exists ((?v1 S2) (?v2 S2) (?v3 S5)) (and (= ?v0 (f20 (f21 (f23 f24 ?v3) ?v1) ?v2)) (and (= (f34 ?v1) f1) (= (f34 ?v2) f1)))) (or (exists ((?v1 S2) (?v2 S5)) (and (= ?v0 (f20 (f25 f26 ?v2) ?v1)) (= (f34 ?v1) f1))) (or (exists ((?v1 S27)) (and (= ?v0 (f53 f54 ?v1)) (not (= (f71 f72 ?v1) f73)))) (exists ((?v1 S27) (?v2 S18) (?v3 S19)) (and (= ?v0 (f35 (f44 (f45 f46 ?v2) ?v1) ?v3)) (= (f34 (f53 f54 ?v1)) f1)))))))))))))
(assert (forall ((?v0 S27)) (=> (not (= (f71 f72 ?v0) f73)) (= (f34 (f53 f54 ?v0)) f1))))
(assert (forall ((?v0 S27) (?v1 S6) (?v2 S6)) (=> (= (f9 (f10 (f11 (f53 f54 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f9 (f10 (f11 (f74 f75 (f71 f72 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S27) (?v1 S6) (?v2 S6)) (=> (= (f9 (f10 (f11 (f74 f75 (f71 f72 ?v0))) ?v1) ?v2) f1) (= (f9 (f10 (f11 (f53 f54 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S27) (?v1 S6) (?v2 S15) (?v3 S6)) (=> (= (f9 (f41 (f42 (f43 (f74 f75 (f71 f72 ?v0))) ?v1) ?v2) ?v3) f1) (= (f9 (f41 (f42 (f43 (f53 f54 ?v0)) ?v1) (f29 f30 (+ (f31 f32 ?v2) 1))) ?v3) f1))))
(assert (forall ((?v0 S27) (?v1 S6) (?v2 S15) (?v3 S6)) (=> (= (f9 (f41 (f42 (f43 (f53 f54 ?v0)) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S15)) (=> (= ?v2 (f29 f30 (+ (f31 f32 ?v4) 1))) (=> (= (f9 (f41 (f42 (f43 (f74 f75 (f71 f72 ?v0))) ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S27)) (=> (= (f34 (f53 f54 ?v0)) f1) (=> (forall ((?v1 S2)) (=> (= (f71 f72 ?v0) (f76 f77 ?v1)) false)) false))))
(assert (forall ((?v0 S27) (?v1 S2)) (=> (= f78 f1) (=> (= (f71 f72 ?v0) (f76 f77 ?v1)) (= (f34 ?v1) f1)))))
(assert (forall ((?v0 S2)) (= (f74 f75 (f76 f77 ?v0)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f76 f77 ?v0) (f76 f77 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (not (= f73 (f76 f77 ?v0)))))
(assert (forall ((?v0 S2)) (not (= (f76 f77 ?v0) f73))))
(assert (forall ((?v0 S43)) (= (forall ((?v1 S2)) (not (= ?v0 (f76 f77 ?v1)))) (= ?v0 f73))))
(assert (forall ((?v0 S43)) (= (not (= ?v0 f73)) (exists ((?v1 S2)) (= ?v0 (f76 f77 ?v1))))))
(assert (forall ((?v0 S43)) (=> (=> (= ?v0 f73) false) (=> (forall ((?v1 S2)) (=> (= ?v0 (f76 f77 ?v1)) false)) false))))
(assert (forall ((?v0 S2)) (= (= (f79 (f76 f77 ?v0)) f1) false)))
(assert (forall ((?v0 S43)) (= (= (f79 ?v0) f1) (= ?v0 f73))))
(assert (= (= (f79 f73) f1) true))
(assert (forall ((?v0 S2) (?v1 S43)) (= (= (f6 ?v0 (f80 ?v1)) f1) (= ?v1 (f76 f77 ?v0)))))
(assert (forall ((?v0 S43) (?v1 S3) (?v2 S2)) (=> (forall ((?v3 S2)) (=> (= (f6 ?v3 (f80 ?v0)) f1) (= (f3 ?v1 ?v3) f1))) (=> (= ?v0 (f76 f77 ?v2)) (= (f3 ?v1 ?v2) f1)))))
(assert (= (f80 f73) f81))
(assert (forall ((?v0 S43)) (= (= (f80 ?v0) f81) (= ?v0 f73))))
(assert (forall ((?v0 S2)) (=> (= (f6 ?v0 f81) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f3 f81 ?v0) f1) (= f82 f1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f81) (not (= (f6 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f47 ?v0) f81) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f6 ?v0 f81) f1) false)))
(assert (forall ((?v0 S3)) (= (= f81 (f47 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 ?v1 f81) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 ?v1 f81) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 ?v1 ?v0) f1)) (not (= ?v0 f81)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 ?v1 ?v0) f1))) (= ?v0 f81))))
(assert (= f81 (f47 f8)))
(assert (forall ((?v0 S2)) (= (= (f3 f81 ?v0) f1) (= f82 f1))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 ?v1 ?v0) f1) false)) (= ?v0 f81))))
(assert (forall ((?v0 S2)) (= (f80 (f76 f77 ?v0)) (f4 (f83 ?v0) f81))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f6 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v0 (f4 (f83 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f6 ?v0 (f4 (f83 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f81 (f4 (f83 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f83 ?v0) ?v1) f81))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 ?v0 (f4 (f83 ?v1) f81)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f83 ?v0) (f4 (f83 ?v1) f81)) (f4 (f83 ?v2) (f4 (f83 ?v3) f81))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 ?v0 (f4 (f83 ?v1) f81)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f83 ?v0) f81) (f4 (f83 ?v1) f81)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (= (f4 (f83 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f6 ?v0 ?v1) f1) (= (f6 ?v0 (f4 (f83 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f83 ?v0))) (=> (not (= (f6 ?v0 ?v1) f1)) (=> (not (= (f6 ?v0 ?v2) f1)) (= (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f83 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f6 ?v0 (f4 (f83 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f83 ?v0)) (?v_0 (f83 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f83 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f83 ?v0) (f47 ?v1)) (f47 (f4 (f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f83 ?v0) ?v1) (f47 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 ?v0 (f4 (f83 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2)) (= (f84 f85 (f4 (f83 ?v0) f81)) ?v0)))
(assert (forall ((?v0 S15)) (= (f29 f30 (f31 f32 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f31 f32 (f29 f30 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f31 f32 (f29 f30 ?v0)) 0))))
(check-sat)
(exit)
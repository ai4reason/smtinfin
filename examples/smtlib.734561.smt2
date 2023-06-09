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
(declare-sort S47 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S1) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S4 S3) S1)
(declare-fun f6 (S5 S4) S4)
(declare-fun f7 (S6 S3) S5)
(declare-fun f8 () S6)
(declare-fun f9 (S7 S4) S1)
(declare-fun f10 (S8 S3) S7)
(declare-fun f11 () S8)
(declare-fun f12 () S6)
(declare-fun f13 () S4)
(declare-fun f14 () S4)
(declare-fun f15 (S10 S9) S4)
(declare-fun f16 () S10)
(declare-fun f17 () S6)
(declare-fun f18 (S11 S12) S3)
(declare-fun f19 (S13 S14) S11)
(declare-fun f20 (S15 S12) S13)
(declare-fun f21 () S15)
(declare-fun f22 () S12)
(declare-fun f23 (S16 S14) S14)
(declare-fun f24 (S17 S18) S16)
(declare-fun f25 () S17)
(declare-fun f26 () S18)
(declare-fun f27 () S14)
(declare-fun f28 (S19 S18) S12)
(declare-fun f29 (S20 S12) S19)
(declare-fun f30 () S20)
(declare-fun f31 (S21 S18) S18)
(declare-fun f32 (S22 S2) S21)
(declare-fun f33 () S22)
(declare-fun f34 () S4)
(declare-fun f35 (S23 Int) S9)
(declare-fun f36 () S23)
(declare-fun f37 (S24 S9) Int)
(declare-fun f38 () S24)
(declare-fun f39 (S25 S4) S7)
(declare-fun f40 () S25)
(declare-fun f41 () S25)
(declare-fun f42 (S27 S3) S9)
(declare-fun f43 (S28 S26) S27)
(declare-fun f44 () S28)
(declare-fun f45 () S5)
(declare-fun f46 (S18 S30) S1)
(declare-fun f47 (S12 S29) S18)
(declare-fun f48 (S31 S14) S16)
(declare-fun f49 (S32 S18) S31)
(declare-fun f50 () S32)
(declare-fun f51 (S33 S4) S3)
(declare-fun f52 () S33)
(declare-fun f53 () S1)
(declare-fun f54 () S14)
(declare-fun f55 () S31)
(declare-fun f56 () S27)
(declare-fun f57 (S35 S34) S14)
(declare-fun f58 () S35)
(declare-fun f59 (S36 S37) S14)
(declare-fun f60 () S36)
(declare-fun f61 (S34) S37)
(declare-fun f62 (S39 S38) S5)
(declare-fun f63 () S39)
(declare-fun f64 (S40 S33) S1)
(declare-fun f65 (S41 S38) S40)
(declare-fun f66 () S41)
(declare-fun f67 (S42 S43) S1)
(declare-fun f68 () S42)
(declare-fun f69 () S43)
(declare-fun f70 (S44 S27) S1)
(declare-fun f71 () S44)
(declare-fun f72 (S45 S9) S18)
(declare-fun f73 (S46 S30) S45)
(declare-fun f74 (S47 S14) S46)
(declare-fun f75 () S47)
(declare-fun f76 (S43 S14) S9)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S1)) (= (= (f3 f4 ?v0) f1) (not (= ?v0 f1)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f9 (f10 f11 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (= (= (f5 (f6 (f7 f12 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3)) (= (= (f5 f13 ?v0) f1) false)))
(assert (not (forall ((?v0 S9)) (=> (forall ((?v1 S3)) (=> (= (f9 (f10 f11 ?v1) f14) f1) (= (f5 (f15 f16 ?v0) ?v1) f1))) (forall ((?v1 S3)) (=> (= (f9 (f10 f11 ?v1) (f6 (f7 f17 (f18 (f19 (f20 f21 f22) (f23 (f24 f25 f26) f27)) (f28 (f29 f30 f22) (f31 (f32 f33 f4) f26)))) f34)) f1) (= (f5 (f15 f16 ?v0) ?v1) f1)))))))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S3)) (=> (= (f9 (f10 f11 ?v1) f14) f1) (= (f5 (f15 f16 ?v0) ?v1) f1))) (forall ((?v1 S3)) (=> (= (f9 (f10 f11 ?v1) (f6 (f7 f17 (f18 (f19 (f20 f21 (f28 (f29 f30 f22) f26)) f27) f22)) f34)) f1) (= (f5 (f15 f16 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S14) (?v2 S12) (?v3 S12) (?v4 S14) (?v5 S12)) (= (= (f18 (f19 (f20 f21 ?v0) ?v1) ?v2) (f18 (f19 (f20 f21 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S4) (?v1 S9)) (=> (forall ((?v2 S3)) (=> (= (f9 (f10 f11 ?v2) ?v0) f1) (= (f5 (f15 f16 (f35 f36 (+ (f37 f38 ?v1) 1))) ?v2) f1))) (forall ((?v2 S3)) (=> (= (f9 (f10 f11 ?v2) ?v0) f1) (= (f5 (f15 f16 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S3)) (=> (= (f5 (f15 f16 (f35 f36 (+ (f37 f38 ?v0) 1))) ?v1) f1) (= (f5 (f15 f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f9 (f39 f40 ?v0) ?v1) f1) (forall ((?v2 S9)) (=> (forall ((?v3 S3)) (=> (= (f9 (f10 f11 ?v3) ?v0) f1) (= (f5 (f15 f16 ?v2) ?v3) f1))) (forall ((?v3 S3)) (=> (= (f9 (f10 f11 ?v3) ?v1) f1) (= (f5 (f15 f16 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S18) (?v3 S14)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f29 f30 ?v1))) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 (f28 ?v_1 ?v2)) ?v3) ?v1)) f34)) f1) (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 ?v1) (f23 (f24 f25 ?v2) ?v3)) (f28 ?v_1 (f31 (f32 f33 f4) ?v2)))) f34)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4)) (let ((?v_0 (f10 f11 ?v0))) (=> (= (f9 ?v_0 (f6 (f7 f17 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f9 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (let ((?v_0 (f10 f11 ?v0))) (=> (=> (not (= (f9 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f9 ?v_0 (f6 (f7 f17 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3)) (=> (= (f9 (f10 f11 ?v0) f34) f1) false)))
(assert (forall ((?v0 S26) (?v1 S12) (?v2 S14) (?v3 S12)) (= (f42 (f43 f44 ?v0) (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) (f35 f36 0))))
(assert (forall ((?v0 S3) (?v1 S4)) (not (= f34 (f6 (f7 f17 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S4)) (not (= (f6 (f7 f17 ?v0) ?v1) f34))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f9 (f10 f11 ?v0) (f6 (f7 f17 ?v1) f34)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f6 (f7 f17 ?v0) (f6 (f7 f17 ?v1) f34)) (f6 (f7 f17 ?v2) (f6 (f7 f17 ?v3) f34))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f39 f41 ?v2))) (=> (= (f9 (f39 f41 ?v0) ?v1) f1) (=> (= (f9 ?v_0 ?v0) f1) (= (f9 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (f9 (f39 f41 ?v0) f34) f1)))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S4)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f7 f17 ?v1))) (=> (= (f9 ?v_0 (f6 ?v_1 ?v2)) f1) (and (= (f9 ?v_0 (f6 ?v_1 f34)) f1) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S4)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f7 f17 ?v1))) (=> (= (f9 ?v_0 (f6 ?v_1 f34)) f1) (=> (= (f9 ?v_0 ?v2) f1) (= (f9 ?v_0 (f6 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (= ?v0 f34) (not (= (f9 (f10 f11 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S4)) (= (= (f6 f45 ?v0) f34) (forall ((?v1 S3)) (not (= (f5 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f9 (f10 f11 ?v0) f34) f1) false)))
(assert (forall ((?v0 S4)) (= (= f34 (f6 f45 ?v0)) (forall ((?v1 S3)) (not (= (f5 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (forall ((?v1 S3)) (=> (= (f9 (f10 f11 ?v1) f34) f1) (= (f5 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S4)) (= (exists ((?v1 S3)) (and (= (f9 (f10 f11 ?v1) f34) f1) (= (f5 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S4)) (= (exists ((?v1 S3)) (= (f9 (f10 f11 ?v1) ?v0) f1)) (not (= ?v0 f34)))))
(assert (forall ((?v0 S4)) (= (forall ((?v1 S3)) (not (= (f9 (f10 f11 ?v1) ?v0) f1))) (= ?v0 f34))))
(assert (= f34 (f6 f45 f13)))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (= (f6 (f7 f17 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (let ((?v_0 (f10 f11 ?v0))) (=> (= (f9 ?v_0 ?v1) f1) (= (f9 ?v_0 (f6 (f7 f17 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S4)) (let ((?v_0 (f10 f11 ?v0)) (?v_1 (f7 f17 ?v0))) (=> (not (= (f9 ?v_0 ?v1) f1)) (=> (not (= (f9 ?v_0 ?v2) f1)) (= (= (f6 ?v_1 ?v1) (f6 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (= (= (f5 (f6 (f7 f17 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4)) (let ((?v_0 (f10 f11 ?v0))) (= (= (f9 ?v_0 (f6 (f7 f17 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4)) (let ((?v_1 (f7 f17 ?v0)) (?v_0 (f7 f17 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S4)) (let ((?v_0 (f7 f17 ?v0))) (let ((?v_1 (f6 ?v_0 ?v1))) (= (f6 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S4)) (= (f6 (f7 f17 ?v0) (f6 f45 ?v1)) (f6 f45 (f6 (f7 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S4)) (= (f6 (f7 f17 ?v0) ?v1) (f6 f45 (f6 (f7 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S4)) (= (f9 (f10 f11 ?v0) (f6 (f7 f17 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f6 (f7 f17 ?v0) f34) (f6 (f7 f17 ?v1) f34)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f9 (f10 f11 ?v0) (f6 (f7 f17 ?v1) f34)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S14) (?v3 S12) (?v4 S12)) (let ((?v_0 (f39 f41 ?v0))) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) f34)) f1) (=> (forall ((?v5 S29) (?v6 S30)) (=> (= (f46 (f47 ?v4 ?v5) ?v6) f1) (= (f46 (f47 ?v1 ?v5) ?v6) f1))) (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 ?v4) ?v2) ?v3)) f34)) f1))))))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S14) (?v3 S12) (?v4 S12)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f19 (f20 f21 ?v1) ?v2))) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 ?v_1 ?v3)) f34)) f1) (=> (forall ((?v5 S29) (?v6 S30)) (=> (= (f46 (f47 ?v3 ?v5) ?v6) f1) (= (f46 (f47 ?v4 ?v5) ?v6) f1))) (= (f9 ?v_0 (f6 (f7 f17 (f18 ?v_1 ?v4)) f34)) f1))))))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S18) (?v3 S14) (?v4 S12) (?v5 S14)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f29 f30 ?v1))) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 (f28 ?v_1 ?v2)) ?v3) ?v4)) f34)) f1) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 (f28 ?v_1 (f31 (f32 f33 f4) ?v2))) ?v5) ?v4)) f34)) f1) (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 ?v1) (f23 (f48 (f49 f50 ?v2) ?v3) ?v5)) ?v4)) f34)) f1))))))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S14) (?v3 S12) (?v4 S12) (?v5 S12)) (let ((?v_0 (f39 f41 ?v0))) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) f34)) f1) (=> (forall ((?v6 S29) (?v7 S30)) (=> (= (f46 (f47 ?v4 ?v6) ?v7) f1) (forall ((?v8 S30)) (=> (forall ((?v9 S29)) (=> (= (f46 (f47 ?v1 ?v9) ?v7) f1) (= (f46 (f47 ?v3 ?v9) ?v8) f1))) (= (f46 (f47 ?v5 ?v6) ?v8) f1))))) (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 ?v4) ?v2) ?v5)) f34)) f1))))))
(assert (forall ((?v0 S3)) (= (f51 f52 (f6 (f7 f17 ?v0) f34)) ?v0)))
(assert (forall ((?v0 S3)) (= (= (f5 f34 ?v0) f1) (= f53 f1))))
(assert (forall ((?v0 S3)) (= (= (f5 f34 ?v0) f1) (= f53 f1))))
(assert (forall ((?v0 S4) (?v1 S12)) (= (f9 (f39 f41 ?v0) (f6 (f7 f17 (f18 (f19 (f20 f21 ?v1) f54) ?v1)) f34)) f1)))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S14) (?v3 S12) (?v4 S14) (?v5 S12)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f20 f21 ?v1))) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 ?v_1 ?v2) ?v3)) f34)) f1) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 (f20 f21 ?v3) ?v4) ?v5)) f34)) f1) (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 ?v_1 (f23 (f48 f55 ?v2) ?v4)) ?v5)) f34)) f1))))))
(assert (forall ((?v0 S12) (?v1 S14) (?v2 S12)) (= (f42 f56 (f18 (f19 (f20 f21 ?v0) ?v1) ?v2)) (f35 f36 0))))
(assert (forall ((?v0 S14) (?v1 S14)) (not (= (f23 (f48 f55 ?v0) ?v1) f54))))
(assert (forall ((?v0 S14) (?v1 S14)) (not (= f54 (f23 (f48 f55 ?v0) ?v1)))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14)) (not (= (f23 (f48 (f49 f50 ?v0) ?v1) ?v2) f54))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14)) (not (= f54 (f23 (f48 (f49 f50 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14) (?v3 S14) (?v4 S14)) (not (= (f23 (f48 (f49 f50 ?v0) ?v1) ?v2) (f23 (f48 f55 ?v3) ?v4)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S18) (?v3 S14) (?v4 S14)) (not (= (f23 (f48 f55 ?v0) ?v1) (f23 (f48 (f49 f50 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S14)) (not (= f54 (f23 (f24 f25 ?v0) ?v1)))))
(assert (forall ((?v0 S18) (?v1 S14)) (not (= (f23 (f24 f25 ?v0) ?v1) f54))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S18) (?v3 S14)) (= (= (f23 (f24 f25 ?v0) ?v1) (f23 (f24 f25 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14) (?v3 S18) (?v4 S14) (?v5 S14)) (= (= (f23 (f48 (f49 f50 ?v0) ?v1) ?v2) (f23 (f48 (f49 f50 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (= (= (f23 (f48 f55 ?v0) ?v1) (f23 (f48 f55 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14) (?v3 S18) (?v4 S14)) (not (= (f23 (f48 (f49 f50 ?v0) ?v1) ?v2) (f23 (f24 f25 ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S18) (?v3 S14) (?v4 S14)) (not (= (f23 (f24 f25 ?v0) ?v1) (f23 (f48 (f49 f50 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14) (?v3 S14)) (not (= (f23 (f24 f25 ?v0) ?v1) (f23 (f48 f55 ?v2) ?v3)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S18) (?v3 S14)) (not (= (f23 (f48 f55 ?v0) ?v1) (f23 (f24 f25 ?v2) ?v3)))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S12) (?v2 S14) (?v3 S12)) (=> (= ?v0 (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (forall ((?v2 S4)) (=> (= ?v1 (f6 (f7 f17 ?v0) ?v2)) (=> (not (= (f9 (f10 f11 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (exists ((?v2 S4)) (and (= ?v1 (f6 (f7 f17 ?v0) ?v2)) (not (= (f9 (f10 f11 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S3)) (=> (= (f9 (f10 f11 ?v1) ?v0) f1) false)) (= ?v0 f34))))
(assert (forall ((?v0 S12) (?v1 S4) (?v2 S14) (?v3 S12)) (=> (forall ((?v4 S29) (?v5 S30)) (=> (= (f46 (f47 ?v0 ?v4) ?v5) f1) (exists ((?v6 S12) (?v7 S12)) (and (= (f9 (f39 f41 ?v1) (f6 (f7 f17 (f18 (f19 (f20 f21 ?v6) ?v2) ?v7)) f34)) f1) (forall ((?v8 S30)) (=> (forall ((?v9 S29)) (=> (= (f46 (f47 ?v6 ?v9) ?v5) f1) (= (f46 (f47 ?v7 ?v9) ?v8) f1))) (= (f46 (f47 ?v3 ?v4) ?v8) f1))))))) (= (f9 (f39 f41 ?v1) (f6 (f7 f17 (f18 (f19 (f20 f21 ?v0) ?v2) ?v3)) f34)) f1))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S30)) (= (= (f46 (f31 (f32 f33 ?v0) ?v1) ?v2) f1) (= (f3 ?v0 (f46 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S30)) (= (= (f46 (f31 (f32 f33 ?v0) ?v1) ?v2) f1) (= (f3 ?v0 (f46 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S4)) (= (= (f9 (f10 f11 ?v0) ?v1) f1) (= (f5 ?v1 ?v0) f1))))
(assert (forall ((?v0 S4)) (= (f6 f45 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S18) (?v3 S30)) (=> (= (f31 (f32 f33 ?v0) ?v1) ?v2) (= (= (f3 ?v0 (f46 ?v1 ?v3)) f1) (= (f46 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S4)) (= (not (= ?v0 f34)) (exists ((?v1 S3) (?v2 S4)) (and (= ?v0 (f6 (f7 f17 ?v1) ?v2)) (not (= (f9 (f10 f11 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (= (= (f5 f34 ?v0) f1) (= (f9 (f10 f11 ?v0) f34) f1))))
(assert (forall ((?v0 S12) (?v1 S34) (?v2 S12)) (= (f5 (f15 f16 (f35 f36 0)) (f18 (f19 (f20 f21 ?v0) (f57 f58 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S34) (?v1 S34)) (= (= (f57 f58 ?v0) (f57 f58 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S34)) (not (= (f23 (f24 f25 ?v0) ?v1) (f57 f58 ?v2)))))
(assert (forall ((?v0 S34) (?v1 S18) (?v2 S14)) (not (= (f57 f58 ?v0) (f23 (f24 f25 ?v1) ?v2)))))
(assert (forall ((?v0 S34) (?v1 S18) (?v2 S14) (?v3 S14)) (not (= (f57 f58 ?v0) (f23 (f48 (f49 f50 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14) (?v3 S34)) (not (= (f23 (f48 (f49 f50 ?v0) ?v1) ?v2) (f57 f58 ?v3)))))
(assert (forall ((?v0 S34) (?v1 S14) (?v2 S14)) (not (= (f57 f58 ?v0) (f23 (f48 f55 ?v1) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S34)) (not (= (f23 (f48 f55 ?v0) ?v1) (f57 f58 ?v2)))))
(assert (forall ((?v0 S34)) (not (= f54 (f57 f58 ?v0)))))
(assert (forall ((?v0 S34)) (not (= (f57 f58 ?v0) f54))))
(assert (forall ((?v0 S12) (?v1 S34) (?v2 S12) (?v3 S4)) (let ((?v_0 (f20 f21 ?v0))) (let ((?v_1 (f7 f17 (f18 (f19 ?v_0 (f57 f58 ?v1)) ?v2)))) (=> (= (f9 (f39 f41 (f6 ?v_1 ?v3)) (f6 (f7 f17 (f18 (f19 ?v_0 (f59 f60 (f61 ?v1))) ?v2)) f34)) f1) (= (f9 (f39 f41 ?v3) (f6 ?v_1 f34)) f1))))))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S34) (?v3 S12)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f20 f21 ?v1))) (=> (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 ?v_1 (f59 f60 (f61 ?v2))) ?v3)) f34)) f1) (= (f9 ?v_0 (f6 (f7 f17 (f18 (f19 ?v_1 (f57 f58 ?v2)) ?v3)) f34)) f1)))))
(assert (forall ((?v0 S38) (?v1 S3) (?v2 S3)) (= (= (f5 (f6 (f62 f63 ?v0) (f6 (f7 f17 ?v1) f34)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S38) (?v1 S33) (?v2 S3)) (=> (= (f64 (f65 f66 ?v0) ?v1) f1) (= (f51 ?v1 (f6 (f7 f17 ?v2) f34)) ?v2))))
(assert (= (f67 f68 f69) f1))
(assert (= (f70 f71 f56) f1))
(assert (forall ((?v0 S9) (?v1 S12) (?v2 S14) (?v3 S12)) (= (= (f5 (f15 f16 ?v0) (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S29) (?v5 S30)) (=> (= (f46 (f47 ?v1 ?v4) ?v5) f1) (forall ((?v6 S30)) (=> (= (f46 (f72 (f73 (f74 f75 ?v2) ?v5) ?v0) ?v6) f1) (= (f46 (f47 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S27)) (= (f70 f71 ?v0) f1)))
(assert (forall ((?v0 S43)) (= (f67 f68 ?v0) f1)))
(assert (forall ((?v0 S27)) (= (= (f70 f71 ?v0) f1) (exists ((?v1 S27)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S43)) (= (= (f67 f68 ?v0) f1) (exists ((?v1 S43)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S34)) (= (f76 f69 (f57 f58 ?v0)) (f35 f36 0))))
(assert (forall ((?v0 S18) (?v1 S14)) (= (f76 f69 (f23 (f24 f25 ?v0) ?v1)) (f35 f36 (+ (f37 f38 (f76 f69 ?v1)) (+ 0 1))))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14)) (= (f76 f69 (f23 (f48 (f49 f50 ?v0) ?v1) ?v2)) (f35 f36 (+ (+ (f37 f38 (f76 f69 ?v1)) (f37 f38 (f76 f69 ?v2))) (+ 0 1))))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f76 f69 (f23 (f48 f55 ?v0) ?v1)) (f35 f36 (+ (+ (f37 f38 (f76 f69 ?v0)) (f37 f38 (f76 f69 ?v1))) (+ 0 1))))))
(assert (= (f76 f69 f54) (f35 f36 0)))
(assert (forall ((?v0 S38) (?v1 S3)) (=> (= (f5 (f6 (f62 f63 ?v0) f34) ?v1) f1) false)))
(assert (forall ((?v0 S38) (?v1 S4) (?v2 S3)) (=> (= (f5 (f6 (f62 f63 ?v0) ?v1) ?v2) f1) (not (= ?v1 f34)))))
(assert (forall ((?v0 S9) (?v1 S12) (?v2 S34) (?v3 S12)) (let ((?v_0 (f20 f21 ?v1))) (= (= (f5 (f15 f16 ?v0) (f18 (f19 ?v_0 (f59 f60 (f61 ?v2))) ?v3)) f1) (= (f5 (f15 f16 (f35 f36 (+ (f37 f38 ?v0) 1))) (f18 (f19 ?v_0 (f57 f58 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S34) (?v1 S30) (?v2 S9) (?v3 S30)) (=> (= (f46 (f72 (f73 (f74 f75 (f59 f60 (f61 ?v0))) ?v1) ?v2) ?v3) f1) (= (f46 (f72 (f73 (f74 f75 (f57 f58 ?v0)) ?v1) (f35 f36 (+ (f37 f38 ?v2) 1))) ?v3) f1))))
(assert (forall ((?v0 S30) (?v1 S9)) (= (f46 (f72 (f73 (f74 f75 f54) ?v0) ?v1) ?v0) f1)))
(assert (forall ((?v0 S30) (?v1 S9) (?v2 S30)) (=> (= (f46 (f72 (f73 (f74 f75 f54) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S14) (?v1 S30) (?v2 S9) (?v3 S30) (?v4 S14) (?v5 S30)) (=> (= (f46 (f72 (f73 (f74 f75 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f46 (f72 (f73 (f74 f75 ?v4) ?v3) ?v2) ?v5) f1) (= (f46 (f72 (f73 (f74 f75 (f23 (f48 f55 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (forall ((?v0 S18) (?v1 S30) (?v2 S14) (?v3 S9) (?v4 S30) (?v5 S14)) (=> (not (= (f46 ?v0 ?v1) f1)) (=> (= (f46 (f72 (f73 (f74 f75 ?v2) ?v1) ?v3) ?v4) f1) (= (f46 (f72 (f73 (f74 f75 (f23 (f48 (f49 f50 ?v0) ?v5) ?v2)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S18) (?v1 S30) (?v2 S14) (?v3 S9)) (=> (not (= (f46 ?v0 ?v1) f1)) (= (f46 (f72 (f73 (f74 f75 (f23 (f24 f25 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S30) (?v2 S14) (?v3 S9) (?v4 S30) (?v5 S30)) (let ((?v_0 (f74 f75 (f23 (f24 f25 ?v0) ?v2)))) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f46 (f72 (f73 (f74 f75 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f46 (f72 (f73 ?v_0 ?v4) ?v3) ?v5) f1) (= (f46 (f72 (f73 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S18) (?v1 S14) (?v2 S14) (?v3 S30) (?v4 S9) (?v5 S30)) (let ((?v_0 (= (f46 ?v0 ?v3) f1))) (=> (= (f46 (f72 (f73 (f74 f75 (f23 (f48 (f49 f50 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (=> ?v_0 (=> (= (f46 (f72 (f73 (f74 f75 ?v1) ?v3) ?v4) ?v5) f1) false)) (=> (=> (not ?v_0) (=> (= (f46 (f72 (f73 (f74 f75 ?v2) ?v3) ?v4) ?v5) f1) false)) false))))))
(assert (forall ((?v0 S18) (?v1 S30) (?v2 S14) (?v3 S9) (?v4 S30) (?v5 S14)) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f46 (f72 (f73 (f74 f75 ?v2) ?v1) ?v3) ?v4) f1) (= (f46 (f72 (f73 (f74 f75 (f23 (f48 (f49 f50 ?v0) ?v2) ?v5)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S14) (?v1 S30) (?v2 S9) (?v3 S30)) (let ((?v_0 (f73 (f74 f75 ?v0) ?v1))) (=> (= (f46 (f72 ?v_0 ?v2) ?v3) f1) (= (f46 (f72 ?v_0 (f35 f36 (+ (f37 f38 ?v2) 1))) ?v3) f1)))))
(assert (forall ((?v0 S14) (?v1 S30) (?v2 S9) (?v3 S30) (?v4 S9)) (let ((?v_0 (f73 (f74 f75 ?v0) ?v1))) (=> (= (f46 (f72 ?v_0 ?v2) ?v3) f1) (=> (<= (f37 f38 ?v2) (f37 f38 ?v4)) (= (f46 (f72 ?v_0 ?v4) ?v3) f1))))))
(assert (forall ((?v0 S34) (?v1 S30) (?v2 S9) (?v3 S30)) (=> (= (f46 (f72 (f73 (f74 f75 (f57 f58 ?v0)) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S9)) (=> (= ?v2 (f35 f36 (+ (f37 f38 ?v4) 1))) (=> (= (f46 (f72 (f73 (f74 f75 (f59 f60 (f61 ?v0))) ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S30) (?v3 S9) (?v4 S30)) (=> (= (f46 (f72 (f73 (f74 f75 (f23 (f48 f55 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (forall ((?v5 S30)) (=> (= (f46 (f72 (f73 (f74 f75 ?v0) ?v2) ?v3) ?v5) f1) (=> (= (f46 (f72 (f73 (f74 f75 ?v1) ?v5) ?v3) ?v4) f1) false))) false))))
(assert (forall ((?v0 S9)) (= (f35 f36 (f37 f38 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f37 f38 (f35 f36 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f37 f38 (f35 f36 ?v0)) 0))))
(check-sat)
(exit)

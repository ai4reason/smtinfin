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
(declare-sort S48 0)
(declare-sort S49 0)
(declare-sort S50 0)
(declare-sort S51 0)
(declare-sort S52 0)
(declare-sort S53 0)
(declare-sort S54 0)
(declare-sort S55 0)
(declare-sort S56 0)
(declare-sort S57 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S2) S4)
(declare-fun f5 () S5)
(declare-fun f6 () S5)
(declare-fun f7 (S6 S7) S3)
(declare-fun f8 (S8 S9) S6)
(declare-fun f9 (S10 S3) S8)
(declare-fun f10 () S10)
(declare-fun f11 (S11 S12) S9)
(declare-fun f12 () S11)
(declare-fun f13 () S12)
(declare-fun f14 (S13 S3) S7)
(declare-fun f15 () S13)
(declare-fun f16 (S15 S14) S1)
(declare-fun f17 (S16 S14) S15)
(declare-fun f18 () S16)
(declare-fun f19 () S16)
(declare-fun f20 (S17 S15) S15)
(declare-fun f21 (S18 S14) S17)
(declare-fun f22 () S18)
(declare-fun f23 (S19 S15) S1)
(declare-fun f24 (S20 S14) S19)
(declare-fun f25 () S20)
(declare-fun f26 () S18)
(declare-fun f27 () S18)
(declare-fun f28 () S18)
(declare-fun f29 (S21 S3) S5)
(declare-fun f30 () S21)
(declare-fun f31 (S22 S2) S5)
(declare-fun f32 (S23 S5) S22)
(declare-fun f33 () S23)
(declare-fun f34 (S24 S5) S5)
(declare-fun f35 (S25 S5) S24)
(declare-fun f36 () S25)
(declare-fun f37 (S26 S4) S5)
(declare-fun f38 (S27 S5) S26)
(declare-fun f39 () S27)
(declare-fun f40 (S28 S1) S24)
(declare-fun f41 () S28)
(declare-fun f42 (S29 S5) S21)
(declare-fun f43 () S29)
(declare-fun f44 (S30 S12) S21)
(declare-fun f45 (S31 S5) S30)
(declare-fun f46 () S31)
(declare-fun f47 (S32 S12) S7)
(declare-fun f48 (S33 S3) S32)
(declare-fun f49 () S33)
(declare-fun f50 (S34 S13) S5)
(declare-fun f51 (S35 S9) S34)
(declare-fun f52 (S36 S5) S35)
(declare-fun f53 () S36)
(declare-fun f54 (S37 S3) S34)
(declare-fun f55 (S38 S12) S37)
(declare-fun f56 (S39 S5) S38)
(declare-fun f57 () S39)
(declare-fun f58 () S5)
(declare-fun f59 () S5)
(declare-fun f60 () S15)
(declare-fun f61 (S40 S15) S19)
(declare-fun f62 () S40)
(declare-fun f63 () S15)
(declare-fun f64 () S18)
(declare-fun f65 (S41 S5) S14)
(declare-fun f66 (S42 S43) S41)
(declare-fun f67 (S44 S5) S42)
(declare-fun f68 () S44)
(declare-fun f69 (S45 S43) S43)
(declare-fun f70 (S46 S13) S45)
(declare-fun f71 (S47 S12) S46)
(declare-fun f72 () S47)
(declare-fun f73 () S43)
(declare-fun f74 () S5)
(declare-fun f75 () S15)
(declare-fun f76 () S17)
(declare-fun f77 (S48 S15) S14)
(declare-fun f78 () S48)
(declare-fun f79 (S50 S14) S7)
(declare-fun f80 (S51 S49) S50)
(declare-fun f81 () S51)
(declare-fun f82 (S52 Int) S7)
(declare-fun f83 () S52)
(declare-fun f84 (S53 S13) S43)
(declare-fun f85 (S54 S9) S53)
(declare-fun f86 () S54)
(declare-fun f87 () S1)
(declare-fun f88 () S43)
(declare-fun f89 (S55 S4) S45)
(declare-fun f90 () S55)
(declare-fun f91 (S56 S43) S45)
(declare-fun f92 () S56)
(declare-fun f93 (S57 S7) Int)
(declare-fun f94 () S57)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v0) (f7 (f8 (f9 f10 ?v1) (f11 f12 f13)) (f14 f15 ?v1))) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f16 (f17 f18 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f16 (f17 f19 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S14)) (= (= (f16 (f20 (f21 f22 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f23 (f24 f25 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S14)) (= (= (f16 (f20 (f21 f26 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f16 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S14)) (= (= (f16 (f20 (f21 f27 ?v0) ?v1) ?v2) f1) (and (= ?v2 ?v0) (= (f16 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S14)) (= (= (f16 (f20 (f21 f28 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f16 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f29 f30 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (= (f4 (f31 (f32 f33 ?v0) ?v1) ?v2) (f4 ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2) (?v3 S3)) (= (= (f3 (f4 (f34 (f35 f36 ?v0) ?v1) ?v2) ?v3) f1) (or (= (f3 (f4 ?v0 ?v2) ?v3) f1) (= (f3 (f4 ?v1 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S4) (?v2 S2) (?v3 S3)) (= (= (f3 (f4 (f37 (f38 f39 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f3 (f4 ?v0 ?v2) ?v3) f1) (not (= (f3 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S5) (?v2 S2) (?v3 S3)) (= (= (f3 (f4 (f34 (f40 f41 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f3 (f4 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f3 (f4 (f29 (f42 f43 ?v0) ?v1) ?v2) ?v3) f1) (and (= ?v1 ?v3) (= (f3 (f4 ?v0 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S12) (?v2 S3) (?v3 S2) (?v4 S3)) (= (= (f3 (f4 (f29 (f44 (f45 f46 ?v0) ?v1) ?v2) ?v3) ?v4) f1) (= (f3 (f4 ?v0 ?v3) (f7 (f8 (f9 f10 ?v4) (f11 f12 ?v1)) (f47 (f48 f49 ?v2) ?v1))) f1))))
(assert (forall ((?v0 S5) (?v1 S9) (?v2 S13) (?v3 S2) (?v4 S3)) (= (= (f3 (f4 (f50 (f51 (f52 f53 ?v0) ?v1) ?v2) ?v3) ?v4) f1) (= (f3 (f4 ?v0 ?v3) (f7 (f8 (f9 f10 ?v4) ?v1) (f14 ?v2 ?v4))) f1))))
(assert (forall ((?v0 S5) (?v1 S12) (?v2 S3) (?v3 S13) (?v4 S2) (?v5 S3)) (= (= (f3 (f4 (f50 (f54 (f55 (f56 f57 ?v0) ?v1) ?v2) ?v3) ?v4) ?v5) f1) (and (= ?v2 ?v5) (= (f3 (f4 ?v0 ?v4) (f7 (f8 (f9 f10 ?v5) (f11 f12 ?v1)) (f14 ?v3 ?v5))) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f58 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f59 ?v0) ?v1) f1) true)))
(assert (forall ((?v0 S14)) (= (= (f16 f60 ?v0) f1) false)))
(assert (not (= (f23 (f61 f62 f63) (f20 (f21 f64 (f65 (f66 (f67 f68 f5) (f69 (f70 (f71 f72 f13) f15) f73)) f74)) f75)) f1)))
(assert (= (f23 (f61 f62 f63) (f20 (f21 f64 (f65 (f66 (f67 f68 f6) f73) f74)) f75)) f1))
(assert (forall ((?v0 S7) (?v1 S2) (?v2 S3)) (let ((?v_0 (f4 f74 ?v1))) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f7 (f8 (f9 f10 ?v2) (f11 f12 f13)) ?v0)) f1)))))
(assert (forall ((?v0 S15)) (= (f23 (f61 f62 ?v0) f75) f1)))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43)) (= (f23 (f61 f62 ?v0) (f20 (f21 f64 (f65 (f66 (f67 f68 ?v1) ?v2) f59)) f75)) f1)))
(assert (forall ((?v0 S15) (?v1 S43) (?v2 S5)) (= (f23 (f61 f62 ?v0) (f20 (f21 f64 (f65 (f66 (f67 f68 f58) ?v1) ?v2)) f75)) f1)))
(assert (forall ((?v0 S14)) (let ((?v_0 (f20 (f21 f64 ?v0) f75))) (= (f23 (f61 f62 ?v_0) ?v_0) f1))))
(assert (forall ((?v0 S5) (?v1 S43) (?v2 S5) (?v3 S5) (?v4 S43) (?v5 S5)) (= (= (f65 (f66 (f67 f68 ?v0) ?v1) ?v2) (f65 (f66 (f67 f68 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f61 f62 ?v2))) (=> (= (f23 (f61 f62 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S15) (?v1 S14) (?v2 S15)) (let ((?v_0 (f61 f62 ?v0)) (?v_1 (f21 f64 ?v1))) (=> (= (f23 ?v_0 (f20 ?v_1 f75)) f1) (=> (= (f23 ?v_0 ?v2) f1) (= (f23 ?v_0 (f20 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S15) (?v1 S14) (?v2 S15)) (let ((?v_0 (f61 f62 ?v0)) (?v_1 (f21 f64 ?v1))) (=> (= (f23 ?v_0 (f20 ?v_1 ?v2)) f1) (and (= (f23 ?v_0 (f20 ?v_1 f75)) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43) (?v3 S5) (?v4 S5) (?v5 S5)) (let ((?v_0 (f61 f62 ?v0))) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v1) ?v2) ?v3)) f75)) f1) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v4) ?v2) ?v5)) f75)) f1) (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 (f34 (f35 f36 ?v1) ?v4)) ?v2) (f34 (f35 f36 ?v3) ?v5))) f75)) f1))))))
(assert (forall ((?v0 S1) (?v1 S15) (?v2 S5) (?v3 S43) (?v4 S5)) (let ((?v_0 (f61 f62 ?v1))) (=> (=> (= ?v0 f1) (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v2) ?v3) ?v4)) f75)) f1)) (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 (f34 (f40 f41 ?v0) ?v2)) ?v3) ?v4)) f75)) f1)))))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43) (?v3 S5)) (=> (forall ((?v4 S3)) (= (f23 (f61 f62 ?v0) (f20 (f21 f64 (f65 (f66 (f67 f68 (f29 (f42 f43 ?v1) ?v4)) ?v2) ?v3)) f75)) f1)) (= (f23 (f61 f62 ?v0) (f20 (f21 f64 (f65 (f66 (f67 f68 ?v1) ?v2) ?v3)) f75)) f1))))
(assert (forall ((?v0 S5) (?v1 S15) (?v2 S43) (?v3 S5)) (=> (forall ((?v4 S2) (?v5 S3)) (=> (= (f3 (f4 ?v0 ?v4) ?v5) f1) (= (f23 (f61 f62 ?v1) (f20 (f21 f64 (f65 (f66 (f67 f68 (f29 f30 ?v5)) ?v2) (f31 (f32 f33 ?v3) ?v4))) f75)) f1))) (= (f23 (f61 f62 ?v1) (f20 (f21 f64 (f65 (f66 (f67 f68 ?v0) ?v2) ?v3)) f75)) f1))))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43) (?v3 S5) (?v4 S5)) (let ((?v_0 (f61 f62 ?v0)) (?v_1 (f66 (f67 f68 ?v1) ?v2))) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 ?v_1 ?v3)) f75)) f1) (=> (forall ((?v5 S2) (?v6 S3)) (=> (= (f3 (f4 ?v3 ?v5) ?v6) f1) (= (f3 (f4 ?v4 ?v5) ?v6) f1))) (= (f23 ?v_0 (f20 (f21 f64 (f65 ?v_1 ?v4)) f75)) f1))))))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43) (?v3 S5) (?v4 S5)) (let ((?v_0 (f61 f62 ?v0))) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v1) ?v2) ?v3)) f75)) f1) (=> (forall ((?v5 S2) (?v6 S3)) (=> (= (f3 (f4 ?v4 ?v5) ?v6) f1) (= (f3 (f4 ?v1 ?v5) ?v6) f1))) (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v4) ?v2) ?v3)) f75)) f1))))))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43) (?v3 S5) (?v4 S12) (?v5 S3) (?v6 S13)) (let ((?v_0 (f61 f62 ?v0))) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v1) ?v2) (f29 (f44 (f45 f46 ?v3) ?v4) ?v5))) f75)) f1) (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 (f50 (f54 (f55 (f56 f57 ?v1) ?v4) ?v5) ?v6)) (f69 (f70 (f71 f72 ?v4) ?v6) ?v2)) ?v3)) f75)) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S15)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 (f20 (f21 f64 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f23 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S14)) (let ((?v_0 (f24 f25 ?v0))) (=> (=> (not (= (f23 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f23 ?v_0 (f20 (f21 f64 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S14)) (=> (= (f23 (f24 f25 ?v0) f75) f1) false)))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43) (?v3 S5) (?v4 S5) (?v5 S5)) (let ((?v_0 (f61 f62 ?v0))) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v1) ?v2) ?v3)) f75)) f1) (=> (forall ((?v6 S2) (?v7 S3)) (=> (= (f3 (f4 ?v4 ?v6) ?v7) f1) (forall ((?v8 S3)) (=> (forall ((?v9 S2)) (=> (= (f3 (f4 ?v1 ?v9) ?v7) f1) (= (f3 (f4 ?v3 ?v9) ?v8) f1))) (= (f3 (f4 ?v5 ?v6) ?v8) f1))))) (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v4) ?v2) ?v5)) f75)) f1))))))
(assert (forall ((?v0 S14)) (= (f20 f76 (f17 f18 ?v0)) (f20 (f21 f64 ?v0) f75))))
(assert (forall ((?v0 S14)) (= (f20 f76 (f17 f19 ?v0)) (f20 (f21 f64 ?v0) f75))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f20 f76 (f20 (f21 f26 ?v0) ?v1)) (ite (= (f16 ?v1 ?v0) f1) (f20 (f21 f64 ?v0) f75) f75))))
(assert (forall ((?v0 S15) (?v1 S14)) (=> (= ?v0 f75) (not (= (f23 (f24 f25 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S15)) (= (= (f20 f76 ?v0) f75) (forall ((?v1 S14)) (not (= (f16 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14)) (= (= (f23 (f24 f25 ?v0) f75) f1) false)))
(assert (forall ((?v0 S15)) (= (= f75 (f20 f76 ?v0)) (forall ((?v1 S14)) (not (= (f16 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S15)) (= (forall ((?v1 S14)) (=> (= (f23 (f24 f25 ?v1) f75) f1) (= (f16 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S15)) (= (exists ((?v1 S14)) (and (= (f23 (f24 f25 ?v1) f75) f1) (= (f16 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S15)) (= (exists ((?v1 S14)) (= (f23 (f24 f25 ?v1) ?v0) f1)) (not (= ?v0 f75)))))
(assert (forall ((?v0 S15)) (= (forall ((?v1 S14)) (not (= (f23 (f24 f25 ?v1) ?v0) f1))) (= ?v0 f75))))
(assert (= f75 (f20 f76 f60)))
(assert (forall ((?v0 S14) (?v1 S15)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f20 (f21 f64 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S14)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 (f20 (f21 f64 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S15)) (let ((?v_0 (f24 f25 ?v0)) (?v_1 (f21 f64 ?v0))) (=> (not (= (f23 ?v_0 ?v1) f1)) (=> (not (= (f23 ?v_0 ?v2) f1)) (= (= (f20 ?v_1 ?v1) (f20 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S14)) (= (= (f16 (f20 (f21 f64 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f16 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S15)) (let ((?v_0 (f24 f25 ?v0))) (= (= (f23 ?v_0 (f20 (f21 f64 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S15)) (let ((?v_1 (f21 f64 ?v0)) (?v_0 (f21 f64 ?v1))) (= (f20 ?v_1 (f20 ?v_0 ?v2)) (f20 ?v_0 (f20 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S15)) (let ((?v_0 (f21 f64 ?v0))) (let ((?v_1 (f20 ?v_0 ?v1))) (= (f20 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f20 (f21 f64 ?v0) (f20 f76 ?v1)) (f20 f76 (f20 (f21 f28 ?v0) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f20 (f21 f64 ?v0) ?v1) (f20 f76 (f20 (f21 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f23 (f24 f25 ?v0) (f20 (f21 f64 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f20 (f21 f64 ?v0) ?v1) (f20 f76 (f20 (f21 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f20 (f21 f64 ?v0) f75) (f20 (f21 f64 ?v1) f75)) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f23 (f24 f25 ?v0) (f20 (f21 f64 ?v1) f75)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (= (= (f20 (f21 f64 ?v0) (f20 (f21 f64 ?v1) f75)) (f20 (f21 f64 ?v2) (f20 (f21 f64 ?v3) f75))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f23 (f24 f25 ?v0) (f20 (f21 f64 ?v1) f75)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S15)) (not (= (f20 (f21 f64 ?v0) ?v1) f75))))
(assert (forall ((?v0 S14) (?v1 S15)) (not (= f75 (f20 (f21 f64 ?v0) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f20 f76 (f20 (f21 f27 ?v0) ?v1)) (ite (= (f16 ?v1 ?v0) f1) (f20 (f21 f64 ?v0) f75) f75))))
(assert (forall ((?v0 S14)) (= (f77 f78 (f20 (f21 f64 ?v0) f75)) ?v0)))
(assert (forall ((?v0 S49) (?v1 S5) (?v2 S43) (?v3 S5)) (= (f79 (f80 f81 ?v0) (f65 (f66 (f67 f68 ?v1) ?v2) ?v3)) (f82 f83 0))))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S9) (?v3 S13)) (= (f23 (f61 f62 ?v0) (f20 (f21 f64 (f65 (f66 (f67 f68 (f50 (f51 (f52 f53 ?v1) ?v2) ?v3)) (f84 (f85 f86 ?v2) ?v3)) ?v1)) f75)) f1)))
(assert (forall ((?v0 S14)) (= (= (f16 f75 ?v0) f1) (= f87 f1))))
(assert (forall ((?v0 S14)) (= (= (f16 f75 ?v0) f1) (= f87 f1))))
(assert (forall ((?v0 S15) (?v1 S5)) (= (f23 (f61 f62 ?v0) (f20 (f21 f64 (f65 (f66 (f67 f68 ?v1) f88) ?v1)) f75)) f1)))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S4) (?v3 S43)) (= (f23 (f61 f62 ?v0) (f20 (f21 f64 (f65 (f66 (f67 f68 (f37 (f38 f39 ?v1) ?v2)) (f69 (f89 f90 ?v2) ?v3)) ?v1)) f75)) f1)))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S43) (?v3 S5) (?v4 S43) (?v5 S5)) (let ((?v_0 (f61 f62 ?v0)) (?v_1 (f67 f68 ?v1))) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 ?v_1 ?v2) ?v3)) f75)) f1) (=> (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 (f67 f68 ?v3) ?v4) ?v5)) f75)) f1) (= (f23 ?v_0 (f20 (f21 f64 (f65 (f66 ?v_1 (f69 (f91 f92 ?v2) ?v4)) ?v5)) f75)) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S15)) (=> (forall ((?v3 S2) (?v4 S3)) (=> (= (f3 (f4 ?v0 ?v3) ?v4) f1) (= (f3 (f4 ?v1 ?v3) ?v4) f1))) (= (f23 (f61 f62 ?v2) (f20 (f21 f64 (f65 (f66 (f67 f68 ?v0) f88) ?v1)) f75)) f1))))
(assert (forall ((?v0 S43) (?v1 S43)) (not (= (f69 (f91 f92 ?v0) ?v1) f88))))
(assert (forall ((?v0 S9) (?v1 S13)) (not (= (f84 (f85 f86 ?v0) ?v1) f88))))
(assert (forall ((?v0 S43) (?v1 S43)) (not (= f88 (f69 (f91 f92 ?v0) ?v1)))))
(assert (forall ((?v0 S7)) (= (f82 f83 (f93 f94 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f93 f94 (f82 f83 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f93 f94 (f82 f83 ?v0)) 0))))
(check-sat)
(exit)

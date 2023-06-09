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
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 () S5)
(declare-fun f7 (S7 S8) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S2) S8)
(declare-fun f10 () S3)
(declare-fun f11 (S9 S2) S6)
(declare-fun f12 () S9)
(declare-fun f13 (S11 S10) S1)
(declare-fun f14 (S12 S10) S11)
(declare-fun f15 () S12)
(declare-fun f16 (S13 S10) Int)
(declare-fun f17 () S13)
(declare-fun f18 (S15 S14) S3)
(declare-fun f19 (S16 S14) S15)
(declare-fun f20 () S16)
(declare-fun f21 (S17 S18) S4)
(declare-fun f22 (S19 S6) S17)
(declare-fun f23 (S20 S18) S19)
(declare-fun f24 () S20)
(declare-fun f25 (S14 S2) S18)
(declare-fun f26 () S16)
(declare-fun f27 (S21 S4) S1)
(declare-fun f28 (S22 S21) S21)
(declare-fun f29 (S23 S21) S22)
(declare-fun f30 () S23)
(declare-fun f31 (S24 S2) S1)
(declare-fun f32 (S25 S24) S24)
(declare-fun f33 (S26 S24) S25)
(declare-fun f34 () S26)
(declare-fun f35 (S27 S11) S11)
(declare-fun f36 (S28 S11) S27)
(declare-fun f37 () S28)
(declare-fun f38 (S29 S21) S1)
(declare-fun f39 (S30 S21) S29)
(declare-fun f40 () S30)
(declare-fun f41 () S21)
(declare-fun f42 (S31 S24) S21)
(declare-fun f43 (S32 S3) S31)
(declare-fun f44 () S32)
(declare-fun f45 () S24)
(declare-fun f46 () S23)
(declare-fun f47 (S33 S24) S1)
(declare-fun f48 () S33)
(declare-fun f49 () S29)
(declare-fun f50 (S35 S21) S24)
(declare-fun f51 (S36 S34) S35)
(declare-fun f52 () S36)
(declare-fun f53 (S38 S11) S1)
(declare-fun f54 () S38)
(declare-fun f55 (S39 S11) S24)
(declare-fun f56 (S40 S37) S39)
(declare-fun f57 () S40)
(declare-fun f58 (S42 S24) S11)
(declare-fun f59 (S43 S41) S42)
(declare-fun f60 () S43)
(declare-fun f61 (S45 S11) S21)
(declare-fun f62 (S46 S44) S45)
(declare-fun f63 () S46)
(declare-fun f64 (S48 S47) S27)
(declare-fun f65 () S48)
(declare-fun f66 () S27)
(declare-fun f67 () S25)
(declare-fun f68 () S22)
(declare-fun f69 (S49 S4) S29)
(declare-fun f70 () S49)
(declare-fun f71 (S50 S10) S38)
(declare-fun f72 () S50)
(declare-fun f73 () S28)
(declare-fun f74 (S51 S2) S33)
(declare-fun f75 () S51)
(declare-fun f76 () S26)
(declare-fun f77 (S44 S10) S4)
(declare-fun f78 (S47 S10) S10)
(declare-fun f79 (S41 S2) S10)
(declare-fun f80 (S52 S4) S10)
(declare-fun f81 (S53 S21) S11)
(declare-fun f82 (S54 S52) S53)
(declare-fun f83 () S54)
(declare-fun f84 (S34 S4) S2)
(declare-fun f85 (S37 S10) S2)
(declare-fun f86 (S55 S1) S1)
(declare-fun f87 (S56 S1) S55)
(declare-fun f88 () S56)
(declare-fun f89 (S57 Int) S10)
(declare-fun f90 () S57)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 f6 (f7 f8 (f9 ?v0))))))
(assert (forall ((?v0 S2)) (= (f3 f10 ?v0) (f5 f6 (f11 f12 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f13 (f14 f15 ?v0) ?v1) f1) (< (f16 f17 ?v1) (f16 f17 ?v0)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (f3 (f18 (f19 f20 ?v0) ?v1) ?v2) (f21 (f22 (f23 f24 (f25 ?v0 ?v2)) (f7 f8 (f9 ?v2))) (f25 ?v1 ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (f3 (f18 (f19 f26 ?v0) ?v1) ?v2) (f21 (f22 (f23 f24 (f25 ?v0 ?v2)) (f11 f12 ?v2)) (f25 ?v1 ?v2)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S4)) (= (= (f27 (f28 (f29 f30 ?v0) ?v1) ?v2) f1) (and (= (f27 ?v0 ?v2) f1) (= (f27 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S2)) (= (= (f31 (f32 (f33 f34 ?v0) ?v1) ?v2) f1) (and (= (f31 ?v0 ?v2) f1) (= (f31 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S10)) (= (= (f13 (f35 (f36 f37 ?v0) ?v1) ?v2) f1) (and (= (f13 ?v0 ?v2) f1) (= (f13 ?v1 ?v2) f1)))))
(assert (not (= (f38 (f39 f40 f41) (f42 (f43 f44 f10) f45)) f1)))
(assert (= (f38 (f39 f40 (f28 (f29 f46 f41) (f42 (f43 f44 f10) f45))) (f42 (f43 f44 f4) f45)) f1))
(assert (= (f47 f48 f45) f1))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_0 (f39 f40 ?v2))) (=> (= (f38 (f39 f40 ?v0) ?v1) f1) (=> (= (f38 ?v_0 ?v0) f1) (= (f38 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S24) (?v1 S3)) (=> (= (f47 f48 ?v0) f1) (= (f38 f49 (f42 (f43 f44 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S21) (?v1 S34)) (=> (= (f38 f49 ?v0) f1) (= (f47 f48 (f50 (f51 f52 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S37)) (=> (= (f53 f54 ?v0) f1) (= (f47 f48 (f55 (f56 f57 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S24) (?v1 S41)) (=> (= (f47 f48 ?v0) f1) (= (f53 f54 (f58 (f59 f60 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S44)) (=> (= (f53 f54 ?v0) f1) (= (f38 f49 (f61 (f62 f63 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S47)) (=> (= (f53 f54 ?v0) f1) (= (f53 f54 (f35 (f64 f65 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (or (= (f53 f54 (f35 f66 ?v0)) f1) (= (f53 f54 (f35 f66 ?v1)) f1)) (= (f53 f54 (f35 f66 (f35 (f36 f37 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S24) (?v1 S24)) (=> (or (= (f47 f48 (f32 f67 ?v0)) f1) (= (f47 f48 (f32 f67 ?v1)) f1)) (= (f47 f48 (f32 f67 (f32 (f33 f34 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S21) (?v1 S21)) (=> (or (= (f38 f49 (f28 f68 ?v0)) f1) (= (f38 f49 (f28 f68 ?v1)) f1)) (= (f38 f49 (f28 f68 (f28 (f29 f30 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S21)) (let ((?v_0 (f69 f70 ?v0))) (=> (= (f38 ?v_0 (f28 (f29 f46 ?v1) ?v2)) f1) (=> (=> (= (f38 ?v_0 ?v1) f1) false) (=> (=> (= (f38 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S11)) (let ((?v_0 (f71 f72 ?v0))) (=> (= (f53 ?v_0 (f35 (f36 f73 ?v1) ?v2)) f1) (=> (=> (= (f53 ?v_0 ?v1) f1) false) (=> (=> (= (f53 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S24)) (let ((?v_0 (f74 f75 ?v0))) (=> (= (f47 ?v_0 (f32 (f33 f76 ?v1) ?v2)) f1) (=> (=> (= (f47 ?v_0 ?v1) f1) false) (=> (=> (= (f47 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S4)) (=> (= (f27 (f28 (f29 f46 ?v0) ?v1) ?v2) f1) (=> (=> (= (f27 ?v0 ?v2) f1) false) (=> (=> (= (f27 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S10)) (=> (= (f13 (f35 (f36 f73 ?v0) ?v1) ?v2) f1) (=> (=> (= (f13 ?v0 ?v2) f1) false) (=> (=> (= (f13 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S2)) (=> (= (f31 (f32 (f33 f76 ?v0) ?v1) ?v2) f1) (=> (=> (= (f31 ?v0 ?v2) f1) false) (=> (=> (= (f31 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S21) (?v1 S4) (?v2 S21)) (=> (=> (not (= (f27 ?v0 ?v1) f1)) (= (f27 ?v2 ?v1) f1)) (= (f27 (f28 (f29 f46 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S10) (?v2 S11)) (=> (=> (not (= (f13 ?v0 ?v1) f1)) (= (f13 ?v2 ?v1) f1)) (= (f13 (f35 (f36 f73 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S2) (?v2 S24)) (=> (=> (not (= (f31 ?v0 ?v1) f1)) (= (f31 ?v2 ?v1) f1)) (= (f31 (f32 (f33 f76 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S21)) (let ((?v_0 (f69 f70 ?v0))) (=> (=> (not (= (f38 ?v_0 ?v1) f1)) (= (f38 ?v_0 ?v2) f1)) (= (f38 ?v_0 (f28 (f29 f46 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S11)) (let ((?v_0 (f71 f72 ?v0))) (=> (=> (not (= (f53 ?v_0 ?v1) f1)) (= (f53 ?v_0 ?v2) f1)) (= (f53 ?v_0 (f35 (f36 f73 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S24)) (let ((?v_0 (f74 f75 ?v0))) (=> (=> (not (= (f47 ?v_0 ?v1) f1)) (= (f47 ?v_0 ?v2) f1)) (= (f47 ?v_0 (f32 (f33 f76 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S24)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f47 (f74 f75 ?v2) ?v3) f1) (= (f38 (f69 f70 ?v0) (f42 (f43 f44 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S44) (?v2 S10) (?v3 S11)) (=> (= ?v0 (f77 ?v1 ?v2)) (=> (= (f53 (f71 f72 ?v2) ?v3) f1) (= (f38 (f69 f70 ?v0) (f61 (f62 f63 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S10) (?v1 S47) (?v2 S10) (?v3 S11)) (=> (= ?v0 (f78 ?v1 ?v2)) (=> (= (f53 (f71 f72 ?v2) ?v3) f1) (= (f53 (f71 f72 ?v0) (f35 (f64 f65 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S10) (?v1 S41) (?v2 S2) (?v3 S24)) (=> (= ?v0 (f79 ?v1 ?v2)) (=> (= (f47 (f74 f75 ?v2) ?v3) f1) (= (f53 (f71 f72 ?v0) (f58 (f59 f60 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S10) (?v1 S52) (?v2 S4) (?v3 S21)) (=> (= ?v0 (f80 ?v1 ?v2)) (=> (= (f38 (f69 f70 ?v2) ?v3) f1) (= (f53 (f71 f72 ?v0) (f81 (f82 f83 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S34) (?v2 S4) (?v3 S21)) (=> (= ?v0 (f84 ?v1 ?v2)) (=> (= (f38 (f69 f70 ?v2) ?v3) f1) (= (f47 (f74 f75 ?v0) (f50 (f51 f52 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S37) (?v2 S10) (?v3 S11)) (=> (= ?v0 (f85 ?v1 ?v2)) (=> (= (f53 (f71 f72 ?v2) ?v3) f1) (= (f47 (f74 f75 ?v0) (f55 (f56 f57 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S21) (?v1 S14) (?v2 S14) (?v3 S24)) (let ((?v_0 (f42 (f43 f44 (f18 (f19 f26 ?v1) ?v2)) ?v3))) (=> (= (f38 (f39 f40 (f28 (f29 f46 ?v0) ?v_0)) (f42 (f43 f44 (f18 (f19 f20 ?v1) ?v2)) ?v3)) f1) (= (f38 (f39 f40 ?v0) ?v_0) f1)))))
(assert (forall ((?v0 S3) (?v1 S24) (?v2 S24)) (let ((?v_0 (f43 f44 ?v0))) (= (f42 ?v_0 (f32 (f33 f76 ?v1) ?v2)) (f28 (f29 f46 (f42 ?v_0 ?v1)) (f42 ?v_0 ?v2))))))
(assert (forall ((?v0 S52) (?v1 S21) (?v2 S21)) (let ((?v_0 (f82 f83 ?v0))) (= (f81 ?v_0 (f28 (f29 f46 ?v1) ?v2)) (f35 (f36 f73 (f81 ?v_0 ?v1)) (f81 ?v_0 ?v2))))))
(assert (forall ((?v0 S34) (?v1 S21) (?v2 S21)) (let ((?v_0 (f51 f52 ?v0))) (= (f50 ?v_0 (f28 (f29 f46 ?v1) ?v2)) (f32 (f33 f76 (f50 ?v_0 ?v1)) (f50 ?v_0 ?v2))))))
(assert (forall ((?v0 S44) (?v1 S11) (?v2 S11)) (let ((?v_0 (f62 f63 ?v0))) (= (f61 ?v_0 (f35 (f36 f73 ?v1) ?v2)) (f28 (f29 f46 (f61 ?v_0 ?v1)) (f61 ?v_0 ?v2))))))
(assert (forall ((?v0 S47) (?v1 S11) (?v2 S11)) (let ((?v_0 (f64 f65 ?v0))) (= (f35 ?v_0 (f35 (f36 f73 ?v1) ?v2)) (f35 (f36 f73 (f35 ?v_0 ?v1)) (f35 ?v_0 ?v2))))))
(assert (forall ((?v0 S41) (?v1 S24) (?v2 S24)) (let ((?v_0 (f59 f60 ?v0))) (= (f58 ?v_0 (f32 (f33 f76 ?v1) ?v2)) (f35 (f36 f73 (f58 ?v_0 ?v1)) (f58 ?v_0 ?v2))))))
(assert (forall ((?v0 S37) (?v1 S11) (?v2 S11)) (let ((?v_0 (f56 f57 ?v0))) (= (f55 ?v_0 (f35 (f36 f73 ?v1) ?v2)) (f32 (f33 f76 (f55 ?v_0 ?v1)) (f55 ?v_0 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S4)) (= (= (f27 (f28 (f29 f46 ?v0) ?v1) ?v2) f1) (= (f86 (f87 f88 (f27 ?v0 ?v2)) (f27 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S10)) (= (= (f13 (f35 (f36 f73 ?v0) ?v1) ?v2) f1) (= (f86 (f87 f88 (f13 ?v0 ?v2)) (f13 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S2)) (= (= (f31 (f32 (f33 f76 ?v0) ?v1) ?v2) f1) (= (f86 (f87 f88 (f31 ?v0 ?v2)) (f31 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S4)) (= (= (f27 (f28 (f29 f46 ?v0) ?v1) ?v2) f1) (= (f86 (f87 f88 (f27 ?v0 ?v2)) (f27 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S10)) (= (= (f13 (f35 (f36 f73 ?v0) ?v1) ?v2) f1) (= (f86 (f87 f88 (f13 ?v0 ?v2)) (f13 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S2)) (= (= (f31 (f32 (f33 f76 ?v0) ?v1) ?v2) f1) (= (f86 (f87 f88 (f31 ?v0 ?v2)) (f31 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (= (f47 f48 (f32 (f33 f76 ?v0) ?v1)) f1) (and (= (f47 f48 ?v0) f1) (= (f47 f48 ?v1) f1)))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f38 f49 (f28 (f29 f46 ?v0) ?v1)) f1) (and (= (f38 f49 ?v0) f1) (= (f38 f49 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f53 f54 (f35 (f36 f73 ?v0) ?v1)) f1) (and (= (f53 f54 ?v0) f1) (= (f53 f54 ?v1) f1)))))
(assert (forall ((?v0 S18) (?v1 S6) (?v2 S18) (?v3 S18) (?v4 S6) (?v5 S18)) (= (= (f21 (f22 (f23 f24 ?v0) ?v1) ?v2) (f21 (f22 (f23 f24 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S24) (?v1 S37) (?v2 S10)) (=> (= ?v0 (f55 (f56 f57 ?v1) (f35 f66 (f14 f15 ?v2)))) (= (f47 f48 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S47) (?v2 S10)) (=> (= ?v0 (f35 (f64 f65 ?v1) (f35 f66 (f14 f15 ?v2)))) (= (f53 f54 ?v0) f1))))
(assert (forall ((?v0 S21) (?v1 S44) (?v2 S10)) (=> (= ?v0 (f61 (f62 f63 ?v1) (f35 f66 (f14 f15 ?v2)))) (= (f38 f49 ?v0) f1))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_0 (f29 f46 ?v0))) (= (f28 (f29 f46 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f46 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f36 f73 ?v0))) (= (f35 (f36 f73 (f35 ?v_0 ?v1)) ?v2) (f35 ?v_0 (f35 (f36 f73 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f87 f88 ?v0))) (= (= (f86 (f87 f88 (f86 ?v_0 ?v1)) ?v2) f1) (= (f86 ?v_0 (f86 (f87 f88 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_0 (f33 f76 ?v0))) (= (f32 (f33 f76 (f32 ?v_0 ?v1)) ?v2) (f32 ?v_0 (f32 (f33 f76 ?v1) ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_0 (f29 f46 ?v0))) (= (f28 (f29 f46 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f46 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f36 f73 ?v0))) (= (f35 (f36 f73 (f35 ?v_0 ?v1)) ?v2) (f35 ?v_0 (f35 (f36 f73 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f87 f88 ?v0))) (= (= (f86 (f87 f88 (f86 ?v_0 ?v1)) ?v2) f1) (= (f86 ?v_0 (f86 (f87 f88 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_0 (f33 f76 ?v0))) (= (f32 (f33 f76 (f32 ?v_0 ?v1)) ?v2) (f32 ?v_0 (f32 (f33 f76 ?v1) ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_0 (f29 f46 ?v0))) (= (f28 (f29 f46 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f46 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f36 f73 ?v0))) (= (f35 (f36 f73 (f35 ?v_0 ?v1)) ?v2) (f35 ?v_0 (f35 (f36 f73 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f87 f88 ?v0))) (= (= (f86 (f87 f88 (f86 ?v_0 ?v1)) ?v2) f1) (= (f86 ?v_0 (f86 (f87 f88 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_0 (f33 f76 ?v0))) (= (f32 (f33 f76 (f32 ?v_0 ?v1)) ?v2) (f32 ?v_0 (f32 (f33 f76 ?v1) ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_1 (f29 f46 ?v0)) (?v_0 (f29 f46 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f36 f73 ?v0)) (?v_0 (f36 f73 ?v1))) (= (f35 ?v_1 (f35 ?v_0 ?v2)) (f35 ?v_0 (f35 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (= (f86 ?v_1 (f86 ?v_0 ?v2)) f1) (= (f86 ?v_0 (f86 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_1 (f33 f76 ?v0)) (?v_0 (f33 f76 ?v1))) (= (f32 ?v_1 (f32 ?v_0 ?v2)) (f32 ?v_0 (f32 ?v_1 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_1 (f29 f46 ?v0)) (?v_0 (f29 f46 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f36 f73 ?v0)) (?v_0 (f36 f73 ?v1))) (= (f35 ?v_1 (f35 ?v_0 ?v2)) (f35 ?v_0 (f35 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (= (f86 ?v_1 (f86 ?v_0 ?v2)) f1) (= (f86 ?v_0 (f86 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_1 (f33 f76 ?v0)) (?v_0 (f33 f76 ?v1))) (= (f32 ?v_1 (f32 ?v_0 ?v2)) (f32 ?v_0 (f32 ?v_1 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_1 (f29 f46 ?v0)) (?v_0 (f29 f46 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f36 f73 ?v0)) (?v_0 (f36 f73 ?v1))) (= (f35 ?v_1 (f35 ?v_0 ?v2)) (f35 ?v_0 (f35 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (= (f86 ?v_1 (f86 ?v_0 ?v2)) f1) (= (f86 ?v_0 (f86 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_1 (f33 f76 ?v0)) (?v_0 (f33 f76 ?v1))) (= (f32 ?v_1 (f32 ?v_0 ?v2)) (f32 ?v_0 (f32 ?v_1 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21)) (let ((?v_0 (f29 f46 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f36 f73 ?v0))) (let ((?v_1 (f35 ?v_0 ?v1))) (= (f35 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f87 f88 ?v0))) (let ((?v_1 (f86 ?v_0 ?v1))) (= (= (f86 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S24) (?v1 S24)) (let ((?v_0 (f33 f76 ?v0))) (let ((?v_1 (f32 ?v_0 ?v1))) (= (f32 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S21) (?v1 S21)) (let ((?v_0 (f29 f46 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f36 f73 ?v0))) (let ((?v_1 (f35 ?v_0 ?v1))) (= (f35 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f87 f88 ?v0))) (let ((?v_1 (f86 ?v_0 ?v1))) (= (= (f86 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S24) (?v1 S24)) (let ((?v_0 (f33 f76 ?v0))) (let ((?v_1 (f32 ?v_0 ?v1))) (= (f32 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S21) (?v1 S21)) (let ((?v_0 (f29 f46 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f36 f73 ?v0))) (let ((?v_1 (f35 ?v_0 ?v1))) (= (f35 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f87 f88 ?v0))) (let ((?v_1 (f86 ?v_0 ?v1))) (= (= (f86 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S24) (?v1 S24)) (let ((?v_0 (f33 f76 ?v0))) (let ((?v_1 (f32 ?v_0 ?v1))) (= (f32 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (f28 (f29 f46 ?v0) ?v1) (f28 (f29 f46 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f35 (f36 f73 ?v0) ?v1) (f35 (f36 f73 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f86 (f87 f88 ?v0) ?v1) f1) (= (f86 (f87 f88 ?v1) ?v0) f1))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (f32 (f33 f76 ?v0) ?v1) (f32 (f33 f76 ?v1) ?v0))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (f28 (f29 f46 ?v0) ?v1) (f28 (f29 f46 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f35 (f36 f73 ?v0) ?v1) (f35 (f36 f73 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f86 (f87 f88 ?v0) ?v1) f1) (= (f86 (f87 f88 ?v1) ?v0) f1))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (f32 (f33 f76 ?v0) ?v1) (f32 (f33 f76 ?v1) ?v0))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (f28 (f29 f46 ?v0) ?v1) (f28 (f29 f46 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f35 (f36 f73 ?v0) ?v1) (f35 (f36 f73 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f86 (f87 f88 ?v0) ?v1) f1) (= (f86 (f87 f88 ?v1) ?v0) f1))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (f32 (f33 f76 ?v0) ?v1) (f32 (f33 f76 ?v1) ?v0))))
(assert (forall ((?v0 S21)) (= (f28 (f29 f46 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f35 (f36 f73 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f86 (f87 f88 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S24)) (= (f32 (f33 f76 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S21)) (= (f28 (f29 f46 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f35 (f36 f73 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f86 (f87 f88 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S24)) (= (f32 (f33 f76 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f89 f90 (f16 f17 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f16 f17 (f89 f90 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f16 f17 (f89 f90 ?v0)) 0))))
(check-sat)
(exit)

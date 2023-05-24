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
(declare-sort S58 0)
(declare-sort S59 0)
(declare-sort S60 0)
(declare-sort S61 0)
(declare-sort S62 0)
(declare-sort S63 0)
(declare-sort S64 0)
(declare-sort S65 0)
(declare-sort S66 0)
(declare-sort S67 0)
(declare-sort S68 0)
(declare-sort S69 0)
(declare-sort S70 0)
(declare-sort S71 0)
(declare-sort S72 0)
(declare-sort S73 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S2) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S3) S4)
(declare-fun f7 () S5)
(declare-fun f8 () S2)
(declare-fun f9 (S6 S7) S1)
(declare-fun f10 (S8 S6) S6)
(declare-fun f11 () S8)
(declare-fun f12 (S9 S7) S8)
(declare-fun f13 () S9)
(declare-fun f14 () S6)
(declare-fun f15 (S10 S3) S2)
(declare-fun f16 () S10)
(declare-fun f17 (S12 S11) S1)
(declare-fun f18 (S13 S11) S12)
(declare-fun f19 () S13)
(declare-fun f20 (S14 S7) S6)
(declare-fun f21 () S14)
(declare-fun f22 () S10)
(declare-fun f23 () S14)
(declare-fun f24 (S16 S7) S2)
(declare-fun f25 (S17 S15) S16)
(declare-fun f26 () S17)
(declare-fun f27 (S15 S3) S6)
(declare-fun f28 (S18 S16) S15)
(declare-fun f29 () S18)
(declare-fun f30 (S19 S14) S14)
(declare-fun f31 () S19)
(declare-fun f32 () S5)
(declare-fun f33 (S20 S2) S1)
(declare-fun f34 (S21 S3) S20)
(declare-fun f35 () S21)
(declare-fun f36 () S9)
(declare-fun f37 (S22 S6) S1)
(declare-fun f38 (S23 S7) S22)
(declare-fun f39 () S23)
(declare-fun f40 () S5)
(declare-fun f41 () S9)
(declare-fun f42 () S5)
(declare-fun f43 () S9)
(declare-fun f44 (S24 S2) S4)
(declare-fun f45 () S24)
(declare-fun f46 (S25 S6) S8)
(declare-fun f47 () S25)
(declare-fun f48 () S24)
(declare-fun f49 () S25)
(declare-fun f50 () S24)
(declare-fun f51 () S25)
(declare-fun f52 () S5)
(declare-fun f53 () S9)
(declare-fun f54 (S26 S11) S13)
(declare-fun f55 () S26)
(declare-fun f56 (S27 S13) S26)
(declare-fun f57 () S27)
(declare-fun f58 (S29 S28) S13)
(declare-fun f59 () S29)
(declare-fun f60 () S29)
(declare-fun f61 (S30 S16) S6)
(declare-fun f62 (S31 S2) S30)
(declare-fun f63 () S31)
(declare-fun f64 (S32 S15) S2)
(declare-fun f65 (S33 S6) S32)
(declare-fun f66 () S33)
(declare-fun f67 (S34 S14) S6)
(declare-fun f68 (S35 S6) S34)
(declare-fun f69 () S35)
(declare-fun f70 (S36 S12) S13)
(declare-fun f71 (S37 S13) S36)
(declare-fun f72 () S37)
(declare-fun f73 (S38 S13) S13)
(declare-fun f74 (S39 S1) S38)
(declare-fun f75 () S39)
(declare-fun f76 (S40 S3) S10)
(declare-fun f77 (S41 S1) S40)
(declare-fun f78 () S41)
(declare-fun f79 (S42 S7) S14)
(declare-fun f80 (S43 S1) S42)
(declare-fun f81 () S43)
(declare-fun f82 () S2)
(declare-fun f83 () S6)
(declare-fun f84 (S44 S2) S20)
(declare-fun f85 () S44)
(declare-fun f86 () S2)
(declare-fun f87 (S45 S28) S3)
(declare-fun f88 () S45)
(declare-fun f89 () S28)
(declare-fun f90 () S1)
(declare-fun f91 (S46 S47) S6)
(declare-fun f92 () S46)
(declare-fun f93 () S47)
(declare-fun f94 (S48 S7) S28)
(declare-fun f95 () S48)
(declare-fun f96 () S4)
(declare-fun f97 () S8)
(declare-fun f98 (S49 S2) S3)
(declare-fun f99 () S49)
(declare-fun f100 (S50 S6) S7)
(declare-fun f101 () S50)
(declare-fun f102 () S1)
(declare-fun f103 (S51 S13) S3)
(declare-fun f104 (S52 S28) S51)
(declare-fun f105 (S53 S13) S52)
(declare-fun f106 () S53)
(declare-fun f107 () S22)
(declare-fun f108 () S44)
(declare-fun f109 () S20)
(declare-fun f110 (S54 S55) S28)
(declare-fun f111 () S54)
(declare-fun f112 (S47 S7) S55)
(declare-fun f113 (S57 S56) S2)
(declare-fun f114 () S57)
(declare-fun f115 (S58 Int) S56)
(declare-fun f116 () S58)
(declare-fun f117 (S59 S56) Int)
(declare-fun f118 () S59)
(declare-fun f119 (S61 S3) S56)
(declare-fun f120 (S62 S60) S61)
(declare-fun f121 () S62)
(declare-fun f122 (S64 S49) S1)
(declare-fun f123 (S65 S63) S64)
(declare-fun f124 () S65)
(declare-fun f125 (S66 S3) S3)
(declare-fun f126 (S63 S3) S66)
(declare-fun f127 (S68 S50) S1)
(declare-fun f128 (S69 S67) S68)
(declare-fun f129 () S69)
(declare-fun f130 (S70 S7) S7)
(declare-fun f131 (S67 S7) S70)
(declare-fun f132 (S71 S28) S28)
(declare-fun f133 (S72 S12) S71)
(declare-fun f134 () S72)
(declare-fun f135 (S73 S28) S71)
(declare-fun f136 () S73)
(declare-fun f137 () S49)
(declare-fun f138 () S50)
(declare-fun f139 () S65)
(declare-fun f140 () S69)
(declare-fun f141 () S61)
(declare-fun f142 () S24)
(declare-fun f143 () S25)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 (f4 (f6 f7 ?v1) f8)))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f9 (f10 f11 ?v0) ?v1) f1) (= ?v0 (f10 (f12 f13 ?v1) f14)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f15 f16 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f17 (f18 f19 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f9 (f20 f21 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f15 f22 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f9 (f20 f23 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S15) (?v1 S7) (?v2 S3)) (= (= (f3 (f24 (f25 f26 ?v0) ?v1) ?v2) f1) (= (f9 (f27 ?v0 ?v2) ?v1) f1))))
(assert (forall ((?v0 S16) (?v1 S3) (?v2 S7)) (= (= (f9 (f27 (f28 f29 ?v0) ?v1) ?v2) f1) (= (f3 (f24 ?v0 ?v2) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S7) (?v2 S7)) (= (= (f9 (f20 (f30 f31 ?v0) ?v1) ?v2) f1) (= (f9 (f20 ?v0 ?v2) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f32 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f33 (f34 f35 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (= (= (f9 (f10 (f12 f36 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f37 (f38 f39 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f40 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (= (= (f9 (f10 (f12 f41 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f9 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f42 ?v0) ?v1) ?v2) f1) (and (= ?v2 ?v0) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (= (= (f9 (f10 (f12 f43 ?v0) ?v1) ?v2) f1) (and (= ?v2 ?v0) (= (f9 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f34 f35 ?v2))) (= (= (f3 (f4 (f44 f45 ?v0) ?v1) ?v2) f1) (and (= (f33 ?v_0 ?v0) f1) (not (= (f33 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (let ((?v_0 (f38 f39 ?v2))) (= (= (f9 (f10 (f46 f47 ?v0) ?v1) ?v2) f1) (and (= (f37 ?v_0 ?v0) f1) (not (= (f37 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f44 f48 ?v0) ?v1) ?v2) f1) (or (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (= (= (f9 (f10 (f46 f49 ?v0) ?v1) ?v2) f1) (or (= (f9 ?v0 ?v2) f1) (= (f9 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f44 f50 ?v0) ?v1) ?v2) f1) (and (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (= (= (f9 (f10 (f46 f51 ?v0) ?v1) ?v2) f1) (and (= (f9 ?v0 ?v2) f1) (= (f9 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f52 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (= (= (f9 (f10 (f12 f53 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f9 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (= (= (f17 (f18 (f54 f55 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S13) (?v1 S11) (?v2 S11)) (= (f18 (f54 (f56 f57 ?v0) ?v1) ?v2) (f18 ?v0 ?v1))))
(assert (forall ((?v0 S28) (?v1 S11) (?v2 S11)) (= (= (f17 (f18 (f58 f59 ?v0) ?v1) ?v2) f1) (forall ((?v3 S11)) (=> (= (f17 (f18 (f58 f60 ?v0) ?v2) ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S16) (?v2 S7)) (= (= (f9 (f61 (f62 f63 ?v0) ?v1) ?v2) f1) (exists ((?v3 S3)) (and (= (f33 (f34 f35 ?v3) ?v0) f1) (= (f3 (f24 ?v1 ?v2) ?v3) f1))))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S3)) (= (= (f3 (f64 (f65 f66 ?v0) ?v1) ?v2) f1) (exists ((?v3 S7)) (and (= (f37 (f38 f39 ?v3) ?v0) f1) (= (f9 (f27 ?v1 ?v2) ?v3) f1))))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S7)) (= (= (f9 (f67 (f68 f69 ?v0) ?v1) ?v2) f1) (exists ((?v3 S7)) (and (= (f37 (f38 f39 ?v3) ?v0) f1) (= (f9 (f20 ?v1 ?v2) ?v3) f1))))))
(assert (forall ((?v0 S13) (?v1 S12) (?v2 S11) (?v3 S11)) (= (= (f17 (f18 (f70 (f71 f72 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f17 (f18 ?v0 ?v2) ?v3) f1) (not (= (f17 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S13) (?v2 S11) (?v3 S11)) (= (= (f17 (f18 (f73 (f74 f75 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f17 (f18 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S1) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (= ?v0 f1))) (= (= (f3 (f15 (f76 (f77 f78 ?v0) ?v1) ?v2) ?v3) f1) (and (=> (= ?v_0 true) (= ?v3 ?v1)) (=> (= ?v_0 false) (= ?v3 ?v2)))))))
(assert (forall ((?v0 S1) (?v1 S7) (?v2 S7) (?v3 S7)) (let ((?v_0 (= ?v0 f1))) (= (= (f9 (f20 (f79 (f80 f81 ?v0) ?v1) ?v2) ?v3) f1) (and (=> (= ?v_0 true) (= ?v3 ?v1)) (=> (= ?v_0 false) (= ?v3 ?v2)))))))
(assert (forall ((?v0 S3)) (= (= (f3 f82 ?v0) f1) false)))
(assert (forall ((?v0 S7)) (= (= (f9 f83 ?v0) f1) false)))
(assert (not (= (f33 (f84 f85 f86) (f4 (f6 f7 (f87 f88 f89)) f8)) f1)))
(assert (= f90 f1))
(assert (forall ((?v0 S7)) (=> (= (f37 (f38 f39 ?v0) (f91 f92 f93)) f1) (= (f33 (f84 f85 f86) (f4 (f6 f7 (f87 f88 (f94 f95 ?v0))) f8)) f1))))
(assert (forall ((?v0 S2)) (= (f33 (f84 f85 ?v0) f8) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f84 f85 ?v2))) (=> (= (f33 (f84 f85 ?v0) ?v1) f1) (=> (= (f33 ?v_0 ?v0) f1) (= (f33 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f84 f85 ?v0)) (?v_1 (f6 f7 ?v1))) (=> (= (f33 ?v_0 (f4 ?v_1 f8)) f1) (=> (= (f33 ?v_0 ?v2) f1) (= (f33 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f84 f85 ?v0)) (?v_1 (f6 f7 ?v1))) (=> (= (f33 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f33 ?v_0 (f4 ?v_1 f8)) f1) (= (f33 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f33 ?v_0 (f4 (f6 f7 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f33 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f37 ?v_0 (f10 (f12 f13 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f37 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f34 f35 ?v0))) (=> (=> (not (= (f33 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f33 ?v_0 (f4 (f6 f7 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (let ((?v_0 (f38 f39 ?v0))) (=> (=> (not (= (f37 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f37 ?v_0 (f10 (f12 f13 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S7)) (=> (= (f37 (f38 f39 ?v0) f14) f1) false)))
(assert (forall ((?v0 S3)) (=> (= (f33 (f34 f35 ?v0) f8) f1) false)))
(assert (forall ((?v0 S3)) (= (f4 f96 (f15 f16 ?v0)) (f4 (f6 f7 ?v0) f8))))
(assert (forall ((?v0 S7)) (= (f10 f97 (f20 f21 ?v0)) (f10 (f12 f13 ?v0) f14))))
(assert (forall ((?v0 S3)) (= (f4 f96 (f15 f22 ?v0)) (f4 (f6 f7 ?v0) f8))))
(assert (forall ((?v0 S7)) (= (f10 f97 (f20 f23 ?v0)) (f10 (f12 f13 ?v0) f14))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 f96 (f4 (f6 f40 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f4 (f6 f7 ?v0) f8) f8))))
(assert (forall ((?v0 S7) (?v1 S6)) (= (f10 f97 (f10 (f12 f41 ?v0) ?v1)) (ite (= (f9 ?v1 ?v0) f1) (f10 (f12 f13 ?v0) f14) f14))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 f96 (f4 (f6 f42 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f4 (f6 f7 ?v0) f8) f8))))
(assert (forall ((?v0 S7) (?v1 S6)) (= (f10 f97 (f10 (f12 f43 ?v0) ?v1)) (ite (= (f9 ?v1 ?v0) f1) (f10 (f12 f13 ?v0) f14) f14))))
(assert (forall ((?v0 S7)) (not (= f89 (f94 f95 ?v0)))))
(assert (forall ((?v0 S7)) (not (= (f94 f95 ?v0) f89))))
(assert (= (= f90 f1) (exists ((?v0 S11) (?v1 S11)) (not (= ?v0 ?v1)))))
(assert (=> (= f90 f1) (forall ((?v0 S11)) (=> (forall ((?v1 S11)) (= ?v1 ?v0)) false))))
(assert (forall ((?v0 S3) (?v1 S2)) (not (= f8 (f4 (f6 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S6)) (not (= f14 (f10 (f12 f13 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= ?v0 f14) (not (= (f37 (f38 f39 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= ?v0 f8) (not (= (f33 (f34 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f4 f96 ?v0) f8) (forall ((?v1 S3)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (= (f10 f97 ?v0) f14) (forall ((?v1 S7)) (not (= (f9 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (= (f37 (f38 f39 ?v0) f14) f1) false)))
(assert (forall ((?v0 S3)) (= (= (f33 (f34 f35 ?v0) f8) f1) false)))
(assert (forall ((?v0 S2)) (= (= f8 (f4 f96 ?v0)) (forall ((?v1 S3)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (= f14 (f10 f97 ?v0)) (forall ((?v1 S7)) (not (= (f9 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (forall ((?v1 S7)) (=> (= (f37 (f38 f39 ?v1) f14) f1) (= (f9 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (=> (= (f33 (f34 f35 ?v1) f8) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S6)) (= (exists ((?v1 S7)) (and (= (f37 (f38 f39 ?v1) f14) f1) (= (f9 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S3)) (and (= (f33 (f34 f35 ?v1) f8) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S6)) (= (exists ((?v1 S7)) (= (f37 (f38 f39 ?v1) ?v0) f1)) (not (= ?v0 f14)))))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S3)) (= (f33 (f34 f35 ?v1) ?v0) f1)) (not (= ?v0 f8)))))
(assert (forall ((?v0 S6)) (= (forall ((?v1 S7)) (not (= (f37 (f38 f39 ?v1) ?v0) f1))) (= ?v0 f14))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (not (= (f33 (f34 f35 ?v1) ?v0) f1))) (= ?v0 f8))))
(assert (= f8 (f4 f96 f82)))
(assert (= f14 (f10 f97 f83)))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f33 (f34 f35 ?v0) ?v1) f1) (= (f4 (f6 f7 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= (f37 (f38 f39 ?v0) ?v1) f1) (= (f10 (f12 f13 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f33 ?v_0 ?v1) f1) (= (f33 ?v_0 (f4 (f6 f7 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f37 ?v_0 ?v1) f1) (= (f37 ?v_0 (f10 (f12 f13 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f34 f35 ?v0)) (?v_1 (f6 f7 ?v0))) (=> (not (= (f33 ?v_0 ?v1) f1)) (=> (not (= (f33 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0)) (?v_1 (f12 f13 ?v0))) (=> (not (= (f37 ?v_0 ?v1) f1)) (=> (not (= (f37 ?v_0 ?v2) f1)) (= (= (f10 ?v_1 ?v1) (f10 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f7 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (= (= (f9 (f10 (f12 f13 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f9 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f34 f35 ?v0))) (= (= (f33 ?v_0 (f4 (f6 f7 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f33 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (= (= (f37 ?v_0 (f10 (f12 f13 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f37 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_1 (f6 f7 ?v0)) (?v_0 (f6 f7 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S6)) (let ((?v_1 (f12 f13 ?v0)) (?v_0 (f12 f13 ?v1))) (= (f10 ?v_1 (f10 ?v_0 ?v2)) (f10 ?v_0 (f10 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2)) (let ((?v_0 (f6 f7 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S7) (?v1 S6)) (let ((?v_0 (f12 f13 ?v0))) (let ((?v_1 (f10 ?v_0 ?v1))) (= (f10 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 (f6 f7 ?v0) (f4 f96 ?v1)) (f4 f96 (f4 (f6 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S6)) (= (f10 (f12 f13 ?v0) (f10 f97 ?v1)) (f10 f97 (f10 (f12 f53 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 (f6 f7 ?v0) ?v1) (f4 f96 (f4 (f6 f32 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S6)) (= (f10 (f12 f13 ?v0) ?v1) (f10 f97 (f10 (f12 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f33 (f34 f35 ?v0) (f4 (f6 f7 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S7) (?v1 S6)) (= (f37 (f38 f39 ?v0) (f10 (f12 f13 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f94 f95 ?v0) (f94 f95 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 (f6 f7 ?v0) ?v1) (f4 f96 (f4 (f6 f32 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S6)) (= (f10 (f12 f13 ?v0) ?v1) (f10 f97 (f10 (f12 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f4 (f6 f7 ?v0) f8) (f4 (f6 f7 ?v1) f8)) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f10 (f12 f13 ?v0) f14) (f10 (f12 f13 ?v1) f14)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f33 (f34 f35 ?v0) (f4 (f6 f7 ?v1) f8)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f37 (f38 f39 ?v0) (f10 (f12 f13 ?v1) f14)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f4 (f6 f7 ?v0) (f4 (f6 f7 ?v1) f8)) (f4 (f6 f7 ?v2) (f4 (f6 f7 ?v3) f8))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (= (f10 (f12 f13 ?v0) (f10 (f12 f13 ?v1) f14)) (f10 (f12 f13 ?v2) (f10 (f12 f13 ?v3) f14))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f33 (f34 f35 ?v0) (f4 (f6 f7 ?v1) f8)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f37 (f38 f39 ?v0) (f10 (f12 f13 ?v1) f14)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (not (= (f4 (f6 f7 ?v0) ?v1) f8))))
(assert (forall ((?v0 S7) (?v1 S6)) (not (= (f10 (f12 f13 ?v0) ?v1) f14))))
(assert (forall ((?v0 S3)) (= (f98 f99 (f4 (f6 f7 ?v0) f8)) ?v0)))
(assert (forall ((?v0 S7)) (= (f100 f101 (f10 (f12 f13 ?v0) f14)) ?v0)))
(assert (forall ((?v0 S3)) (= (= (f3 f8 ?v0) f1) (= f102 f1))))
(assert (forall ((?v0 S7)) (= (= (f9 f14 ?v0) f1) (= f102 f1))))
(assert (forall ((?v0 S3)) (= (= (f3 f8 ?v0) f1) (= f102 f1))))
(assert (forall ((?v0 S7)) (= (= (f9 f14 ?v0) f1) (= f102 f1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f33 (f34 f35 ?v0) ?v1) f1) (=> (forall ((?v2 S2)) (=> (= ?v1 (f4 (f6 f7 ?v0) ?v2)) (=> (not (= (f33 (f34 f35 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= (f37 (f38 f39 ?v0) ?v1) f1) (=> (forall ((?v2 S6)) (=> (= ?v1 (f10 (f12 f13 ?v0) ?v2)) (=> (not (= (f37 (f38 f39 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f33 (f34 f35 ?v0) ?v1) f1) (exists ((?v2 S2)) (and (= ?v1 (f4 (f6 f7 ?v0) ?v2)) (not (= (f33 (f34 f35 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= (f37 (f38 f39 ?v0) ?v1) f1) (exists ((?v2 S6)) (and (= ?v1 (f10 (f12 f13 ?v0) ?v2)) (not (= (f37 (f38 f39 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S7)) (=> (= (f37 (f38 f39 ?v1) ?v0) f1) false)) (= ?v0 f14))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S3)) (=> (= (f33 (f34 f35 ?v1) ?v0) f1) false)) (= ?v0 f8))))
(assert (forall ((?v0 S2) (?v1 S13)) (= (f33 (f84 f85 ?v0) (f4 (f6 f7 (f103 (f104 (f105 f106 ?v1) f89) ?v1)) f8)) f1)))
(assert (= (f37 f107 (f91 f92 f93)) f1))
(assert (forall ((?v0 S28) (?v1 S13) (?v2 S13)) (let ((?v_0 (f84 f85 f8)) (?v_1 (f4 (f6 f7 (f103 (f104 (f105 f106 ?v1) ?v0) ?v2)) f8))) (=> (= (f33 ?v_0 (f4 (f6 f7 (f87 f88 ?v0)) f8)) f1) (=> (= (f33 (f84 f108 f8) ?v_1) f1) (= (f33 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S1) (?v1 S2) (?v2 S13) (?v3 S28) (?v4 S13)) (let ((?v_0 (f84 f85 ?v1))) (=> (=> (= ?v0 f1) (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 ?v2) ?v3) ?v4)) f8)) f1)) (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 (f73 (f74 f75 ?v0) ?v2)) ?v3) ?v4)) f8)) f1)))))
(assert (forall ((?v0 S13) (?v1 S28) (?v2 S13) (?v3 S13) (?v4 S28) (?v5 S13)) (= (= (f103 (f104 (f105 f106 ?v0) ?v1) ?v2) (f103 (f104 (f105 f106 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f33 (f84 f85 ?v0) ?v1) f1) (= (f33 (f84 f108 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S2) (?v2 S28) (?v3 S13)) (=> (forall ((?v4 S11) (?v5 S11)) (=> (= (f17 (f18 ?v0 ?v4) ?v5) f1) (= (f33 (f84 f85 ?v1) (f4 (f6 f7 (f103 (f104 (f105 f106 (f54 f55 ?v5)) ?v2) (f54 (f56 f57 ?v3) ?v4))) f8)) f1))) (= (f33 (f84 f85 ?v1) (f4 (f6 f7 (f103 (f104 (f105 f106 ?v0) ?v2) ?v3)) f8)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f33 f109 ?v0) f1) (= (f33 f109 (f4 (f6 f7 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f37 f107 ?v0) f1) (= (f37 f107 (f10 (f12 f13 ?v1) ?v0)) f1))))
(assert (= (f37 f107 f14) f1))
(assert (= (f33 f109 f8) f1))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S28) (?v3 S13) (?v4 S13)) (let ((?v_0 (f84 f85 ?v0)) (?v_1 (f104 (f105 f106 ?v1) ?v2))) (=> (= (f33 ?v_0 (f4 (f6 f7 (f103 ?v_1 ?v3)) f8)) f1) (=> (forall ((?v5 S11) (?v6 S11)) (=> (= (f17 (f18 ?v3 ?v5) ?v6) f1) (= (f17 (f18 ?v4 ?v5) ?v6) f1))) (= (f33 ?v_0 (f4 (f6 f7 (f103 ?v_1 ?v4)) f8)) f1))))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S28) (?v3 S13) (?v4 S13)) (let ((?v_0 (f84 f85 ?v0))) (=> (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 ?v1) ?v2) ?v3)) f8)) f1) (=> (forall ((?v5 S11) (?v6 S11)) (=> (= (f17 (f18 ?v4 ?v5) ?v6) f1) (= (f17 (f18 ?v1 ?v5) ?v6) f1))) (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 ?v4) ?v2) ?v3)) f8)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (or (= (f37 f107 (f10 f97 ?v0)) f1) (= (f37 f107 (f10 f97 ?v1)) f1)) (= (f37 f107 (f10 f97 (f10 (f46 f51 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (or (= (f33 f109 (f4 f96 ?v0)) f1) (= (f33 f109 (f4 f96 ?v1)) f1)) (= (f33 f109 (f4 f96 (f4 (f44 f50 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S7) (?v3 S13)) (let ((?v_0 (f84 f85 ?v0)) (?v_1 (f105 f106 ?v1))) (=> (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 ?v_1 (f110 f111 (f112 f93 ?v2))) ?v3)) f8)) f1) (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 ?v_1 (f94 f95 ?v2)) ?v3)) f8)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f37 f107 (f10 f97 (f10 (f46 f49 ?v0) ?v1))) f1) (and (= (f37 f107 (f10 f97 ?v0)) f1) (= (f37 f107 (f10 f97 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f33 f109 (f4 f96 (f4 (f44 f48 ?v0) ?v1))) f1) (and (= (f33 f109 (f4 f96 ?v0)) f1) (= (f33 f109 (f4 f96 ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S15)) (=> (= (f37 f107 ?v0) f1) (= (= (f33 f109 (f4 f96 (f64 (f65 f66 ?v0) ?v1))) f1) (forall ((?v2 S7)) (=> (= (f37 (f38 f39 ?v2) ?v0) f1) (= (f33 f109 (f4 f96 (f24 (f25 f26 ?v1) ?v2))) f1)))))))
(assert (forall ((?v0 S6) (?v1 S14)) (=> (= (f37 f107 ?v0) f1) (= (= (f37 f107 (f10 f97 (f67 (f68 f69 ?v0) ?v1))) f1) (forall ((?v2 S7)) (=> (= (f37 (f38 f39 ?v2) ?v0) f1) (= (f37 f107 (f10 f97 (f20 (f30 f31 ?v1) ?v2))) f1)))))))
(assert (forall ((?v0 S2) (?v1 S16)) (=> (= (f33 f109 ?v0) f1) (= (= (f37 f107 (f10 f97 (f61 (f62 f63 ?v0) ?v1))) f1) (forall ((?v2 S3)) (=> (= (f33 (f34 f35 ?v2) ?v0) f1) (= (f37 f107 (f10 f97 (f27 (f28 f29 ?v1) ?v2))) f1)))))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f33 f109 (f4 (f6 f7 ?v0) ?v1)) f1) (= (f33 f109 ?v1) f1))))
(assert (forall ((?v0 S7) (?v1 S6)) (= (= (f37 f107 (f10 (f12 f13 ?v0) ?v1)) f1) (= (f37 f107 ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S7) (?v2 S13) (?v3 S2)) (let ((?v_0 (f105 f106 ?v0))) (let ((?v_1 (f6 f7 (f103 (f104 ?v_0 (f94 f95 ?v1)) ?v2)))) (=> (= (f33 (f84 f85 (f4 ?v_1 ?v3)) (f4 (f6 f7 (f103 (f104 ?v_0 (f110 f111 (f112 f93 ?v1))) ?v2)) f8)) f1) (= (f33 (f84 f85 ?v3) (f4 ?v_1 f8)) f1))))))
(assert (forall ((?v0 S2) (?v1 S20)) (=> (= (f33 f109 ?v0) f1) (=> (= (f33 ?v1 f8) f1) (=> (forall ((?v2 S3) (?v3 S2)) (=> (= (f33 f109 ?v3) f1) (=> (not (= (f33 (f34 f35 ?v2) ?v3) f1)) (=> (= (f33 ?v1 ?v3) f1) (= (f33 ?v1 (f4 (f6 f7 ?v2) ?v3)) f1))))) (= (f33 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S6) (?v1 S22)) (=> (= (f37 f107 ?v0) f1) (=> (= (f37 ?v1 f14) f1) (=> (forall ((?v2 S7) (?v3 S6)) (=> (= (f37 f107 ?v3) f1) (=> (not (= (f37 (f38 f39 ?v2) ?v3) f1)) (=> (= (f37 ?v1 ?v3) f1) (= (f37 ?v1 (f10 (f12 f13 ?v2) ?v3)) f1))))) (= (f37 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S2)) (= (= (f33 f109 ?v0) f1) (or (= ?v0 f8) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f6 f7 ?v2) ?v1)) (= (f33 f109 ?v1) f1)))))))
(assert (forall ((?v0 S6)) (= (= (f37 f107 ?v0) f1) (or (= ?v0 f14) (exists ((?v1 S6) (?v2 S7)) (and (= ?v0 (f10 (f12 f13 ?v2) ?v1)) (= (f37 f107 ?v1) f1)))))))
(assert (forall ((?v0 S56) (?v1 S13) (?v2 S7) (?v3 S13)) (let ((?v_0 (f105 f106 ?v1))) (= (= (f3 (f113 f114 ?v0) (f103 (f104 ?v_0 (f110 f111 (f112 f93 ?v2))) ?v3)) f1) (= (f3 (f113 f114 (f115 f116 (+ (f117 f118 ?v0) 1))) (f103 (f104 ?v_0 (f94 f95 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S28) (?v3 S13) (?v4 S13) (?v5 S13)) (let ((?v_0 (f84 f85 ?v0))) (=> (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 ?v1) ?v2) ?v3)) f8)) f1) (=> (forall ((?v6 S11) (?v7 S11)) (=> (= (f17 (f18 ?v4 ?v6) ?v7) f1) (forall ((?v8 S11)) (=> (forall ((?v9 S11)) (=> (= (f17 (f18 ?v1 ?v9) ?v7) f1) (= (f17 (f18 ?v3 ?v9) ?v8) f1))) (= (f17 (f18 ?v5 ?v6) ?v8) f1))))) (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 ?v4) ?v2) ?v5)) f8)) f1))))))
(assert (forall ((?v0 S60) (?v1 S13) (?v2 S28) (?v3 S13)) (= (f119 (f120 f121 ?v0) (f103 (f104 (f105 f106 ?v1) ?v2) ?v3)) (f115 f116 0))))
(assert (forall ((?v0 S2)) (= (not (= ?v0 f8)) (exists ((?v1 S3) (?v2 S2)) (and (= ?v0 (f4 (f6 f7 ?v1) ?v2)) (not (= (f33 (f34 f35 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S6)) (= (not (= ?v0 f14)) (exists ((?v1 S7) (?v2 S6)) (and (= ?v0 (f10 (f12 f13 ?v1) ?v2)) (not (= (f37 (f38 f39 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S56) (?v1 S3)) (=> (= (f3 (f113 f114 (f115 f116 (+ (f117 f118 ?v0) 1))) ?v1) f1) (= (f3 (f113 f114 ?v0) ?v1) f1))))
(assert (forall ((?v0 S7) (?v1 S6)) (= (= (f37 (f38 f39 ?v0) ?v1) f1) (= (f9 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f33 (f34 f35 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (f4 f96 ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 f97 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S56)) (=> (forall ((?v2 S3)) (=> (= (f33 (f34 f35 ?v2) ?v0) f1) (= (f3 (f113 f114 (f115 f116 (+ (f117 f118 ?v1) 1))) ?v2) f1))) (forall ((?v2 S3)) (=> (= (f33 (f34 f35 ?v2) ?v0) f1) (= (f3 (f113 f114 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f33 (f84 f108 ?v0) ?v1) f1) (forall ((?v2 S56)) (=> (forall ((?v3 S3)) (=> (= (f33 (f34 f35 ?v3) ?v0) f1) (= (f3 (f113 f114 ?v2) ?v3) f1))) (forall ((?v3 S3)) (=> (= (f33 (f34 f35 ?v3) ?v1) f1) (= (f3 (f113 f114 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S13) (?v1 S7) (?v2 S13)) (= (f3 (f113 f114 (f115 f116 0)) (f103 (f104 (f105 f106 ?v0) (f94 f95 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S2) (?v3 S3)) (=> (= (f122 (f123 f124 ?v0) ?v1) f1) (=> (= (f33 f109 ?v2) f1) (=> (not (= ?v2 f8)) (= (f98 ?v1 (f4 (f6 f7 ?v3) ?v2)) (f125 (f126 ?v0 ?v3) (f98 ?v1 ?v2))))))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S6) (?v3 S7)) (=> (= (f127 (f128 f129 ?v0) ?v1) f1) (=> (= (f37 f107 ?v2) f1) (=> (not (= ?v2 f14)) (= (f100 ?v1 (f10 (f12 f13 ?v3) ?v2)) (f130 (f131 ?v0 ?v3) (f100 ?v1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S20)) (=> (= (f33 f109 ?v0) f1) (=> (not (= ?v0 f8)) (=> (forall ((?v2 S3)) (= (f33 ?v1 (f4 (f6 f7 ?v2) f8)) f1)) (=> (forall ((?v2 S3) (?v3 S2)) (=> (= (f33 f109 ?v3) f1) (=> (not (= ?v3 f8)) (=> (not (= (f33 (f34 f35 ?v2) ?v3) f1)) (=> (= (f33 ?v1 ?v3) f1) (= (f33 ?v1 (f4 (f6 f7 ?v2) ?v3)) f1)))))) (= (f33 ?v1 ?v0) f1)))))))
(assert (forall ((?v0 S6) (?v1 S22)) (=> (= (f37 f107 ?v0) f1) (=> (not (= ?v0 f14)) (=> (forall ((?v2 S7)) (= (f37 ?v1 (f10 (f12 f13 ?v2) f14)) f1)) (=> (forall ((?v2 S7) (?v3 S6)) (=> (= (f37 f107 ?v3) f1) (=> (not (= ?v3 f14)) (=> (not (= (f37 (f38 f39 ?v2) ?v3) f1)) (=> (= (f37 ?v1 ?v3) f1) (= (f37 ?v1 (f10 (f12 f13 ?v2) ?v3)) f1)))))) (= (f37 ?v1 ?v0) f1)))))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S12) (?v3 S28)) (= (f33 (f84 f85 ?v0) (f4 (f6 f7 (f103 (f104 (f105 f106 (f70 (f71 f72 ?v1) ?v2)) (f132 (f133 f134 ?v2) ?v3)) ?v1)) f8)) f1)))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S28) (?v3 S13) (?v4 S28) (?v5 S13)) (let ((?v_0 (f84 f85 ?v0)) (?v_1 (f105 f106 ?v1))) (=> (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 ?v_1 ?v2) ?v3)) f8)) f1) (=> (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 ?v3) ?v4) ?v5)) f8)) f1) (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 ?v_1 (f132 (f135 f136 ?v2) ?v4)) ?v5)) f8)) f1))))))
(assert (forall ((?v0 S2)) (= (f98 f99 ?v0) (f98 f137 (f4 f5 ?v0)))))
(assert (forall ((?v0 S6)) (= (f100 f101 ?v0) (f100 f138 (f10 f11 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S28) (?v2 S12) (?v3 S28)) (= (= (f132 (f133 f134 ?v0) ?v1) (f132 (f133 f134 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (= (= (f132 (f135 f136 ?v0) ?v1) (f132 (f135 f136 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S28) (?v2 S28) (?v3 S28)) (not (= (f132 (f133 f134 ?v0) ?v1) (f132 (f135 f136 ?v2) ?v3)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S12) (?v3 S28)) (not (= (f132 (f135 f136 ?v0) ?v1) (f132 (f133 f134 ?v2) ?v3)))))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S3)) (=> (= (f122 (f123 f124 ?v0) ?v1) f1) (= (f125 (f126 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S7)) (=> (= (f127 (f128 f129 ?v0) ?v1) f1) (= (f130 (f131 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S12) (?v1 S28) (?v2 S7)) (not (= (f132 (f133 f134 ?v0) ?v1) (f94 f95 ?v2)))))
(assert (forall ((?v0 S7) (?v1 S12) (?v2 S28)) (not (= (f94 f95 ?v0) (f132 (f133 f134 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S28)) (not (= (f132 (f133 f134 ?v0) ?v1) f89))))
(assert (forall ((?v0 S12) (?v1 S28)) (not (= f89 (f132 (f133 f134 ?v0) ?v1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S7)) (not (= (f132 (f135 f136 ?v0) ?v1) (f94 f95 ?v2)))))
(assert (forall ((?v0 S7) (?v1 S28) (?v2 S28)) (not (= (f94 f95 ?v0) (f132 (f135 f136 ?v1) ?v2)))))
(assert (forall ((?v0 S28) (?v1 S28)) (not (= (f132 (f135 f136 ?v0) ?v1) f89))))
(assert (forall ((?v0 S28) (?v1 S28)) (not (= f89 (f132 (f135 f136 ?v0) ?v1)))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S6) (?v3 S7)) (let ((?v_0 (f100 ?v1 ?v2))) (=> (= (f127 (f128 f129 ?v0) ?v1) f1) (=> (= (f37 f107 ?v2) f1) (=> (= (f37 (f38 f39 ?v3) ?v2) f1) (= (f130 (f131 ?v0 ?v3) ?v_0) ?v_0)))))))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S2) (?v3 S3)) (let ((?v_0 (f98 ?v1 ?v2))) (=> (= (f122 (f123 f124 ?v0) ?v1) f1) (=> (= (f33 f109 ?v2) f1) (=> (= (f33 (f34 f35 ?v3) ?v2) f1) (= (f125 (f126 ?v0 ?v3) ?v_0) ?v_0)))))))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S2) (?v3 S3)) (=> (= (f122 (f123 f139 ?v0) ?v1) f1) (=> (= (f33 f109 ?v2) f1) (=> (not (= (f33 (f34 f35 ?v3) ?v2) f1)) (=> (not (= ?v2 f8)) (= (f98 ?v1 (f4 (f6 f7 ?v3) ?v2)) (f125 (f126 ?v0 ?v3) (f98 ?v1 ?v2)))))))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S6) (?v3 S7)) (=> (= (f127 (f128 f140 ?v0) ?v1) f1) (=> (= (f37 f107 ?v2) f1) (=> (not (= (f37 (f38 f39 ?v3) ?v2) f1)) (=> (not (= ?v2 f14)) (= (f100 ?v1 (f10 (f12 f13 ?v3) ?v2)) (f130 (f131 ?v0 ?v3) (f100 ?v1 ?v2)))))))))
(assert (forall ((?v0 S7)) (= (f100 f138 (f20 f21 ?v0)) ?v0)))
(assert (forall ((?v0 S3)) (= (f98 f137 (f15 f16 ?v0)) ?v0)))
(assert (forall ((?v0 S7)) (= (f100 f138 (f20 f23 ?v0)) ?v0)))
(assert (forall ((?v0 S3)) (= (f98 f137 (f15 f22 ?v0)) ?v0)))
(assert (forall ((?v0 S1) (?v1 S7) (?v2 S7)) (= (ite (= ?v0 f1) ?v1 ?v2) (f100 f138 (f20 (f79 (f80 f81 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S1) (?v1 S3) (?v2 S3)) (= (ite (= ?v0 f1) ?v1 ?v2) (f98 f137 (f15 (f76 (f77 f78 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S28) (?v2 S13)) (= (f119 f141 (f103 (f104 (f105 f106 ?v0) ?v1) ?v2)) (f115 f116 0))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S13) (?v2 S28) (?v3 S13)) (=> (= ?v0 (f103 (f104 (f105 f106 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S3)) (=> (= (f122 (f123 f139 ?v0) ?v1) f1) (= (f98 ?v1 (f4 (f6 f7 ?v2) f8)) ?v2))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S7)) (=> (= (f127 (f128 f140 ?v0) ?v1) f1) (= (f100 ?v1 (f10 (f12 f13 ?v2) f14)) ?v2))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f9 ?v0 ?v1) f1) (=> (forall ((?v2 S7)) (=> (= (f9 ?v0 ?v2) f1) (= ?v2 ?v1))) (= (f100 f138 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f3 ?v0 ?v1) f1) (=> (forall ((?v2 S3)) (=> (= (f3 ?v0 ?v2) f1) (= ?v2 ?v1))) (= (f98 f137 ?v0) ?v1)))))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S2)) (=> (= (f122 (f123 f139 ?v0) ?v1) f1) (=> (= (f33 f109 ?v2) f1) (=> (not (= ?v2 f8)) (=> (forall ((?v3 S3) (?v4 S3)) (= (f33 (f34 f35 (f125 (f126 ?v0 ?v3) ?v4)) (f4 (f6 f7 ?v3) (f4 (f6 f7 ?v4) f8))) f1)) (= (f33 (f34 f35 (f98 ?v1 ?v2)) ?v2) f1)))))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S6)) (=> (= (f127 (f128 f140 ?v0) ?v1) f1) (=> (= (f37 f107 ?v2) f1) (=> (not (= ?v2 f14)) (=> (forall ((?v3 S7) (?v4 S7)) (= (f37 (f38 f39 (f130 (f131 ?v0 ?v3) ?v4)) (f10 (f12 f13 ?v3) (f10 (f12 f13 ?v4) f14))) f1)) (= (f37 (f38 f39 (f100 ?v1 ?v2)) ?v2) f1)))))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f9 ?v0 ?v1) f1) (=> (forall ((?v2 S7)) (=> (= (f9 ?v0 ?v2) f1) (= ?v2 ?v1))) (= (f9 ?v0 (f100 f138 ?v0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f3 ?v0 ?v1) f1) (=> (forall ((?v2 S3)) (=> (= (f3 ?v0 ?v2) f1) (= ?v2 ?v1))) (= (f3 ?v0 (f98 f137 ?v0)) f1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (exists ((?v2 S7)) (and (= (f9 ?v0 ?v2) f1) (forall ((?v3 S7)) (=> (= (f9 ?v0 ?v3) f1) (= ?v3 ?v2))))) (=> (= (f9 ?v0 ?v1) f1) (= (f100 f138 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (exists ((?v2 S3)) (and (= (f3 ?v0 ?v2) f1) (forall ((?v3 S3)) (=> (= (f3 ?v0 ?v3) f1) (= ?v3 ?v2))))) (=> (= (f3 ?v0 ?v1) f1) (= (f98 f137 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (=> (exists ((?v1 S7)) (and (= (f9 ?v0 ?v1) f1) (forall ((?v2 S7)) (=> (= (f9 ?v0 ?v2) f1) (= ?v2 ?v1))))) (= (f9 ?v0 (f100 f138 ?v0)) f1))))
(assert (forall ((?v0 S2)) (=> (exists ((?v1 S3)) (and (= (f3 ?v0 ?v1) f1) (forall ((?v2 S3)) (=> (= (f3 ?v0 ?v2) f1) (= ?v2 ?v1))))) (= (f3 ?v0 (f98 f137 ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S28)) (let ((?v_0 (f84 f85 ?v0))) (=> (= f90 f1) (=> (= (f33 ?v_0 (f4 (f6 f7 (f103 (f104 (f105 f106 (f58 f59 ?v1)) ?v1) f19)) f8)) f1) (= (f33 ?v_0 (f4 (f6 f7 (f87 f88 ?v1)) f8)) f1))))))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S2) (?v3 S3)) (let ((?v_0 (f4 (f44 f142 ?v2) (f4 (f6 f7 ?v3) f8)))) (=> (= (f122 (f123 f139 ?v0) ?v1) f1) (=> (= (f33 f109 ?v2) f1) (=> (= (f33 (f34 f35 ?v3) ?v2) f1) (= (f98 ?v1 ?v2) (ite (= ?v_0 f8) ?v3 (f125 (f126 ?v0 ?v3) (f98 ?v1 ?v_0))))))))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S6) (?v3 S7)) (let ((?v_0 (f10 (f46 f143 ?v2) (f10 (f12 f13 ?v3) f14)))) (=> (= (f127 (f128 f140 ?v0) ?v1) f1) (=> (= (f37 f107 ?v2) f1) (=> (= (f37 (f38 f39 ?v3) ?v2) f1) (= (f100 ?v1 ?v2) (ite (= ?v_0 f14) ?v3 (f130 (f131 ?v0 ?v3) (f100 ?v1 ?v_0))))))))))
(assert (forall ((?v0 S63) (?v1 S49) (?v2 S2) (?v3 S3)) (let ((?v_0 (f6 f7 ?v3))) (let ((?v_1 (f4 (f44 f142 ?v2) (f4 ?v_0 f8)))) (=> (= (f122 (f123 f139 ?v0) ?v1) f1) (=> (= (f33 f109 ?v2) f1) (= (f98 ?v1 (f4 ?v_0 ?v2)) (ite (= ?v_1 f8) ?v3 (f125 (f126 ?v0 ?v3) (f98 ?v1 ?v_1))))))))))
(assert (forall ((?v0 S67) (?v1 S50) (?v2 S6) (?v3 S7)) (let ((?v_0 (f12 f13 ?v3))) (let ((?v_1 (f10 (f46 f143 ?v2) (f10 ?v_0 f14)))) (=> (= (f127 (f128 f140 ?v0) ?v1) f1) (=> (= (f37 f107 ?v2) f1) (= (f100 ?v1 (f10 ?v_0 ?v2)) (ite (= ?v_1 f14) ?v3 (f130 (f131 ?v0 ?v3) (f100 ?v1 ?v_1))))))))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f37 ?v_0 ?v1) f1) (=> (not (= (f37 ?v_0 ?v2) f1)) (= (f37 ?v_0 (f10 (f46 f143 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f33 ?v_0 ?v1) f1) (=> (not (= (f33 ?v_0 ?v2) f1)) (= (f33 ?v_0 (f4 (f44 f142 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f37 ?v_0 (f10 (f46 f143 ?v1) ?v2)) f1) (=> (=> (= (f37 ?v_0 ?v1) f1) (=> (not (= (f37 ?v_0 ?v2) f1)) false)) false)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f33 ?v_0 (f4 (f44 f142 ?v1) ?v2)) f1) (=> (=> (= (f33 ?v_0 ?v1) f1) (=> (not (= (f33 ?v_0 ?v2) f1)) false)) false)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f37 f107 ?v0) f1) (= (f37 f107 (f10 (f46 f143 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f33 f109 ?v0) f1) (= (f33 f109 (f4 (f44 f142 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f46 f143 ?v0) ?v1) (f10 f97 (f10 (f46 f47 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f44 f142 ?v0) ?v1) (f4 f96 (f4 (f44 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (= (= (f37 ?v_0 (f10 (f46 f143 ?v1) ?v2)) f1) (and (= (f37 ?v_0 ?v1) f1) (not (= (f37 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f34 f35 ?v0))) (= (= (f33 ?v_0 (f4 (f44 f142 ?v1) ?v2)) f1) (and (= (f33 ?v_0 ?v1) f1) (not (= (f33 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 (f44 f142 ?v0) ?v1))) (= (f4 (f44 f142 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f10 (f46 f143 ?v0) ?v1))) (= (f10 (f46 f143 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f37 ?v_0 (f10 (f46 f143 ?v1) ?v2)) f1) (= (f37 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f33 ?v_0 (f4 (f44 f142 ?v1) ?v2)) f1) (= (f33 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S56)) (= (f115 f116 (f117 f118 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f117 f118 (f115 f116 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f117 f118 (f115 f116 ?v0)) 0))))
(check-sat)
(exit)

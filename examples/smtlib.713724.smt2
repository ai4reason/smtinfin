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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 (S7 S8) S5)
(declare-fun f7 (S9 S6) S7)
(declare-fun f8 () S9)
(declare-fun f9 (S10 S2) S6)
(declare-fun f10 () S10)
(declare-fun f11 (S11 S2) S8)
(declare-fun f12 () S11)
(declare-fun f13 () S10)
(declare-fun f14 () S3)
(declare-fun f15 () S10)
(declare-fun f16 () S10)
(declare-fun f17 (S13 S12) S1)
(declare-fun f18 (S14 S12) S13)
(declare-fun f19 () S14)
(declare-fun f20 (S15 S12) Int)
(declare-fun f21 () S15)
(declare-fun f22 (S16 S4) S1)
(declare-fun f23 (S17 S16) S16)
(declare-fun f24 (S18 S16) S17)
(declare-fun f25 () S18)
(declare-fun f26 (S19 S13) S13)
(declare-fun f27 (S20 S13) S19)
(declare-fun f28 () S20)
(declare-fun f29 (S21 S2) S1)
(declare-fun f30 (S22 S21) S21)
(declare-fun f31 (S23 S21) S22)
(declare-fun f32 () S23)
(declare-fun f33 (S26 S24) S1)
(declare-fun f34 (S6 S25) S26)
(declare-fun f35 (S27 S24) S6)
(declare-fun f36 () S27)
(declare-fun f37 (S28 S25) S6)
(declare-fun f38 (S29 S6) S28)
(declare-fun f39 () S29)
(declare-fun f40 (S30 S6) S6)
(declare-fun f41 (S31 S1) S30)
(declare-fun f42 () S31)
(declare-fun f43 (S32 S4) S4)
(declare-fun f44 (S33 S4) S32)
(declare-fun f45 () S33)
(declare-fun f46 (S34 S12) S4)
(declare-fun f47 (S35 S4) S34)
(declare-fun f48 () S35)
(declare-fun f49 (S36 S4) S3)
(declare-fun f50 () S36)
(declare-fun f51 (S37 S4) S12)
(declare-fun f52 (S38 S12) S37)
(declare-fun f53 () S38)
(declare-fun f54 (S39 S12) S12)
(declare-fun f55 (S40 S12) S39)
(declare-fun f56 () S40)
(declare-fun f57 (S41 S2) S12)
(declare-fun f58 (S42 S12) S41)
(declare-fun f59 () S42)
(declare-fun f60 (S43 S4) S2)
(declare-fun f61 (S44 S2) S43)
(declare-fun f62 () S44)
(declare-fun f63 (S45 S12) S2)
(declare-fun f64 (S46 S2) S45)
(declare-fun f65 () S46)
(declare-fun f66 () S16)
(declare-fun f67 () S13)
(declare-fun f68 () S21)
(declare-fun f69 (S47 S16) S1)
(declare-fun f70 (S48 S16) S47)
(declare-fun f71 () S48)
(declare-fun f72 () S16)
(declare-fun f73 (S49 S21) S16)
(declare-fun f74 (S50 S3) S49)
(declare-fun f75 () S50)
(declare-fun f76 () S21)
(declare-fun f77 (S51 S21) S1)
(declare-fun f78 () S51)
(declare-fun f79 (S52 S4) S17)
(declare-fun f80 () S52)
(declare-fun f81 () S16)
(declare-fun f82 () S47)
(declare-fun f83 (S53 S16) S21)
(declare-fun f84 (S54 S43) S53)
(declare-fun f85 () S54)
(declare-fun f86 (S55 S13) S1)
(declare-fun f87 () S55)
(declare-fun f88 (S56 S13) S21)
(declare-fun f89 (S57 S45) S56)
(declare-fun f90 () S57)
(declare-fun f91 (S58 S21) S13)
(declare-fun f92 (S59 S41) S58)
(declare-fun f93 () S59)
(declare-fun f94 (S60 S39) S19)
(declare-fun f95 () S60)
(declare-fun f96 (S61 S13) S16)
(declare-fun f97 (S62 S34) S61)
(declare-fun f98 () S62)
(declare-fun f99 (S63 S32) S17)
(declare-fun f100 () S63)
(declare-fun f101 (S64 S16) S13)
(declare-fun f102 (S65 S37) S64)
(declare-fun f103 () S65)
(declare-fun f104 (S66 S2) S22)
(declare-fun f105 () S66)
(declare-fun f106 (S67 S12) S19)
(declare-fun f107 () S67)
(declare-fun f108 () S21)
(declare-fun f109 () S13)
(declare-fun f110 () S19)
(declare-fun f111 () S22)
(declare-fun f112 () S17)
(declare-fun f113 (S68 S2) S51)
(declare-fun f114 () S68)
(declare-fun f115 (S69 S4) S47)
(declare-fun f116 () S69)
(declare-fun f117 (S70 S12) S55)
(declare-fun f118 () S70)
(declare-fun f119 (S71 Int) S12)
(declare-fun f120 () S71)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 (f9 f10 ?v0)) (f11 f12 ?v0)) (f9 f13 ?v0)))))
(assert (forall ((?v0 S2)) (= (f3 f14 ?v0) (f5 (f6 (f7 f8 (f9 f15 ?v0)) (f11 f12 ?v0)) (f9 f16 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f17 (f18 f19 ?v0) ?v1) f1) (< (f20 f21 ?v1) (f20 f21 ?v0)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S4)) (= (= (f22 (f23 (f24 f25 ?v0) ?v1) ?v2) f1) (and (= (f22 ?v0 ?v2) f1) (= (f22 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S12)) (= (= (f17 (f26 (f27 f28 ?v0) ?v1) ?v2) f1) (and (= (f17 ?v0 ?v2) f1) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S2)) (= (= (f29 (f30 (f31 f32 ?v0) ?v1) ?v2) f1) (and (= (f29 ?v0 ?v2) f1) (= (f29 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S24) (?v1 S25) (?v2 S24)) (= (= (f33 (f34 (f35 f36 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S6) (?v1 S25) (?v2 S25)) (= (f34 (f37 (f38 f39 ?v0) ?v1) ?v2) (f34 ?v0 ?v1))))
(assert (forall ((?v0 S1) (?v1 S6) (?v2 S25) (?v3 S24)) (= (= (f33 (f34 (f40 (f41 f42 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f33 (f34 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f43 (f44 f45 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4) (?v1 S12)) (= (f46 (f47 f48 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f3 (f49 f50 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S12) (?v1 S4)) (= (f51 (f52 f53 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f54 (f55 f56 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S12) (?v1 S2)) (= (f57 (f58 f59 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S4)) (= (f60 (f61 f62 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S12)) (= (f63 (f64 f65 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4)) (= (= (f22 f66 ?v0) f1) false)))
(assert (forall ((?v0 S12)) (= (= (f17 f67 ?v0) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f29 f68 ?v0) f1) false)))
(assert (let ((?v_0 (f70 f71 f72))) (not (=> (= (f69 ?v_0 (f73 (f74 f75 f4) f76)) f1) (= (f69 ?v_0 (f73 (f74 f75 f14) f76)) f1)))))
(assert (= (f77 f78 f76) f1))
(assert (forall ((?v0 S2)) (let ((?v_0 (f70 f71 f72)) (?v_1 (f11 f12 ?v0))) (=> (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 (f9 f10 ?v0)) ?v_1) (f9 f13 ?v0))) f81)) f1) (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 (f9 f15 ?v0)) ?v_1) (f9 f16 ?v0))) f81)) f1)))))
(assert (forall ((?v0 S16)) (= (f69 (f70 f71 ?v0) f81) f1)))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_0 (f70 f71 ?v2))) (=> (= (f69 (f70 f71 ?v0) ?v1) f1) (=> (= (f69 ?v_0 ?v0) f1) (= (f69 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S16) (?v1 S4) (?v2 S16)) (let ((?v_0 (f70 f71 ?v0)) (?v_1 (f79 f80 ?v1))) (=> (= (f69 ?v_0 (f23 ?v_1 f81)) f1) (=> (= (f69 ?v_0 ?v2) f1) (= (f69 ?v_0 (f23 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S16) (?v1 S4) (?v2 S16)) (let ((?v_0 (f70 f71 ?v0)) (?v_1 (f79 f80 ?v1))) (=> (= (f69 ?v_0 (f23 ?v_1 ?v2)) f1) (and (= (f69 ?v_0 (f23 ?v_1 f81)) f1) (= (f69 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S16) (?v2 S6) (?v3 S8) (?v4 S6)) (let ((?v_0 (f70 f71 ?v1))) (=> (=> (= ?v0 f1) (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 ?v2) ?v3) ?v4)) f81)) f1)) (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 (f40 (f41 f42 ?v0) ?v2)) ?v3) ?v4)) f81)) f1)))))
(assert (forall ((?v0 S6) (?v1 S16) (?v2 S8) (?v3 S6)) (=> (forall ((?v4 S25) (?v5 S24)) (=> (= (f33 (f34 ?v0 ?v4) ?v5) f1) (= (f69 (f70 f71 ?v1) (f23 (f79 f80 (f5 (f6 (f7 f8 (f35 f36 ?v5)) ?v2) (f37 (f38 f39 ?v3) ?v4))) f81)) f1))) (= (f69 (f70 f71 ?v1) (f23 (f79 f80 (f5 (f6 (f7 f8 ?v0) ?v2) ?v3)) f81)) f1))))
(assert (forall ((?v0 S16) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (let ((?v_0 (f70 f71 ?v0)) (?v_1 (f6 (f7 f8 ?v1) ?v2))) (=> (= (f69 ?v_0 (f23 (f79 f80 (f5 ?v_1 ?v3)) f81)) f1) (=> (forall ((?v5 S25) (?v6 S24)) (=> (= (f33 (f34 ?v3 ?v5) ?v6) f1) (= (f33 (f34 ?v4 ?v5) ?v6) f1))) (= (f69 ?v_0 (f23 (f79 f80 (f5 ?v_1 ?v4)) f81)) f1))))))
(assert (forall ((?v0 S16) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (let ((?v_0 (f70 f71 ?v0))) (=> (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) f81)) f1) (=> (forall ((?v5 S25) (?v6 S24)) (=> (= (f33 (f34 ?v4 ?v5) ?v6) f1) (= (f33 (f34 ?v1 ?v5) ?v6) f1))) (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 ?v4) ?v2) ?v3)) f81)) f1))))))
(assert (forall ((?v0 S21) (?v1 S3)) (=> (= (f77 f78 ?v0) f1) (= (f69 f82 (f73 (f74 f75 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S16) (?v1 S43)) (=> (= (f69 f82 ?v0) f1) (= (f77 f78 (f83 (f84 f85 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S45)) (=> (= (f86 f87 ?v0) f1) (= (f77 f78 (f88 (f89 f90 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S21) (?v1 S41)) (=> (= (f77 f78 ?v0) f1) (= (f86 f87 (f91 (f92 f93 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S39)) (=> (= (f86 f87 ?v0) f1) (= (f86 f87 (f26 (f94 f95 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S34)) (=> (= (f86 f87 ?v0) f1) (= (f69 f82 (f96 (f97 f98 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S16) (?v1 S32)) (=> (= (f69 f82 ?v0) f1) (= (f69 f82 (f23 (f99 f100 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S16) (?v1 S37)) (=> (= (f69 f82 ?v0) f1) (= (f86 f87 (f101 (f102 f103 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S16) (?v1 S4)) (=> (= (f69 f82 ?v0) f1) (= (f69 f82 (f23 (f79 f80 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S21) (?v1 S2)) (=> (= (f77 f78 ?v0) f1) (= (f77 f78 (f30 (f104 f105 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S12)) (=> (= (f86 f87 ?v0) f1) (= (f86 f87 (f26 (f106 f107 ?v1) ?v0)) f1))))
(assert (= (f77 f78 f108) f1))
(assert (= (f69 f82 f81) f1))
(assert (= (f86 f87 f109) f1))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (or (= (f86 f87 (f26 f110 ?v0)) f1) (= (f86 f87 (f26 f110 ?v1)) f1)) (= (f86 f87 (f26 f110 (f26 (f27 f28 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S21) (?v1 S21)) (=> (or (= (f77 f78 (f30 f111 ?v0)) f1) (= (f77 f78 (f30 f111 ?v1)) f1)) (= (f77 f78 (f30 f111 (f30 (f31 f32 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S16) (?v1 S16)) (=> (or (= (f69 f82 (f23 f112 ?v0)) f1) (= (f69 f82 (f23 f112 ?v1)) f1)) (= (f69 f82 (f23 f112 (f23 (f24 f25 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S4) (?v1 S21)) (= (f73 (f74 f75 (f49 f50 ?v0)) ?v1) (ite (= ?v1 f108) f81 (f23 (f79 f80 ?v0) f81)))))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f96 (f97 f98 (f47 f48 ?v0)) ?v1) (ite (= ?v1 f109) f81 (f23 (f79 f80 ?v0) f81)))))
(assert (forall ((?v0 S12) (?v1 S16)) (= (f101 (f102 f103 (f52 f53 ?v0)) ?v1) (ite (= ?v1 f81) f109 (f26 (f106 f107 ?v0) f109)))))
(assert (forall ((?v0 S2) (?v1 S16)) (= (f83 (f84 f85 (f61 f62 ?v0)) ?v1) (ite (= ?v1 f81) f108 (f30 (f104 f105 ?v0) f108)))))
(assert (forall ((?v0 S12) (?v1 S13)) (= (f26 (f94 f95 (f55 f56 ?v0)) ?v1) (ite (= ?v1 f109) f109 (f26 (f106 f107 ?v0) f109)))))
(assert (forall ((?v0 S4) (?v1 S16)) (= (f23 (f99 f100 (f44 f45 ?v0)) ?v1) (ite (= ?v1 f81) f81 (f23 (f79 f80 ?v0) f81)))))
(assert (forall ((?v0 S12) (?v1 S21)) (= (f91 (f92 f93 (f58 f59 ?v0)) ?v1) (ite (= ?v1 f108) f109 (f26 (f106 f107 ?v0) f109)))))
(assert (forall ((?v0 S2) (?v1 S13)) (= (f88 (f89 f90 (f64 f65 ?v0)) ?v1) (ite (= ?v1 f109) f108 (f30 (f104 f105 ?v0) f108)))))
(assert (forall ((?v0 S2) (?v1 S21) (?v2 S4)) (=> (= (f77 (f113 f114 ?v0) ?v1) f1) (= (f73 (f74 f75 (f49 f50 ?v2)) ?v1) (f23 (f79 f80 ?v2) f81)))))
(assert (forall ((?v0 S4) (?v1 S16) (?v2 S4)) (=> (= (f69 (f115 f116 ?v0) ?v1) f1) (= (f23 (f99 f100 (f44 f45 ?v2)) ?v1) (f23 (f79 f80 ?v2) f81)))))
(assert (forall ((?v0 S12) (?v1 S13) (?v2 S4)) (=> (= (f86 (f117 f118 ?v0) ?v1) f1) (= (f96 (f97 f98 (f47 f48 ?v2)) ?v1) (f23 (f79 f80 ?v2) f81)))))
(assert (forall ((?v0 S12) (?v1 S13) (?v2 S12)) (=> (= (f86 (f117 f118 ?v0) ?v1) f1) (= (f26 (f94 f95 (f55 f56 ?v2)) ?v1) (f26 (f106 f107 ?v2) f109)))))
(assert (forall ((?v0 S4) (?v1 S16) (?v2 S12)) (=> (= (f69 (f115 f116 ?v0) ?v1) f1) (= (f101 (f102 f103 (f52 f53 ?v2)) ?v1) (f26 (f106 f107 ?v2) f109)))))
(assert (forall ((?v0 S2) (?v1 S21) (?v2 S12)) (=> (= (f77 (f113 f114 ?v0) ?v1) f1) (= (f91 (f92 f93 (f58 f59 ?v2)) ?v1) (f26 (f106 f107 ?v2) f109)))))
(assert (forall ((?v0 S4) (?v1 S16) (?v2 S2)) (=> (= (f69 (f115 f116 ?v0) ?v1) f1) (= (f83 (f84 f85 (f61 f62 ?v2)) ?v1) (f30 (f104 f105 ?v2) f108)))))
(assert (forall ((?v0 S12) (?v1 S13) (?v2 S2)) (=> (= (f86 (f117 f118 ?v0) ?v1) f1) (= (f88 (f89 f90 (f64 f65 ?v2)) ?v1) (f30 (f104 f105 ?v2) f108)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S21)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f77 (f113 f114 ?v2) ?v3) f1) (= (f69 (f115 f116 ?v0) (f73 (f74 f75 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S12) (?v1 S39) (?v2 S12) (?v3 S13)) (=> (= ?v0 (f54 ?v1 ?v2)) (=> (= (f86 (f117 f118 ?v2) ?v3) f1) (= (f86 (f117 f118 ?v0) (f26 (f94 f95 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S34) (?v2 S12) (?v3 S13)) (=> (= ?v0 (f46 ?v1 ?v2)) (=> (= (f86 (f117 f118 ?v2) ?v3) f1) (= (f69 (f115 f116 ?v0) (f96 (f97 f98 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S12) (?v1 S41) (?v2 S2) (?v3 S21)) (=> (= ?v0 (f57 ?v1 ?v2)) (=> (= (f77 (f113 f114 ?v2) ?v3) f1) (= (f86 (f117 f118 ?v0) (f91 (f92 f93 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S32) (?v2 S4) (?v3 S16)) (=> (= ?v0 (f43 ?v1 ?v2)) (=> (= (f69 (f115 f116 ?v2) ?v3) f1) (= (f69 (f115 f116 ?v0) (f23 (f99 f100 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S12) (?v1 S37) (?v2 S4) (?v3 S16)) (=> (= ?v0 (f51 ?v1 ?v2)) (=> (= (f69 (f115 f116 ?v2) ?v3) f1) (= (f86 (f117 f118 ?v0) (f101 (f102 f103 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S43) (?v2 S4) (?v3 S16)) (=> (= ?v0 (f60 ?v1 ?v2)) (=> (= (f69 (f115 f116 ?v2) ?v3) f1) (= (f77 (f113 f114 ?v0) (f83 (f84 f85 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S45) (?v2 S12) (?v3 S13)) (=> (= ?v0 (f63 ?v1 ?v2)) (=> (= (f86 (f117 f118 ?v2) ?v3) f1) (= (f77 (f113 f114 ?v0) (f88 (f89 f90 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S16) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6) (?v5 S6)) (let ((?v_0 (f70 f71 ?v0))) (=> (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) f81)) f1) (=> (forall ((?v6 S25) (?v7 S24)) (=> (= (f33 (f34 ?v4 ?v6) ?v7) f1) (forall ((?v8 S24)) (=> (forall ((?v9 S25)) (=> (= (f33 (f34 ?v1 ?v9) ?v7) f1) (= (f33 (f34 ?v3 ?v9) ?v8) f1))) (= (f33 (f34 ?v5 ?v6) ?v8) f1))))) (= (f69 ?v_0 (f23 (f79 f80 (f5 (f6 (f7 f8 ?v4) ?v2) ?v5)) f81)) f1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S16)) (let ((?v_0 (f115 f116 ?v0))) (=> (= (f69 ?v_0 (f23 (f79 f80 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f69 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S13)) (let ((?v_0 (f117 f118 ?v0))) (=> (= (f86 ?v_0 (f26 (f106 f107 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f86 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S21)) (let ((?v_0 (f113 f114 ?v0))) (=> (= (f77 ?v_0 (f30 (f104 f105 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f77 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S4)) (=> (= (f69 (f115 f116 ?v0) f81) f1) false)))
(assert (forall ((?v0 S12)) (=> (= (f86 (f117 f118 ?v0) f109) f1) false)))
(assert (forall ((?v0 S2)) (=> (= (f77 (f113 f114 ?v0) f108) f1) false)))
(assert (forall ((?v0 S4) (?v1 S16) (?v2 S4)) (let ((?v_0 (f115 f116 ?v0))) (=> (=> (not (= (f69 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f69 ?v_0 (f23 (f79 f80 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S12) (?v1 S13) (?v2 S12)) (let ((?v_0 (f117 f118 ?v0))) (=> (=> (not (= (f86 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f86 ?v_0 (f26 (f106 f107 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S21) (?v2 S2)) (let ((?v_0 (f113 f114 ?v0))) (=> (=> (not (= (f77 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f77 ?v_0 (f30 (f104 f105 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S21) (?v1 S45) (?v2 S12)) (=> (= ?v0 (f88 (f89 f90 ?v1) (f26 f110 (f18 f19 ?v2)))) (= (f77 f78 ?v0) f1))))
(assert (forall ((?v0 S16) (?v1 S34) (?v2 S12)) (=> (= ?v0 (f96 (f97 f98 ?v1) (f26 f110 (f18 f19 ?v2)))) (= (f69 f82 ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S39) (?v2 S12)) (=> (= ?v0 (f26 (f94 f95 ?v1) (f26 f110 (f18 f19 ?v2)))) (= (f86 f87 ?v0) f1))))
(assert (forall ((?v0 S16) (?v1 S4)) (=> (= ?v0 f81) (not (= (f69 (f115 f116 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S12)) (=> (= ?v0 f109) (not (= (f86 (f117 f118 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S21) (?v1 S2)) (=> (= ?v0 f108) (not (= (f77 (f113 f114 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13)) (= (= (f26 f110 ?v0) f109) (forall ((?v1 S12)) (not (= (f17 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S16)) (= (= (f23 f112 ?v0) f81) (forall ((?v1 S4)) (not (= (f22 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S21)) (= (= (f30 f111 ?v0) f108) (forall ((?v1 S2)) (not (= (f29 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (= (f69 (f115 f116 ?v0) f81) f1) false)))
(assert (forall ((?v0 S12)) (= (= (f86 (f117 f118 ?v0) f109) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f77 (f113 f114 ?v0) f108) f1) false)))
(assert (forall ((?v0 S13)) (= (= f109 (f26 f110 ?v0)) (forall ((?v1 S12)) (not (= (f17 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S16)) (= (= f81 (f23 f112 ?v0)) (forall ((?v1 S4)) (not (= (f22 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S21)) (= (= f108 (f30 f111 ?v0)) (forall ((?v1 S2)) (not (= (f29 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S16)) (= (forall ((?v1 S4)) (=> (= (f69 (f115 f116 ?v1) f81) f1) (= (f22 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S13)) (= (forall ((?v1 S12)) (=> (= (f86 (f117 f118 ?v1) f109) f1) (= (f17 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S21)) (= (forall ((?v1 S2)) (=> (= (f77 (f113 f114 ?v1) f108) f1) (= (f29 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S16)) (= (exists ((?v1 S4)) (and (= (f69 (f115 f116 ?v1) f81) f1) (= (f22 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S13)) (= (exists ((?v1 S12)) (and (= (f86 (f117 f118 ?v1) f109) f1) (= (f17 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S21)) (= (exists ((?v1 S2)) (and (= (f77 (f113 f114 ?v1) f108) f1) (= (f29 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S16)) (= (exists ((?v1 S4)) (= (f69 (f115 f116 ?v1) ?v0) f1)) (not (= ?v0 f81)))))
(assert (forall ((?v0 S13)) (= (exists ((?v1 S12)) (= (f86 (f117 f118 ?v1) ?v0) f1)) (not (= ?v0 f109)))))
(assert (forall ((?v0 S21)) (= (exists ((?v1 S2)) (= (f77 (f113 f114 ?v1) ?v0) f1)) (not (= ?v0 f108)))))
(assert (forall ((?v0 S16)) (= (forall ((?v1 S4)) (not (= (f69 (f115 f116 ?v1) ?v0) f1))) (= ?v0 f81))))
(assert (forall ((?v0 S13)) (= (forall ((?v1 S12)) (not (= (f86 (f117 f118 ?v1) ?v0) f1))) (= ?v0 f109))))
(assert (forall ((?v0 S21)) (= (forall ((?v1 S2)) (not (= (f77 (f113 f114 ?v1) ?v0) f1))) (= ?v0 f108))))
(assert (= f109 (f26 f110 f67)))
(assert (= f81 (f23 f112 f66)))
(assert (= f108 (f30 f111 f68)))
(assert (forall ((?v0 S12)) (= (f119 f120 (f20 f21 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f20 f21 (f119 f120 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f20 f21 (f119 f120 ?v0)) 0))))
(check-sat)
(exit)

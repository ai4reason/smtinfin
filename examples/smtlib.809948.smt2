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
(declare-fun f14 (S12 S10) S3)
(declare-fun f15 (S13 S10) S12)
(declare-fun f16 () S13)
(declare-fun f17 (S14 S15) S8)
(declare-fun f18 () S14)
(declare-fun f19 (S2) S15)
(declare-fun f20 () S13)
(declare-fun f21 (S16 S4) S1)
(declare-fun f22 (S17 S18) S16)
(declare-fun f23 () S17)
(declare-fun f24 (S19 Int) S18)
(declare-fun f25 () S19)
(declare-fun f26 (S20 S18) Int)
(declare-fun f27 () S20)
(declare-fun f28 () S18)
(declare-fun f29 () S2)
(declare-fun f30 (S21 S16) S1)
(declare-fun f31 (S22 S4) S21)
(declare-fun f32 () S22)
(declare-fun f33 (S23 S16) S16)
(declare-fun f34 (S24 S16) S23)
(declare-fun f35 () S24)
(declare-fun f36 () S16)
(declare-fun f37 (S25 S26) S16)
(declare-fun f38 (S27 S3) S25)
(declare-fun f39 () S27)
(declare-fun f40 () S26)
(declare-fun f41 (S28 S26) S1)
(declare-fun f42 (S29 S2) S28)
(declare-fun f43 () S29)
(declare-fun f44 (S30 S16) S21)
(declare-fun f45 () S30)
(declare-fun f46 (S31 S26) S26)
(declare-fun f47 (S32 S26) S31)
(declare-fun f48 () S32)
(declare-fun f49 (S26 S2) S1)
(declare-fun f50 (S33 S4) S2)
(declare-fun f51 (S34 S16) S26)
(declare-fun f52 (S35 S33) S34)
(declare-fun f53 () S35)
(declare-fun f54 (S37 S4) S18)
(declare-fun f55 (S38 S36) S37)
(declare-fun f56 () S38)
(declare-fun f57 (S39 S1) S1)
(declare-fun f58 (S40 S1) S39)
(declare-fun f59 () S40)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 (f9 f10 ?v0)) (f11 f12 ?v0)) (f9 f13 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S2)) (= (f3 (f14 (f15 f16 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f9 ?v0 ?v2)) (f17 f18 (f19 ?v2))) (f9 ?v1 ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S2)) (= (f3 (f14 (f15 f20 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f9 ?v0 ?v2)) (f11 f12 ?v2)) (f9 ?v1 ?v2)))))
(assert (not (= (f21 (f22 f23 (f24 f25 (+ (f26 f27 f28) 1))) (f5 (f6 (f7 f8 (f9 f10 f29)) (f11 f12 f29)) (f9 f13 f29))) f1)))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S4)) (=> (= (f30 (f31 f32 ?v1) (f33 (f34 f35 f36) (f37 (f38 f39 f4) f40))) f1) (= (f21 (f22 f23 ?v0) ?v1) f1))) (forall ((?v1 S2)) (=> (= (f41 (f42 f43 ?v1) f40) f1) (= (f21 (f22 f23 ?v0) (f5 (f6 (f7 f8 (f9 f10 ?v1)) (f17 f18 (f19 ?v1))) (f9 f13 ?v1))) f1))))))
(assert (= (f41 (f42 f43 f29) f40) f1))
(assert (forall ((?v0 S4)) (=> (= (f30 (f31 f32 ?v0) f36) f1) (= (f21 (f22 f23 f28) ?v0) f1))))
(assert (forall ((?v0 S2)) (=> (= (f41 (f42 f43 ?v0) f40) f1) (= (f21 (f22 f23 f28) (f5 (f6 (f7 f8 (f9 f10 ?v0)) (f11 f12 ?v0)) (f9 f13 ?v0))) f1))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (= (f21 (f22 f23 (f24 f25 0)) (f5 (f6 (f7 f8 ?v0) (f11 f12 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S18) (?v1 S6) (?v2 S2) (?v3 S6)) (let ((?v_0 (f7 f8 ?v1))) (= (= (f21 (f22 f23 ?v0) (f5 (f6 ?v_0 (f17 f18 (f19 ?v2))) ?v3)) f1) (= (f21 (f22 f23 (f24 f25 (+ (f26 f27 ?v0) 1))) (f5 (f6 ?v_0 (f11 f12 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S16) (?v1 S18)) (=> (forall ((?v2 S4)) (=> (= (f30 (f31 f32 ?v2) ?v0) f1) (= (f21 (f22 f23 (f24 f25 (+ (f26 f27 ?v1) 1))) ?v2) f1))) (forall ((?v2 S4)) (=> (= (f30 (f31 f32 ?v2) ?v0) f1) (= (f21 (f22 f23 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S4)) (=> (= (f21 (f22 f23 (f24 f25 (+ (f26 f27 ?v0) 1))) ?v1) f1) (= (f21 (f22 f23 ?v0) ?v1) f1))))
(assert (forall ((?v0 S16) (?v1 S10) (?v2 S10) (?v3 S26)) (let ((?v_0 (f37 (f38 f39 (f14 (f15 f20 ?v1) ?v2)) ?v3))) (=> (= (f30 (f44 f45 (f33 (f34 f35 ?v0) ?v_0)) (f37 (f38 f39 (f14 (f15 f16 ?v1) ?v2)) ?v3)) f1) (= (f30 (f44 f45 ?v0) ?v_0) f1)))))
(assert (forall ((?v0 S2) (?v1 S26) (?v2 S26)) (let ((?v_0 (f42 f43 ?v0))) (=> (= (f41 ?v_0 (f46 (f47 f48 ?v1) ?v2)) f1) (=> (=> (= (f41 ?v_0 ?v1) f1) false) (=> (=> (= (f41 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S4) (?v1 S16) (?v2 S16)) (let ((?v_0 (f31 f32 ?v0))) (=> (= (f30 ?v_0 (f33 (f34 f35 ?v1) ?v2)) f1) (=> (=> (= (f30 ?v_0 ?v1) f1) false) (=> (=> (= (f30 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S4)) (=> (= (f21 (f33 (f34 f35 ?v0) ?v1) ?v2) f1) (=> (=> (= (f21 ?v0 ?v2) f1) false) (=> (=> (= (f21 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S2)) (=> (= (f49 (f46 (f47 f48 ?v0) ?v1) ?v2) f1) (=> (=> (= (f49 ?v0 ?v2) f1) false) (=> (=> (= (f49 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S16) (?v1 S4) (?v2 S16)) (=> (=> (not (= (f21 ?v0 ?v1) f1)) (= (f21 ?v2 ?v1) f1)) (= (f21 (f33 (f34 f35 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S26)) (=> (=> (not (= (f49 ?v0 ?v1) f1)) (= (f49 ?v2 ?v1) f1)) (= (f49 (f46 (f47 f48 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S26) (?v2 S26)) (let ((?v_0 (f42 f43 ?v0))) (=> (=> (not (= (f41 ?v_0 ?v1) f1)) (= (f41 ?v_0 ?v2) f1)) (= (f41 ?v_0 (f46 (f47 f48 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S16) (?v2 S16)) (let ((?v_0 (f31 f32 ?v0))) (=> (=> (not (= (f30 ?v_0 ?v1) f1)) (= (f30 ?v_0 ?v2) f1)) (= (f30 ?v_0 (f33 (f34 f35 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S26)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f41 (f42 f43 ?v2) ?v3) f1) (= (f30 (f31 f32 ?v0) (f37 (f38 f39 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S33) (?v2 S4) (?v3 S16)) (=> (= ?v0 (f50 ?v1 ?v2)) (=> (= (f30 (f31 f32 ?v2) ?v3) f1) (= (f41 (f42 f43 ?v0) (f51 (f52 f53 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S36) (?v1 S6) (?v2 S8) (?v3 S6)) (= (f54 (f55 f56 ?v0) (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) (f24 f25 0))))
(assert (forall ((?v0 S3) (?v1 S26) (?v2 S26)) (let ((?v_0 (f38 f39 ?v0))) (= (f37 ?v_0 (f46 (f47 f48 ?v1) ?v2)) (f33 (f34 f35 (f37 ?v_0 ?v1)) (f37 ?v_0 ?v2))))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S16)) (let ((?v_0 (f52 f53 ?v0))) (= (f51 ?v_0 (f33 (f34 f35 ?v1) ?v2)) (f46 (f47 f48 (f51 ?v_0 ?v1)) (f51 ?v_0 ?v2))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S4)) (= (= (f21 (f33 (f34 f35 ?v0) ?v1) ?v2) f1) (= (f57 (f58 f59 (f21 ?v0 ?v2)) (f21 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S2)) (= (= (f49 (f46 (f47 f48 ?v0) ?v1) ?v2) f1) (= (f57 (f58 f59 (f49 ?v0 ?v2)) (f49 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S4)) (= (= (f21 (f33 (f34 f35 ?v0) ?v1) ?v2) f1) (= (f57 (f58 f59 (f21 ?v0 ?v2)) (f21 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S2)) (= (= (f49 (f46 (f47 f48 ?v0) ?v1) ?v2) f1) (= (f57 (f58 f59 (f49 ?v0 ?v2)) (f49 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_0 (f44 f45 ?v2))) (=> (= (f30 (f44 f45 ?v0) ?v1) f1) (=> (= (f30 ?v_0 ?v0) f1) (= (f30 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v2) (f33 ?v_0 (f33 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f47 f48 ?v0))) (= (f46 (f47 f48 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f47 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f58 f59 ?v0))) (= (= (f57 (f58 f59 (f57 ?v_0 ?v1)) ?v2) f1) (= (f57 ?v_0 (f57 (f58 f59 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v2) (f33 ?v_0 (f33 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f47 f48 ?v0))) (= (f46 (f47 f48 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f47 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f58 f59 ?v0))) (= (= (f57 (f58 f59 (f57 ?v_0 ?v1)) ?v2) f1) (= (f57 ?v_0 (f57 (f58 f59 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v2) (f33 ?v_0 (f33 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f47 f48 ?v0))) (= (f46 (f47 f48 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f47 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f58 f59 ?v0))) (= (= (f57 (f58 f59 (f57 ?v_0 ?v1)) ?v2) f1) (= (f57 ?v_0 (f57 (f58 f59 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_1 (f34 f35 ?v0)) (?v_0 (f34 f35 ?v1))) (= (f33 ?v_1 (f33 ?v_0 ?v2)) (f33 ?v_0 (f33 ?v_1 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_1 (f47 f48 ?v0)) (?v_0 (f47 f48 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f58 f59 ?v0)) (?v_0 (f58 f59 ?v1))) (= (= (f57 ?v_1 (f57 ?v_0 ?v2)) f1) (= (f57 ?v_0 (f57 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_1 (f34 f35 ?v0)) (?v_0 (f34 f35 ?v1))) (= (f33 ?v_1 (f33 ?v_0 ?v2)) (f33 ?v_0 (f33 ?v_1 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_1 (f47 f48 ?v0)) (?v_0 (f47 f48 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f58 f59 ?v0)) (?v_0 (f58 f59 ?v1))) (= (= (f57 ?v_1 (f57 ?v_0 ?v2)) f1) (= (f57 ?v_0 (f57 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_1 (f34 f35 ?v0)) (?v_0 (f34 f35 ?v1))) (= (f33 ?v_1 (f33 ?v_0 ?v2)) (f33 ?v_0 (f33 ?v_1 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_1 (f47 f48 ?v0)) (?v_0 (f47 f48 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f58 f59 ?v0)) (?v_0 (f58 f59 ?v1))) (= (= (f57 ?v_1 (f57 ?v_0 ?v2)) f1) (= (f57 ?v_0 (f57 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S16) (?v1 S16)) (let ((?v_0 (f34 f35 ?v0))) (let ((?v_1 (f33 ?v_0 ?v1))) (= (f33 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S26) (?v1 S26)) (let ((?v_0 (f47 f48 ?v0))) (let ((?v_1 (f46 ?v_0 ?v1))) (= (f46 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f58 f59 ?v0))) (let ((?v_1 (f57 ?v_0 ?v1))) (= (= (f57 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S16) (?v1 S16)) (let ((?v_0 (f34 f35 ?v0))) (let ((?v_1 (f33 ?v_0 ?v1))) (= (f33 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S26) (?v1 S26)) (let ((?v_0 (f47 f48 ?v0))) (let ((?v_1 (f46 ?v_0 ?v1))) (= (f46 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f58 f59 ?v0))) (let ((?v_1 (f57 ?v_0 ?v1))) (= (= (f57 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S16) (?v1 S16)) (let ((?v_0 (f34 f35 ?v0))) (let ((?v_1 (f33 ?v_0 ?v1))) (= (f33 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S26) (?v1 S26)) (let ((?v_0 (f47 f48 ?v0))) (let ((?v_1 (f46 ?v_0 ?v1))) (= (f46 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f58 f59 ?v0))) (let ((?v_1 (f57 ?v_0 ?v1))) (= (= (f57 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (f33 (f34 f35 ?v0) ?v1) (f33 (f34 f35 ?v1) ?v0))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f57 (f58 f59 ?v0) ?v1) f1) (= (f57 (f58 f59 ?v1) ?v0) f1))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (f33 (f34 f35 ?v0) ?v1) (f33 (f34 f35 ?v1) ?v0))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f57 (f58 f59 ?v0) ?v1) f1) (= (f57 (f58 f59 ?v1) ?v0) f1))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (f33 (f34 f35 ?v0) ?v1) (f33 (f34 f35 ?v1) ?v0))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f57 (f58 f59 ?v0) ?v1) f1) (= (f57 (f58 f59 ?v1) ?v0) f1))))
(assert (forall ((?v0 S16)) (= (f33 (f34 f35 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S26)) (= (f46 (f47 f48 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f57 (f58 f59 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S16)) (= (f33 (f34 f35 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S26)) (= (f46 (f47 f48 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f57 (f58 f59 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S18)) (= (f24 f25 (f26 f27 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f26 f27 (f24 f25 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f26 f27 (f24 f25 ?v0)) 0))))
(check-sat)
(exit)

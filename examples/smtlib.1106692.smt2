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
(declare-fun f9 () S6)
(declare-fun f10 (S10 S11) S8)
(declare-fun f11 () S10)
(declare-fun f12 (S2) S11)
(declare-fun f13 (S8) S6)
(declare-fun f14 () S3)
(declare-fun f15 (S12 S2) S8)
(declare-fun f16 () S12)
(declare-fun f17 () S3)
(declare-fun f18 (S14 S13) S1)
(declare-fun f19 (S13) S14)
(declare-fun f20 (S15 S13) Int)
(declare-fun f21 () S15)
(declare-fun f22 (S17 S16) S1)
(declare-fun f23 (S6 S16) S17)
(declare-fun f24 (S19 S18) S3)
(declare-fun f25 (S20 S18) S19)
(declare-fun f26 () S20)
(declare-fun f27 (S18 S2) S6)
(declare-fun f28 () S20)
(declare-fun f29 (S21 S4) S1)
(declare-fun f30 (S22 S21) S21)
(declare-fun f31 (S21) S22)
(declare-fun f32 (S23 S2) S1)
(declare-fun f33 (S24 S23) S23)
(declare-fun f34 (S23) S24)
(declare-fun f35 (S25 S14) S14)
(declare-fun f36 (S14) S25)
(declare-fun f37 (S21 S21) S1)
(declare-fun f38 (S21) S22)
(declare-fun f39 () S21)
(declare-fun f40 (S26 S23) S21)
(declare-fun f41 (S3) S26)
(declare-fun f42 () S23)
(declare-fun f43 (S23) S1)
(declare-fun f44 (S21 S21) S1)
(declare-fun f45 (S21) S1)
(declare-fun f46 (S28 S21) S23)
(declare-fun f47 (S27) S28)
(declare-fun f48 (S14) S1)
(declare-fun f49 (S30 S14) S23)
(declare-fun f50 (S29) S30)
(declare-fun f51 (S32 S23) S14)
(declare-fun f52 (S31) S32)
(declare-fun f53 (S33) S25)
(declare-fun f54 (S35 S14) S21)
(declare-fun f55 (S34) S35)
(declare-fun f56 (S14) S14)
(declare-fun f57 (S23) S23)
(declare-fun f58 (S21) S21)
(declare-fun f59 (S4 S21) S1)
(declare-fun f60 (S13 S14) S1)
(declare-fun f61 (S14) S25)
(declare-fun f62 (S2 S23) S1)
(declare-fun f63 (S23) S24)
(declare-fun f64 (S33 S13) S13)
(declare-fun f65 (S34 S13) S4)
(declare-fun f66 (S31 S2) S13)
(declare-fun f67 (S36 S4) S13)
(declare-fun f68 (S37 S21) S14)
(declare-fun f69 (S36) S37)
(declare-fun f70 (S27 S4) S2)
(declare-fun f71 (S29 S13) S2)
(declare-fun f72 (S13) S21)
(declare-fun f73 (S38 Int) S13)
(declare-fun f74 () S38)
(declare-fun f75 (S40 S39) S36)
(declare-fun f76 () S40)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f10 f11 (f12 ?v0)))) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 f9) ?v_0) (f13 ?v_0))))))
(assert (forall ((?v0 S2)) (= (f3 f14 ?v0) (f5 (f6 (f7 f8 f9) (f10 f11 (f12 ?v0))) (f13 (f15 f16 ?v0))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f15 f16 ?v0))) (= (f3 f17 ?v0) (f5 (f6 (f7 f8 f9) ?v_0) (f13 ?v_0))))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f18 (f19 ?v0) ?v1) f1) (< (f20 f21 ?v1) (f20 f21 ?v0)))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (= (f22 (f23 f9 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (= (f3 (f24 (f25 f26 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f27 ?v0 ?v2)) (f10 f11 (f12 ?v2))) (f27 ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (= (f3 (f24 (f25 f28 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f27 ?v0 ?v2)) (f15 f16 ?v2)) (f27 ?v1 ?v2)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S4)) (= (= (f29 (f30 (f31 ?v0) ?v1) ?v2) f1) (and (= (f29 ?v0 ?v2) f1) (= (f29 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S2)) (= (= (f32 (f33 (f34 ?v0) ?v1) ?v2) f1) (and (= (f32 ?v0 ?v2) f1) (= (f32 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S13)) (= (= (f18 (f35 (f36 ?v0) ?v1) ?v2) f1) (and (= (f18 ?v0 ?v2) f1) (= (f18 ?v1 ?v2) f1)))))
(assert (not (= (f37 (f30 (f38 f39) (f40 (f41 f17) f42)) (f40 (f41 f14) f42)) f1)))
(assert (= (f37 (f30 (f38 f39) (f40 (f41 f17) f42)) (f40 (f41 f4) f42)) f1))
(assert (= (f43 f42) f1))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (=> (= (f37 ?v0 ?v1) f1) (=> (= (f37 ?v2 ?v0) f1) (= (f37 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S21) (?v1 S18) (?v2 S18) (?v3 S23)) (let ((?v_0 (f40 (f41 (f24 (f25 f28 ?v1) ?v2)) ?v3))) (=> (= (f37 (f30 (f38 ?v0) ?v_0) (f40 (f41 (f24 (f25 f26 ?v1) ?v2)) ?v3)) f1) (= (f37 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S2) (?v1 S16) (?v2 S16)) (=> (= (f22 (f23 (f13 (f15 f16 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f22 (f23 (f13 (f10 f11 (f12 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S16) (?v2 S16)) (=> (= (f22 (f23 (f13 (f10 f11 (f12 ?v0))) ?v1) ?v2) f1) (= (f22 (f23 (f13 (f15 f16 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S21) (?v1 S18) (?v2 S18) (?v3 S23)) (let ((?v_0 (f40 (f41 (f24 (f25 f28 ?v1) ?v2)) ?v3))) (=> (= (f44 (f30 (f38 ?v0) ?v_0) (f40 (f41 (f24 (f25 f26 ?v1) ?v2)) ?v3)) f1) (= (f44 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S23) (?v1 S3)) (=> (= (f43 ?v0) f1) (= (f45 (f40 (f41 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S21) (?v1 S27)) (=> (= (f45 ?v0) f1) (= (f43 (f46 (f47 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S29)) (=> (= (f48 ?v0) f1) (= (f43 (f49 (f50 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S23) (?v1 S31)) (=> (= (f43 ?v0) f1) (= (f48 (f51 (f52 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S33)) (=> (= (f48 ?v0) f1) (= (f48 (f35 (f53 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S34)) (=> (= (f48 ?v0) f1) (= (f45 (f54 (f55 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (or (= (f48 (f56 ?v0)) f1) (= (f48 (f56 ?v1)) f1)) (= (f48 (f56 (f35 (f36 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S23) (?v1 S23)) (=> (or (= (f43 (f57 ?v0)) f1) (= (f43 (f57 ?v1)) f1)) (= (f43 (f57 (f33 (f34 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S21) (?v1 S21)) (=> (or (= (f45 (f58 ?v0)) f1) (= (f45 (f58 ?v1)) f1)) (= (f45 (f58 (f30 (f31 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S21)) (=> (= (f59 ?v0 (f30 (f38 ?v1) ?v2)) f1) (=> (=> (= (f59 ?v0 ?v1) f1) false) (=> (=> (= (f59 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S14)) (=> (= (f60 ?v0 (f35 (f61 ?v1) ?v2)) f1) (=> (=> (= (f60 ?v0 ?v1) f1) false) (=> (=> (= (f60 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S23)) (=> (= (f62 ?v0 (f33 (f63 ?v1) ?v2)) f1) (=> (=> (= (f62 ?v0 ?v1) f1) false) (=> (=> (= (f62 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S4)) (=> (= (f29 (f30 (f38 ?v0) ?v1) ?v2) f1) (=> (=> (= (f29 ?v0 ?v2) f1) false) (=> (=> (= (f29 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S2)) (=> (= (f32 (f33 (f63 ?v0) ?v1) ?v2) f1) (=> (=> (= (f32 ?v0 ?v2) f1) false) (=> (=> (= (f32 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S21) (?v1 S4) (?v2 S21)) (=> (=> (not (= (f29 ?v0 ?v1) f1)) (= (f29 ?v2 ?v1) f1)) (= (f29 (f30 (f38 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S23)) (=> (=> (not (= (f32 ?v0 ?v1) f1)) (= (f32 ?v2 ?v1) f1)) (= (f32 (f33 (f63 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S21)) (=> (=> (not (= (f59 ?v0 ?v1) f1)) (= (f59 ?v0 ?v2) f1)) (= (f59 ?v0 (f30 (f38 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S14)) (=> (=> (not (= (f60 ?v0 ?v1) f1)) (= (f60 ?v0 ?v2) f1)) (= (f60 ?v0 (f35 (f61 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S23)) (=> (=> (not (= (f62 ?v0 ?v1) f1)) (= (f62 ?v0 ?v2) f1)) (= (f62 ?v0 (f33 (f63 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S23)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f62 ?v2 ?v3) f1) (= (f59 ?v0 (f40 (f41 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S13) (?v1 S33) (?v2 S13) (?v3 S14)) (=> (= ?v0 (f64 ?v1 ?v2)) (=> (= (f60 ?v2 ?v3) f1) (= (f60 ?v0 (f35 (f53 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S34) (?v2 S13) (?v3 S14)) (=> (= ?v0 (f65 ?v1 ?v2)) (=> (= (f60 ?v2 ?v3) f1) (= (f59 ?v0 (f54 (f55 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S13) (?v1 S31) (?v2 S2) (?v3 S23)) (=> (= ?v0 (f66 ?v1 ?v2)) (=> (= (f62 ?v2 ?v3) f1) (= (f60 ?v0 (f51 (f52 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S13) (?v1 S36) (?v2 S4) (?v3 S21)) (=> (= ?v0 (f67 ?v1 ?v2)) (=> (= (f59 ?v2 ?v3) f1) (= (f60 ?v0 (f68 (f69 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S27) (?v2 S4) (?v3 S21)) (=> (= ?v0 (f70 ?v1 ?v2)) (=> (= (f59 ?v2 ?v3) f1) (= (f62 ?v0 (f46 (f47 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S29) (?v2 S13) (?v3 S14)) (=> (= ?v0 (f71 ?v1 ?v2)) (=> (= (f60 ?v2 ?v3) f1) (= (f62 ?v0 (f49 (f50 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S2) (?v3 S6)) (let ((?v_0 (f7 f8 ?v1))) (= (= (f29 (f72 ?v0) (f5 (f6 ?v_0 (f10 f11 (f12 ?v2))) ?v3)) f1) (= (f29 (f72 (f73 f74 (+ (f20 f21 ?v0) 1))) (f5 (f6 ?v_0 (f15 f16 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S39) (?v1 S6) (?v2 S8) (?v3 S6)) (= (f67 (f75 f76 ?v0) (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) (f73 f74 0))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f44 ?v0 ?v1) f1) (forall ((?v2 S13)) (=> (forall ((?v3 S4)) (=> (= (f59 ?v3 ?v0) f1) (= (f29 (f72 ?v2) ?v3) f1))) (forall ((?v3 S4)) (=> (= (f59 ?v3 ?v1) f1) (= (f29 (f72 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S13) (?v1 S4)) (=> (= (f29 (f72 (f73 f74 (+ (f20 f21 ?v0) 1))) ?v1) f1) (= (f29 (f72 ?v0) ?v1) f1))))
(assert (forall ((?v0 S21) (?v1 S13)) (=> (forall ((?v2 S4)) (=> (= (f59 ?v2 ?v0) f1) (= (f29 (f72 (f73 f74 (+ (f20 f21 ?v1) 1))) ?v2) f1))) (forall ((?v2 S4)) (=> (= (f59 ?v2 ?v0) f1) (= (f29 (f72 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S23) (?v1 S29) (?v2 S13)) (=> (= ?v0 (f49 (f50 ?v1) (f56 (f19 ?v2)))) (= (f43 ?v0) f1))))
(assert (forall ((?v0 S21) (?v1 S34) (?v2 S13)) (=> (= ?v0 (f54 (f55 ?v1) (f56 (f19 ?v2)))) (= (f45 ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S33) (?v2 S13)) (=> (= ?v0 (f35 (f53 ?v1) (f56 (f19 ?v2)))) (= (f48 ?v0) f1))))
(assert (forall ((?v0 S21) (?v1 S21)) (=> (= (f37 ?v0 ?v1) f1) (= (f44 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S4) (?v3 S3)) (=> (= (f62 ?v0 ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f59 ?v2 (f40 (f41 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S13) (?v3 S33)) (=> (= (f60 ?v0 ?v1) f1) (=> (= ?v2 (f64 ?v3 ?v0)) (= (f60 ?v2 (f35 (f53 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S4) (?v3 S34)) (=> (= (f60 ?v0 ?v1) f1) (=> (= ?v2 (f65 ?v3 ?v0)) (= (f59 ?v2 (f54 (f55 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S13) (?v3 S31)) (=> (= (f62 ?v0 ?v1) f1) (=> (= ?v2 (f66 ?v3 ?v0)) (= (f60 ?v2 (f51 (f52 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S13) (?v3 S36)) (=> (= (f59 ?v0 ?v1) f1) (=> (= ?v2 (f67 ?v3 ?v0)) (= (f60 ?v2 (f68 (f69 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S2) (?v3 S27)) (=> (= (f59 ?v0 ?v1) f1) (=> (= ?v2 (f70 ?v3 ?v0)) (= (f62 ?v2 (f46 (f47 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S2) (?v3 S29)) (=> (= (f60 ?v0 ?v1) f1) (=> (= ?v2 (f71 ?v3 ?v0)) (= (f62 ?v2 (f49 (f50 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S3)) (=> (= (f62 ?v0 ?v1) f1) (= (f59 (f3 ?v2 ?v0) (f40 (f41 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S33)) (=> (= (f60 ?v0 ?v1) f1) (= (f60 (f64 ?v2 ?v0) (f35 (f53 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S34)) (=> (= (f60 ?v0 ?v1) f1) (= (f59 (f65 ?v2 ?v0) (f54 (f55 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S31)) (=> (= (f62 ?v0 ?v1) f1) (= (f60 (f66 ?v2 ?v0) (f51 (f52 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S36)) (=> (= (f59 ?v0 ?v1) f1) (= (f60 (f67 ?v2 ?v0) (f68 (f69 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S27)) (=> (= (f59 ?v0 ?v1) f1) (= (f62 (f70 ?v2 ?v0) (f46 (f47 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S29)) (=> (= (f60 ?v0 ?v1) f1) (= (f62 (f71 ?v2 ?v0) (f49 (f50 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S23)) (= (= (f59 ?v0 (f40 (f41 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f62 ?v3 ?v2) f1) (= ?v0 (f3 ?v1 ?v3)))))))
(assert (forall ((?v0 S13) (?v1 S33) (?v2 S14)) (= (= (f60 ?v0 (f35 (f53 ?v1) ?v2)) f1) (exists ((?v3 S13)) (and (= (f60 ?v3 ?v2) f1) (= ?v0 (f64 ?v1 ?v3)))))))
(assert (forall ((?v0 S4) (?v1 S34) (?v2 S14)) (= (= (f59 ?v0 (f54 (f55 ?v1) ?v2)) f1) (exists ((?v3 S13)) (and (= (f60 ?v3 ?v2) f1) (= ?v0 (f65 ?v1 ?v3)))))))
(assert (forall ((?v0 S13) (?v1 S31) (?v2 S23)) (= (= (f60 ?v0 (f51 (f52 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f62 ?v3 ?v2) f1) (= ?v0 (f66 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S27) (?v2 S21)) (= (= (f62 ?v0 (f46 (f47 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f59 ?v3 ?v2) f1) (= ?v0 (f70 ?v1 ?v3)))))))
(assert (forall ((?v0 S13) (?v1 S36) (?v2 S21)) (= (= (f60 ?v0 (f68 (f69 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f59 ?v3 ?v2) f1) (= ?v0 (f67 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S29) (?v2 S14)) (= (= (f62 ?v0 (f49 (f50 ?v1) ?v2)) f1) (exists ((?v3 S13)) (and (= (f60 ?v3 ?v2) f1) (= ?v0 (f71 ?v1 ?v3)))))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S21)) (=> (= (f59 ?v0 ?v1) f1) (= (f59 ?v0 (f30 (f38 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S14)) (=> (= (f60 ?v0 ?v1) f1) (= (f60 ?v0 (f35 (f61 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S23)) (=> (= (f62 ?v0 ?v1) f1) (= (f62 ?v0 (f33 (f63 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S21) (?v2 S21)) (=> (= (f59 ?v0 ?v1) f1) (= (f59 ?v0 (f30 (f38 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S14)) (=> (= (f60 ?v0 ?v1) f1) (= (f60 ?v0 (f35 (f61 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S23)) (=> (= (f62 ?v0 ?v1) f1) (= (f62 ?v0 (f33 (f63 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S21) (?v1 S4) (?v2 S21)) (=> (= (f29 ?v0 ?v1) f1) (= (f29 (f30 (f38 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S23)) (=> (= (f32 ?v0 ?v1) f1) (= (f32 (f33 (f63 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S21) (?v1 S4) (?v2 S21)) (=> (= (f29 ?v0 ?v1) f1) (= (f29 (f30 (f38 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S23)) (=> (= (f32 ?v0 ?v1) f1) (= (f32 (f33 (f63 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (= (forall ((?v3 S4)) (=> (= (f59 ?v3 (f30 (f38 ?v0) ?v1)) f1) (= (f29 ?v2 ?v3) f1))) (and (forall ((?v3 S4)) (=> (= (f59 ?v3 ?v0) f1) (= (f29 ?v2 ?v3) f1))) (forall ((?v3 S4)) (=> (= (f59 ?v3 ?v1) f1) (= (f29 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (forall ((?v3 S13)) (=> (= (f60 ?v3 (f35 (f61 ?v0) ?v1)) f1) (= (f18 ?v2 ?v3) f1))) (and (forall ((?v3 S13)) (=> (= (f60 ?v3 ?v0) f1) (= (f18 ?v2 ?v3) f1))) (forall ((?v3 S13)) (=> (= (f60 ?v3 ?v1) f1) (= (f18 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (= (forall ((?v3 S2)) (=> (= (f62 ?v3 (f33 (f63 ?v0) ?v1)) f1) (= (f32 ?v2 ?v3) f1))) (and (forall ((?v3 S2)) (=> (= (f62 ?v3 ?v0) f1) (= (f32 ?v2 ?v3) f1))) (forall ((?v3 S2)) (=> (= (f62 ?v3 ?v1) f1) (= (f32 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (= (exists ((?v3 S4)) (and (= (f59 ?v3 (f30 (f38 ?v0) ?v1)) f1) (= (f29 ?v2 ?v3) f1))) (or (exists ((?v3 S4)) (and (= (f59 ?v3 ?v0) f1) (= (f29 ?v2 ?v3) f1))) (exists ((?v3 S4)) (and (= (f59 ?v3 ?v1) f1) (= (f29 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (exists ((?v3 S13)) (and (= (f60 ?v3 (f35 (f61 ?v0) ?v1)) f1) (= (f18 ?v2 ?v3) f1))) (or (exists ((?v3 S13)) (and (= (f60 ?v3 ?v0) f1) (= (f18 ?v2 ?v3) f1))) (exists ((?v3 S13)) (and (= (f60 ?v3 ?v1) f1) (= (f18 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (= (exists ((?v3 S2)) (and (= (f62 ?v3 (f33 (f63 ?v0) ?v1)) f1) (= (f32 ?v2 ?v3) f1))) (or (exists ((?v3 S2)) (and (= (f62 ?v3 ?v0) f1) (= (f32 ?v2 ?v3) f1))) (exists ((?v3 S2)) (and (= (f62 ?v3 ?v1) f1) (= (f32 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21)) (let ((?v_0 (f38 ?v0))) (= (f30 (f38 (f30 ?v_0 ?v1)) ?v2) (f30 ?v_0 (f30 (f38 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f63 ?v0))) (= (f33 (f63 (f33 ?v_0 ?v1)) ?v2) (f33 ?v_0 (f33 (f63 ?v1) ?v2))))))
(assert (forall ((?v0 S13)) (= (f73 f74 (f20 f21 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f20 f21 (f73 f74 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f20 f21 (f73 f74 ?v0)) 0))))
(check-sat)
(exit)

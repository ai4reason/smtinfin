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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S5 S3) S1)
(declare-fun f7 (S2) S5)
(declare-fun f8 (S7 S6) S1)
(declare-fun f9 (S8 S7) S7)
(declare-fun f10 (S6) S8)
(declare-fun f11 (S9 S7) S1)
(declare-fun f12 (S6) S9)
(declare-fun f13 (S2) S4)
(declare-fun f14 (S6) S8)
(declare-fun f15 () S3)
(declare-fun f16 () S7)
(declare-fun f17 (S3) S5)
(declare-fun f18 () S3)
(declare-fun f19 (S2) S4)
(declare-fun f20 (S10 S11) S2)
(declare-fun f21 () S10)
(declare-fun f22 (S12 S6) S11)
(declare-fun f23 () S12)
(declare-fun f24 () S6)
(declare-fun f25 () S3)
(declare-fun f26 (S13 S14) S11)
(declare-fun f27 () S13)
(declare-fun f28 (S15 S6) S14)
(declare-fun f29 () S15)
(declare-fun f30 (S6) S8)
(declare-fun f31 () S7)
(declare-fun f32 (S17 S16) S2)
(declare-fun f33 (S18 S11) S17)
(declare-fun f34 (S19 S16) S18)
(declare-fun f35 () S19)
(declare-fun f36 () S1)
(declare-fun f37 (S3) S3)
(declare-fun f38 (S7) S7)
(declare-fun f39 (S21 S20) S1)
(declare-fun f40 (S16 S20) S21)
(declare-fun f41 (S3) S5)
(declare-fun f42 (S22 S3) S2)
(declare-fun f43 () S22)
(declare-fun f44 (S23 S7) S6)
(declare-fun f45 () S23)
(declare-fun f46 (S24) S3)
(declare-fun f47 (S25 Int) S24)
(declare-fun f48 () S25)
(declare-fun f49 (S26 S24) Int)
(declare-fun f50 () S26)
(declare-fun f51 (S28 S2) S24)
(declare-fun f52 (S29 S27) S28)
(declare-fun f53 () S29)
(declare-fun f54 () S11)
(declare-fun f55 (S30 S11) S11)
(declare-fun f56 (S31 S11) S30)
(declare-fun f57 () S31)
(declare-fun f58 () S28)
(declare-fun f59 (S11 S20) S21)
(declare-fun f60 (S11 S20 S24 S20) S1)
(declare-fun f61 () S1)
(declare-fun f62 (S15) S7)
(declare-fun f63 (S11) S1)
(declare-fun f64 (S32) S4)
(declare-fun f65 (S33) S8)
(declare-fun f66 (S32 S22) S1)
(declare-fun f67 (S33 S23) S1)
(declare-fun f68 (S7) S1)
(declare-fun f69 (S35 S27) S11)
(declare-fun f70 (S36 S6) S35)
(declare-fun f71 (S37 S34) S36)
(declare-fun f72 () S37)
(declare-fun f73 (S3) S1)
(declare-fun f74 (S38 S2) S2)
(declare-fun f75 (S32 S2) S38)
(declare-fun f76 (S39 S6) S6)
(declare-fun f77 (S33 S6) S39)
(declare-fun f78 (S32 S22) S1)
(declare-fun f79 (S33 S23) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 (f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (= (= (f8 (f9 (f10 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f11 (f12 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f13 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (= (= (f8 (f9 (f14 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f8 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f15 ?v0) f1) false)))
(assert (forall ((?v0 S6)) (= (= (f8 f16 ?v0) f1) false)))
(assert (not (= (f6 (f17 f18) (f4 (f19 (f20 f21 (f22 f23 f24))) f25)) f1)))
(assert (= (f6 (f17 (f4 (f19 (f20 f21 (f22 f23 f24))) f18)) (f4 (f19 (f20 f21 (f26 f27 (f28 f29 f24)))) f25)) f1))
(assert (forall ((?v0 S3)) (= (f6 (f17 ?v0) f25) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v2))) (=> (= (f6 (f17 ?v0) ?v1) f1) (=> (= (f6 ?v_0 ?v0) f1) (= (f6 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f17 ?v0)) (?v_1 (f19 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 f25)) f1) (=> (= (f6 ?v_0 ?v2) f1) (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f17 ?v0)) (?v_1 (f19 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f6 ?v_0 (f4 ?v_1 f25)) f1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f19 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 (f9 (f30 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f11 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (=> (not (= (f6 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v_0 (f4 (f19 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (let ((?v_0 (f12 ?v0))) (=> (=> (not (= (f11 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f11 ?v_0 (f9 (f30 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6)) (=> (= (f11 (f12 ?v0) f31) f1) false)))
(assert (forall ((?v0 S2)) (=> (= (f6 (f7 ?v0) f25) f1) false)))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S6) (?v3 S16)) (let ((?v_0 (f17 ?v0)) (?v_1 (f34 f35 ?v1))) (=> (= (f6 ?v_0 (f4 (f19 (f32 (f33 ?v_1 (f26 f27 (f28 f29 ?v2))) ?v3)) f25)) f1) (= (f6 ?v_0 (f4 (f19 (f32 (f33 ?v_1 (f22 f23 ?v2)) ?v3)) f25)) f1)))))
(assert (forall ((?v0 S16) (?v1 S6) (?v2 S16) (?v3 S3)) (let ((?v_0 (f34 f35 ?v0))) (let ((?v_1 (f19 (f32 (f33 ?v_0 (f22 f23 ?v1)) ?v2)))) (=> (= (f6 (f17 (f4 ?v_1 ?v3)) (f4 (f19 (f32 (f33 ?v_0 (f26 f27 (f28 f29 ?v1))) ?v2)) f25)) f1) (= (f6 (f17 ?v3) (f4 ?v_1 f25)) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f25 (f4 (f19 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (not (= f31 (f9 (f30 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f19 ?v0) ?v1) f25))))
(assert (forall ((?v0 S6) (?v1 S7)) (not (= (f9 (f30 ?v0) ?v1) f31))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 (f7 ?v0) (f4 (f19 ?v1) f25)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f11 (f12 ?v0) (f9 (f30 ?v1) f31)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f19 ?v0) (f4 (f19 ?v1) f25)) (f4 (f19 ?v2) (f4 (f19 ?v3) f25))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (= (f9 (f30 ?v0) (f9 (f30 ?v1) f31)) (f9 (f30 ?v2) (f9 (f30 ?v3) f31))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 (f7 ?v0) (f4 (f19 ?v1) f25)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f12 ?v0) (f9 (f30 ?v1) f31)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f19 ?v0) f25) (f4 (f19 ?v1) f25)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f9 (f30 ?v0) f31) (f9 (f30 ?v1) f31)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (= (= (f3 f25 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S6)) (= (= (f8 f31 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S16) (?v1 S11) (?v2 S16) (?v3 S16) (?v4 S11) (?v5 S16)) (= (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) (f32 (f33 (f34 f35 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= ?v0 f31) (not (= (f11 (f12 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f25) (not (= (f6 (f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f37 ?v0) f25) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (= (f38 ?v0) f31) (forall ((?v1 S6)) (not (= (f8 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (= (f11 (f12 ?v0) f31) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f6 (f7 ?v0) f25) f1) false)))
(assert (forall ((?v0 S3)) (= (= f25 (f37 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (= f31 (f38 ?v0)) (forall ((?v1 S6)) (not (= (f8 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (forall ((?v1 S6)) (=> (= (f11 (f12 ?v1) f31) f1) (= (f8 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) f25) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S7)) (= (exists ((?v1 S6)) (and (= (f11 (f12 ?v1) f31) f1) (= (f8 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 (f7 ?v1) f25) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S7)) (= (exists ((?v1 S6)) (= (f11 (f12 ?v1) ?v0) f1)) (not (= ?v0 f31)))))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 (f7 ?v1) ?v0) f1)) (not (= ?v0 f25)))))
(assert (forall ((?v0 S7)) (= (forall ((?v1 S6)) (not (= (f11 (f12 ?v1) ?v0) f1))) (= ?v0 f31))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 (f7 ?v1) ?v0) f1))) (= ?v0 f25))))
(assert (= f25 (f37 f15)))
(assert (= f31 (f38 f16)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f19 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f11 (f12 ?v0) ?v1) f1) (= (f9 (f30 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (= (f6 ?v_0 (f4 (f19 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (= (f11 ?v_0 (f9 (f30 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0)) (?v_1 (f19 ?v0))) (=> (not (= (f6 ?v_0 ?v1) f1)) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f12 ?v0)) (?v_1 (f30 ?v0))) (=> (not (= (f11 ?v_0 ?v1) f1)) (=> (not (= (f11 ?v_0 ?v2) f1)) (= (= (f9 ?v_1 ?v1) (f9 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f19 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (= (= (f8 (f9 (f30 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f8 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f19 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (= (= (f11 ?v_0 (f9 (f30 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f11 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f19 ?v0)) (?v_0 (f19 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (let ((?v_1 (f30 ?v0)) (?v_0 (f30 ?v1))) (= (f9 ?v_1 (f9 ?v_0 ?v2)) (f9 ?v_0 (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f19 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (let ((?v_0 (f30 ?v0))) (let ((?v_1 (f9 ?v_0 ?v1))) (= (f9 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f19 ?v0) (f37 ?v1)) (f37 (f4 (f13 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f9 (f30 ?v0) (f38 ?v1)) (f38 (f9 (f14 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f19 ?v0) ?v1) (f37 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f9 (f30 ?v0) ?v1) (f38 (f9 (f10 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 (f7 ?v0) (f4 (f19 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f11 (f12 ?v0) (f9 (f30 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2)) (= (= (f3 f25 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S6)) (= (= (f8 f31 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S11) (?v3 S16) (?v4 S16)) (let ((?v_0 (f17 ?v0))) (=> (= (f6 ?v_0 (f4 (f19 (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) f25)) f1) (=> (forall ((?v5 S20) (?v6 S20)) (=> (= (f39 (f40 ?v4 ?v5) ?v6) f1) (= (f39 (f40 ?v1 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f19 (f32 (f33 (f34 f35 ?v4) ?v2) ?v3)) f25)) f1))))))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S11) (?v3 S16) (?v4 S16)) (let ((?v_0 (f17 ?v0)) (?v_1 (f33 (f34 f35 ?v1) ?v2))) (=> (= (f6 ?v_0 (f4 (f19 (f32 ?v_1 ?v3)) f25)) f1) (=> (forall ((?v5 S20) (?v6 S20)) (=> (= (f39 (f40 ?v3 ?v5) ?v6) f1) (= (f39 (f40 ?v4 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f19 (f32 ?v_1 ?v4)) f25)) f1))))))
(assert (forall ((?v0 S11) (?v1 S16) (?v2 S16)) (let ((?v_0 (f17 f25)) (?v_1 (f4 (f19 (f32 (f33 (f34 f35 ?v1) ?v0) ?v2)) f25))) (=> (= (f6 ?v_0 (f4 (f19 (f20 f21 ?v0)) f25)) f1) (=> (= (f6 (f41 f25) ?v_1) f1) (= (f6 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S2)) (= (f42 f43 (f4 (f19 ?v0) f25)) ?v0)))
(assert (forall ((?v0 S6)) (= (f44 f45 (f9 (f30 ?v0) f31)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S11) (?v3 S16) (?v4 S16) (?v5 S16)) (let ((?v_0 (f17 ?v0))) (=> (= (f6 ?v_0 (f4 (f19 (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) f25)) f1) (=> (forall ((?v6 S20) (?v7 S20)) (=> (= (f39 (f40 ?v4 ?v6) ?v7) f1) (forall ((?v8 S20)) (=> (forall ((?v9 S20)) (=> (= (f39 (f40 ?v1 ?v9) ?v7) f1) (= (f39 (f40 ?v3 ?v9) ?v8) f1))) (= (f39 (f40 ?v5 ?v6) ?v8) f1))))) (= (f6 ?v_0 (f4 (f19 (f32 (f33 (f34 f35 ?v4) ?v2) ?v5)) f25)) f1))))))
(assert (forall ((?v0 S24) (?v1 S16) (?v2 S6) (?v3 S16)) (let ((?v_0 (f34 f35 ?v1))) (= (= (f3 (f46 ?v0) (f32 (f33 ?v_0 (f26 f27 (f28 f29 ?v2))) ?v3)) f1) (= (f3 (f46 (f47 f48 (+ (f49 f50 ?v0) 1))) (f32 (f33 ?v_0 (f22 f23 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S27) (?v1 S16) (?v2 S11) (?v3 S16)) (= (f51 (f52 f53 ?v0) (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) (f47 f48 0))))
(assert (forall ((?v0 S3) (?v1 S16)) (= (f6 (f17 ?v0) (f4 (f19 (f32 (f33 (f34 f35 ?v1) f54) ?v1)) f25)) f1)))
(assert (forall ((?v0 S24) (?v1 S2)) (=> (= (f3 (f46 (f47 f48 (+ (f49 f50 ?v0) 1))) ?v1) f1) (= (f3 (f46 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S24)) (=> (forall ((?v2 S2)) (=> (= (f6 (f7 ?v2) ?v0) f1) (= (f3 (f46 (f47 f48 (+ (f49 f50 ?v1) 1))) ?v2) f1))) (forall ((?v2 S2)) (=> (= (f6 (f7 ?v2) ?v0) f1) (= (f3 (f46 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f41 ?v0) ?v1) f1) (forall ((?v2 S24)) (=> (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v0) f1) (= (f3 (f46 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v1) f1) (= (f3 (f46 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f6 (f17 ?v0) ?v1) f1) (= (f6 (f41 ?v0) ?v1) f1))))
(assert (forall ((?v0 S16) (?v1 S6) (?v2 S16)) (= (f3 (f46 (f47 f48 0)) (f32 (f33 (f34 f35 ?v0) (f22 f23 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S6)) (not (= f54 (f22 f23 ?v0)))))
(assert (forall ((?v0 S6)) (not (= (f22 f23 ?v0) f54))))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S11) (?v3 S16) (?v4 S11) (?v5 S16)) (let ((?v_0 (f17 ?v0)) (?v_1 (f34 f35 ?v1))) (=> (= (f6 ?v_0 (f4 (f19 (f32 (f33 ?v_1 ?v2) ?v3)) f25)) f1) (=> (= (f6 ?v_0 (f4 (f19 (f32 (f33 (f34 f35 ?v3) ?v4) ?v5)) f25)) f1) (= (f6 ?v_0 (f4 (f19 (f32 (f33 ?v_1 (f55 (f56 f57 ?v2) ?v4)) ?v5)) f25)) f1))))))
(assert (forall ((?v0 S16) (?v1 S11) (?v2 S16)) (= (f51 f58 (f32 (f33 (f34 f35 ?v0) ?v1) ?v2)) (f47 f48 0))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S16) (?v2 S11) (?v3 S16)) (=> (= ?v0 (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f19 ?v0) ?v2)) (not (= (f6 (f7 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f11 (f12 ?v0) ?v1) f1) (exists ((?v2 S7)) (and (= ?v1 (f9 (f30 ?v0) ?v2)) (not (= (f11 (f12 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f19 ?v0) ?v2)) (=> (not (= (f6 (f7 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f11 (f12 ?v0) ?v1) f1) (=> (forall ((?v2 S7)) (=> (= ?v1 (f9 (f30 ?v0) ?v2)) (=> (not (= (f11 (f12 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S6)) (=> (= (f11 (f12 ?v1) ?v0) f1) false)) (= ?v0 f31))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) ?v0) f1) false)) (= ?v0 f25))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (= (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S6)) (not (= (f55 (f56 f57 ?v0) ?v1) (f22 f23 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S11) (?v2 S11)) (not (= (f22 f23 ?v0) (f55 (f56 f57 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= f54 (f55 (f56 f57 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= (f55 (f56 f57 ?v0) ?v1) f54))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f22 f23 ?v0) (f22 f23 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S16) (?v1 S3) (?v2 S11) (?v3 S16)) (=> (forall ((?v4 S20) (?v5 S20)) (=> (= (f39 (f40 ?v0 ?v4) ?v5) f1) (exists ((?v6 S16) (?v7 S16)) (and (= (f6 (f17 ?v1) (f4 (f19 (f32 (f33 (f34 f35 ?v6) ?v2) ?v7)) f25)) f1) (forall ((?v8 S20)) (=> (forall ((?v9 S20)) (=> (= (f39 (f40 ?v6 ?v9) ?v5) f1) (= (f39 (f40 ?v7 ?v9) ?v8) f1))) (= (f39 (f40 ?v3 ?v4) ?v8) f1))))))) (= (f6 (f17 ?v1) (f4 (f19 (f32 (f33 (f34 f35 ?v0) ?v2) ?v3)) f25)) f1))))
(assert (forall ((?v0 S6) (?v1 S20) (?v2 S20)) (=> (= (f39 (f59 (f26 f27 (f28 f29 ?v0)) ?v1) ?v2) f1) (= (f39 (f59 (f22 f23 ?v0) ?v1) ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S20) (?v2 S20)) (=> (= (f39 (f59 (f22 f23 ?v0) ?v1) ?v2) f1) (=> (=> (= (f39 (f59 (f26 f27 (f28 f29 ?v0)) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f25)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f19 ?v1) ?v2)) (not (= (f6 (f7 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S7)) (= (not (= ?v0 f31)) (exists ((?v1 S6) (?v2 S7)) (and (= ?v0 (f9 (f30 ?v1) ?v2)) (not (= (f11 (f12 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S6) (?v1 S20) (?v2 S24) (?v3 S20)) (=> (= (f60 (f26 f27 (f28 f29 ?v0)) ?v1 ?v2 ?v3) f1) (= (f60 (f22 f23 ?v0) ?v1 (f47 f48 (+ (f49 f50 ?v2) 1)) ?v3) f1))))
(assert (forall ((?v0 S6)) (= (= (f8 f31 ?v0) f1) (= (f11 (f12 ?v0) f31) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f25 ?v0) f1) (= (f6 (f7 ?v0) f25) f1))))
(assert (forall ((?v0 S3) (?v1 S11)) (=> (= f61 f1) (=> (forall ((?v2 S6)) (=> (= (f11 (f12 ?v2) (f62 f29)) f1) (= (f6 (f17 ?v0) (f4 (f19 (f20 f21 (f22 f23 ?v2))) f25)) f1))) (=> (= (f63 ?v1) f1) (= (f6 (f17 ?v0) (f4 (f19 (f20 f21 ?v1)) f25)) f1))))))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S24) (?v3 S20) (?v4 S11) (?v5 S20)) (=> (= (f60 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f60 ?v4 ?v3 ?v2 ?v5) f1) (= (f60 (f55 (f56 f57 ?v0) ?v4) ?v1 ?v2 ?v5) f1)))))
(assert (forall ((?v0 S20) (?v1 S24) (?v2 S20)) (=> (= (f60 f54 ?v0 ?v1 ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f11 (f12 ?v0) ?v1) f1) (= (f8 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S7)) (= (f38 ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f37 ?v0) ?v0)))
(assert (forall ((?v0 S20) (?v1 S24)) (= (f60 f54 ?v0 ?v1 ?v0) f1)))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S20) (?v3 S11) (?v4 S20)) (=> (= (f39 (f59 ?v0 ?v1) ?v2) f1) (=> (= (f39 (f59 ?v3 ?v2) ?v4) f1) (= (f39 (f59 (f55 (f56 f57 ?v0) ?v3) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f63 (f55 (f56 f57 ?v0) ?v1)) f1) (=> (=> (= (f63 ?v0) f1) (=> (= (f63 ?v1) f1) false)) false))))
(assert (forall ((?v0 S20) (?v1 S20)) (=> (= (f39 (f59 f54 ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S20)) (= (f39 (f59 f54 ?v0) ?v0) f1)))
(assert (=> (= (f63 f54) f1) (=> false false)))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S24) (?v3 S20) (?v4 S24)) (=> (= (f60 ?v0 ?v1 ?v2 ?v3) f1) (=> (<= (f49 f50 ?v2) (f49 f50 ?v4)) (= (f60 ?v0 ?v1 ?v4 ?v3) f1)))))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S24) (?v3 S20)) (=> (= (f60 ?v0 ?v1 ?v2 ?v3) f1) (= (f60 ?v0 ?v1 (f47 f48 (+ (f49 f50 ?v2) 1)) ?v3) f1))))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S24) (?v3 S20)) (=> (= (f60 ?v0 ?v1 ?v2 ?v3) f1) (= (f39 (f59 ?v0 ?v1) ?v3) f1))))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S20) (?v3 S20)) (let ((?v_0 (f59 ?v0 ?v1))) (=> (= (f39 ?v_0 ?v2) f1) (=> (= (f39 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S20)) (= (= (f39 (f59 ?v0 ?v1) ?v2) f1) (exists ((?v3 S24)) (= (f60 ?v0 ?v1 ?v3 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f63 ?v0) f1) (=> (= (f63 ?v1) f1) (= (f63 (f55 (f56 f57 ?v0) ?v1)) f1)))))
(assert (= (f63 f54) f1))
(assert (forall ((?v0 S24) (?v1 S16) (?v2 S11) (?v3 S16)) (= (= (f3 (f46 ?v0) (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S20) (?v5 S20)) (=> (= (f39 (f40 ?v1 ?v4) ?v5) f1) (forall ((?v6 S20)) (=> (= (f60 ?v2 ?v5 ?v0 ?v6) f1) (= (f39 (f40 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S6) (?v1 S20) (?v2 S24) (?v3 S20)) (=> (= (f60 (f22 f23 ?v0) ?v1 ?v2 ?v3) f1) (=> (forall ((?v4 S24)) (=> (= ?v2 (f47 f48 (+ (f49 f50 ?v4) 1))) (=> (= (f60 (f26 f27 (f28 f29 ?v0)) ?v1 ?v4 ?v3) f1) false))) false))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S20) (?v3 S20)) (=> (= (f39 (f59 (f55 (f56 f57 ?v0) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S20)) (=> (= (f39 (f59 ?v0 ?v2) ?v4) f1) (=> (= (f39 (f59 ?v1 ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S20) (?v3 S24) (?v4 S20)) (=> (= (f60 (f55 (f56 f57 ?v0) ?v1) ?v2 ?v3 ?v4) f1) (=> (forall ((?v5 S20)) (=> (= (f60 ?v0 ?v2 ?v3 ?v5) f1) (=> (= (f60 ?v1 ?v5 ?v3 ?v4) f1) false))) false))))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S20)) (=> (= (f39 (f59 ?v0 ?v1) ?v2) f1) (exists ((?v3 S24)) (= (f60 ?v0 ?v1 ?v3 ?v2) f1)))))
(assert (=> (= f61 f1) (forall ((?v0 S20)) (=> (forall ((?v1 S20)) (= ?v1 ?v0)) false))))
(assert (= (= f61 f1) (exists ((?v0 S20) (?v1 S20)) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S11) (?v1 S20) (?v2 S24) (?v3 S20) (?v4 S11) (?v5 S20) (?v6 S24) (?v7 S20)) (=> (= (f60 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f60 ?v4 ?v5 ?v6 ?v7) f1) (exists ((?v8 S24)) (and (= (f60 ?v0 ?v1 ?v8 ?v3) f1) (= (f60 ?v4 ?v5 ?v8 ?v7) f1)))))))
(assert (forall ((?v0 S32) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f64 ?v0) (f4 (f19 ?v1) f25)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S33) (?v1 S6) (?v2 S6)) (= (= (f8 (f9 (f65 ?v0) (f9 (f30 ?v1) f31)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S32) (?v1 S22) (?v2 S2)) (=> (= (f66 ?v0 ?v1) f1) (= (f42 ?v1 (f4 (f19 ?v2) f25)) ?v2))))
(assert (forall ((?v0 S33) (?v1 S23) (?v2 S6)) (=> (= (f67 ?v0 ?v1) f1) (= (f44 ?v1 (f9 (f30 ?v2) f31)) ?v2))))
(assert (= (f68 (f62 f29)) f1))
(assert (forall ((?v0 S34) (?v1 S6) (?v2 S27)) (=> (= (f63 (f69 (f70 (f71 f72 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f63 (f22 f23 ?v1)) f1) false) false))))
(assert (= (f68 f31) f1))
(assert (= (f73 f25) f1))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f73 ?v0) f1) (= (f73 (f4 (f19 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= (f68 ?v0) f1) (= (f68 (f9 (f30 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S34) (?v1 S6) (?v2 S27) (?v3 S34) (?v4 S6) (?v5 S27)) (= (= (f69 (f70 (f71 f72 ?v0) ?v1) ?v2) (f69 (f70 (f71 f72 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f73 (f4 (f19 ?v0) ?v1)) f1) (= (f73 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f68 (f9 (f30 ?v0) ?v1)) f1) (= (f68 ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S22) (?v2 S3) (?v3 S2)) (=> (= (f66 ?v0 ?v1) f1) (=> (= (f73 ?v2) f1) (=> (not (= (f6 (f7 ?v3) ?v2) f1)) (=> (not (= ?v2 f25)) (= (f42 ?v1 (f4 (f19 ?v3) ?v2)) (f74 (f75 ?v0 ?v3) (f42 ?v1 ?v2)))))))))
(assert (forall ((?v0 S33) (?v1 S23) (?v2 S7) (?v3 S6)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f68 ?v2) f1) (=> (not (= (f11 (f12 ?v3) ?v2) f1)) (=> (not (= ?v2 f31)) (= (f44 ?v1 (f9 (f30 ?v3) ?v2)) (f76 (f77 ?v0 ?v3) (f44 ?v1 ?v2)))))))))
(assert (forall ((?v0 S6) (?v1 S34) (?v2 S6) (?v3 S27)) (not (= (f22 f23 ?v0) (f69 (f70 (f71 f72 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S34) (?v1 S6) (?v2 S27) (?v3 S6)) (not (= (f69 (f70 (f71 f72 ?v0) ?v1) ?v2) (f22 f23 ?v3)))))
(assert (forall ((?v0 S34) (?v1 S6) (?v2 S27) (?v3 S11) (?v4 S11)) (not (= (f69 (f70 (f71 f72 ?v0) ?v1) ?v2) (f55 (f56 f57 ?v3) ?v4)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S34) (?v3 S6) (?v4 S27)) (not (= (f55 (f56 f57 ?v0) ?v1) (f69 (f70 (f71 f72 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S34) (?v1 S6) (?v2 S27)) (not (= (f69 (f70 (f71 f72 ?v0) ?v1) ?v2) f54))))
(assert (forall ((?v0 S34) (?v1 S6) (?v2 S27)) (not (= f54 (f69 (f70 (f71 f72 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S32) (?v1 S2)) (=> (= (f3 (f4 (f64 ?v0) f25) ?v1) f1) false)))
(assert (forall ((?v0 S33) (?v1 S6)) (=> (= (f8 (f9 (f65 ?v0) f31) ?v1) f1) false)))
(assert (forall ((?v0 S32) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f64 ?v0) ?v1) ?v2) f1) (not (= ?v1 f25)))))
(assert (forall ((?v0 S33) (?v1 S7) (?v2 S6)) (=> (= (f8 (f9 (f65 ?v0) ?v1) ?v2) f1) (not (= ?v1 f31)))))
(assert (forall ((?v0 S6) (?v1 S34) (?v2 S27)) (=> (= (f63 (f22 f23 ?v0)) f1) (= (f63 (f69 (f70 (f71 f72 ?v1) ?v0) ?v2)) f1))))
(assert (forall ((?v0 S32) (?v1 S22) (?v2 S3)) (=> (= (f66 ?v0 ?v1) f1) (=> (= (f73 ?v2) f1) (=> (not (= ?v2 f25)) (=> (forall ((?v3 S2) (?v4 S2)) (= (f6 (f7 (f74 (f75 ?v0 ?v3) ?v4)) (f4 (f19 ?v3) (f4 (f19 ?v4) f25))) f1)) (= (f6 (f7 (f42 ?v1 ?v2)) ?v2) f1)))))))
(assert (forall ((?v0 S33) (?v1 S23) (?v2 S7)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f68 ?v2) f1) (=> (not (= ?v2 f31)) (=> (forall ((?v3 S6) (?v4 S6)) (= (f11 (f12 (f76 (f77 ?v0 ?v3) ?v4)) (f9 (f30 ?v3) (f9 (f30 ?v4) f31))) f1)) (= (f11 (f12 (f44 ?v1 ?v2)) ?v2) f1)))))))
(assert (forall ((?v0 S7) (?v1 S33)) (=> (= (f68 ?v0) f1) (=> (not (= ?v0 f31)) (exists ((?v2 S6)) (= (f8 (f9 (f65 ?v1) ?v0) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S32)) (=> (= (f73 ?v0) f1) (=> (not (= ?v0 f25)) (exists ((?v2 S2)) (= (f3 (f4 (f64 ?v1) ?v0) ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (= (f73 ?v0) f1) (or (= ?v0 f25) (exists ((?v1 S3) (?v2 S2)) (and (= ?v0 (f4 (f19 ?v2) ?v1)) (= (f73 ?v1) f1)))))))
(assert (forall ((?v0 S7)) (= (= (f68 ?v0) f1) (or (= ?v0 f31) (exists ((?v1 S7) (?v2 S6)) (and (= ?v0 (f9 (f30 ?v2) ?v1)) (= (f68 ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f73 ?v0) f1) (=> (= (f6 ?v1 f25) f1) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f73 ?v3) f1) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f19 ?v2) ?v3)) f1))))) (= (f6 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S7) (?v1 S9)) (=> (= (f68 ?v0) f1) (=> (= (f11 ?v1 f31) f1) (=> (forall ((?v2 S6) (?v3 S7)) (=> (= (f68 ?v3) f1) (=> (not (= (f11 (f12 ?v2) ?v3) f1)) (=> (= (f11 ?v1 ?v3) f1) (= (f11 ?v1 (f9 (f30 ?v2) ?v3)) f1))))) (= (f11 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S32) (?v1 S22) (?v2 S3) (?v3 S2)) (=> (= (f78 ?v0 ?v1) f1) (=> (= (f73 ?v2) f1) (=> (not (= ?v2 f25)) (= (f42 ?v1 (f4 (f19 ?v3) ?v2)) (f74 (f75 ?v0 ?v3) (f42 ?v1 ?v2))))))))
(assert (forall ((?v0 S33) (?v1 S23) (?v2 S7) (?v3 S6)) (=> (= (f79 ?v0 ?v1) f1) (=> (= (f68 ?v2) f1) (=> (not (= ?v2 f31)) (= (f44 ?v1 (f9 (f30 ?v3) ?v2)) (f76 (f77 ?v0 ?v3) (f44 ?v1 ?v2))))))))
(assert (forall ((?v0 S33) (?v1 S23) (?v2 S6)) (=> (= (f79 ?v0 ?v1) f1) (= (f76 (f77 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S32) (?v1 S22) (?v2 S2)) (=> (= (f78 ?v0 ?v1) f1) (= (f74 (f75 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S24)) (= (f47 f48 (f49 f50 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f49 f50 (f47 f48 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f49 f50 (f47 f48 ?v0)) 0))))
(check-sat)
(exit)

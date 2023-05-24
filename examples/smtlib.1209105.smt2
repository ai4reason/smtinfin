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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S5 S2) S4)
(declare-fun f6 () S5)
(declare-fun f7 (S6 S3) S1)
(declare-fun f8 (S7 S2) S6)
(declare-fun f9 () S7)
(declare-fun f10 () S5)
(declare-fun f11 () S3)
(declare-fun f12 (S8 S3) S6)
(declare-fun f13 () S8)
(declare-fun f14 () S3)
(declare-fun f15 () S5)
(declare-fun f16 (S9 S10) S2)
(declare-fun f17 (S11 S12) S9)
(declare-fun f18 (S13 S10) S11)
(declare-fun f19 () S13)
(declare-fun f20 () S10)
(declare-fun f21 () S12)
(declare-fun f22 () S10)
(declare-fun f23 () S3)
(declare-fun f24 (S16 S15) S1)
(declare-fun f25 (S10 S14) S16)
(declare-fun f26 () S10)
(declare-fun f27 () S10)
(declare-fun f28 (S18 S2) S19)
(declare-fun f29 (S20 S17) S18)
(declare-fun f30 () S20)
(declare-fun f31 (S21 Int) S19)
(declare-fun f32 () S21)
(declare-fun f33 () S4)
(declare-fun f34 (S22 S3) S2)
(declare-fun f35 () S22)
(declare-fun f36 () S1)
(declare-fun f37 (S23 S12) S12)
(declare-fun f38 (S24 S12) S23)
(declare-fun f39 () S24)
(declare-fun f40 () S18)
(declare-fun f41 () S8)
(declare-fun f42 (S26 S25) S4)
(declare-fun f43 () S26)
(declare-fun f44 () S8)
(declare-fun f45 (S27 S1) S1)
(declare-fun f46 (S28 S1) S27)
(declare-fun f47 () S28)
(declare-fun f48 (S29 S1) S3)
(declare-fun f49 () S28)
(declare-fun f50 (S30 S3) S4)
(declare-fun f51 () S30)
(declare-fun f52 () S28)
(declare-fun f53 () S30)
(declare-fun f54 (S31 S28) S28)
(declare-fun f55 () S31)
(declare-fun f56 (S32 S8) S30)
(declare-fun f57 () S32)
(declare-fun f58 (S33 S19) Int)
(declare-fun f59 () S33)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f7 (f8 f9 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f10 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f11 ?v0) f1) false)))
(assert (not (= (f7 (f12 f13 f14) (f4 (f5 f15 (f16 (f17 (f18 f19 f20) f21) f22)) f23)) f1)))
(assert (forall ((?v0 S14) (?v1 S15)) (=> (= (f24 (f25 f26 ?v0) ?v1) f1) (= (f24 (f25 f27 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (f7 (f12 f13 ?v0) f23) f1)))
(assert (forall ((?v0 S3) (?v1 S10)) (= (f7 (f12 f13 ?v0) (f4 (f5 f15 (f16 (f17 (f18 f19 ?v1) f21) ?v1)) f23)) f1)))
(assert (forall ((?v0 S10) (?v1 S12) (?v2 S10) (?v3 S10) (?v4 S12) (?v5 S10)) (= (= (f16 (f17 (f18 f19 ?v0) ?v1) ?v2) (f16 (f17 (f18 f19 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v2))) (=> (= (f7 (f12 f13 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f5 f15 ?v1))) (=> (= (f7 ?v_0 (f4 ?v_1 f23)) f1) (=> (= (f7 ?v_0 ?v2) f1) (= (f7 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f5 f15 ?v1))) (=> (= (f7 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f7 ?v_0 (f4 ?v_1 f23)) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S12) (?v3 S10) (?v4 S10)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f17 (f18 f19 ?v1) ?v2))) (=> (= (f7 ?v_0 (f4 (f5 f15 (f16 ?v_1 ?v3)) f23)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f24 (f25 ?v3 ?v5) ?v6) f1) (= (f24 (f25 ?v4 ?v5) ?v6) f1))) (= (f7 ?v_0 (f4 (f5 f15 (f16 ?v_1 ?v4)) f23)) f1))))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S12) (?v3 S10) (?v4 S10)) (let ((?v_0 (f12 f13 ?v0))) (=> (= (f7 ?v_0 (f4 (f5 f15 (f16 (f17 (f18 f19 ?v1) ?v2) ?v3)) f23)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f24 (f25 ?v4 ?v5) ?v6) f1) (= (f24 (f25 ?v1 ?v5) ?v6) f1))) (= (f7 ?v_0 (f4 (f5 f15 (f16 (f17 (f18 f19 ?v4) ?v2) ?v3)) f23)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 (f4 (f5 f15 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f7 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (=> (=> (not (= (f7 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f7 ?v_0 (f4 (f5 f15 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f7 (f8 f9 ?v0) f23) f1) false)))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S12) (?v3 S10) (?v4 S10) (?v5 S10)) (let ((?v_0 (f12 f13 ?v0))) (=> (= (f7 ?v_0 (f4 (f5 f15 (f16 (f17 (f18 f19 ?v1) ?v2) ?v3)) f23)) f1) (=> (forall ((?v6 S14) (?v7 S15)) (=> (= (f24 (f25 ?v4 ?v6) ?v7) f1) (forall ((?v8 S15)) (=> (forall ((?v9 S14)) (=> (= (f24 (f25 ?v1 ?v9) ?v7) f1) (= (f24 (f25 ?v3 ?v9) ?v8) f1))) (= (f24 (f25 ?v5 ?v6) ?v8) f1))))) (= (f7 ?v_0 (f4 (f5 f15 (f16 (f17 (f18 f19 ?v4) ?v2) ?v5)) f23)) f1))))))
(assert (forall ((?v0 S17) (?v1 S10) (?v2 S12) (?v3 S10)) (= (f28 (f29 f30 ?v0) (f16 (f17 (f18 f19 ?v1) ?v2) ?v3)) (f31 f32 0))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f23 (f4 (f5 f15 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f5 f15 ?v0) ?v1) f23))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 (f8 f9 ?v0) (f4 (f5 f15 ?v1) f23)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f23) (not (= (f7 (f8 f9 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f4 f33 ?v0) f23) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f7 (f8 f9 ?v0) f23) f1) false)))
(assert (forall ((?v0 S3)) (= (= f23 (f4 f33 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f7 (f8 f9 ?v1) f23) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f7 (f8 f9 ?v1) f23) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f7 (f8 f9 ?v1) ?v0) f1)) (not (= ?v0 f23)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f7 (f8 f9 ?v1) ?v0) f1))) (= ?v0 f23))))
(assert (= f23 (f4 f33 f11)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) f1) (= (f4 (f5 f15 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (= (f7 ?v_0 (f4 (f5 f15 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0)) (?v_1 (f5 f15 ?v0))) (=> (not (= (f7 ?v_0 ?v1) f1)) (=> (not (= (f7 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f15 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (= (f7 ?v_0 (f4 (f5 f15 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f5 f15 ?v0)) (?v_0 (f5 f15 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f5 f15 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f5 f15 ?v0) (f4 f33 ?v1)) (f4 f33 (f4 (f5 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f5 f15 ?v0) ?v1) (f4 f33 (f4 (f5 f6 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f7 (f8 f9 ?v0) (f4 (f5 f15 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f5 f15 ?v0) f23) (f4 (f5 f15 ?v1) f23)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f7 (f8 f9 ?v0) (f4 (f5 f15 ?v1) f23)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f5 f15 ?v0) (f4 (f5 f15 ?v1) f23)) (f4 (f5 f15 ?v2) (f4 (f5 f15 ?v3) f23))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2)) (= (f34 f35 (f4 (f5 f15 ?v0) f23)) ?v0)))
(assert (forall ((?v0 S2)) (= (= (f3 f23 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f23 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S12) (?v3 S10) (?v4 S12) (?v5 S10)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f18 f19 ?v1))) (=> (= (f7 ?v_0 (f4 (f5 f15 (f16 (f17 ?v_1 ?v2) ?v3)) f23)) f1) (=> (= (f7 ?v_0 (f4 (f5 f15 (f16 (f17 (f18 f19 ?v3) ?v4) ?v5)) f23)) f1) (= (f7 ?v_0 (f4 (f5 f15 (f16 (f17 ?v_1 (f37 (f38 f39 ?v2) ?v4)) ?v5)) f23)) f1))))))
(assert (forall ((?v0 S10) (?v1 S12) (?v2 S10)) (= (f28 f40 (f16 (f17 (f18 f19 ?v0) ?v1) ?v2)) (f31 f32 0))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S10) (?v2 S12) (?v3 S10)) (=> (= ?v0 (f16 (f17 (f18 f19 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f5 f15 ?v0) ?v2)) (=> (not (= (f7 (f8 f9 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f5 f15 ?v0) ?v2)) (not (= (f7 (f8 f9 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f7 (f8 f9 ?v1) ?v0) f1) false)) (= ?v0 f23))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S12) (?v3 S10)) (=> (forall ((?v4 S14) (?v5 S15)) (=> (= (f24 (f25 ?v0 ?v4) ?v5) f1) (exists ((?v6 S10) (?v7 S10)) (and (= (f7 (f12 f13 ?v1) (f4 (f5 f15 (f16 (f17 (f18 f19 ?v6) ?v2) ?v7)) f23)) f1) (forall ((?v8 S15)) (=> (forall ((?v9 S14)) (=> (= (f24 (f25 ?v6 ?v9) ?v5) f1) (= (f24 (f25 ?v7 ?v9) ?v8) f1))) (= (f24 (f25 ?v3 ?v4) ?v8) f1))))))) (= (f7 (f12 f13 ?v1) (f4 (f5 f15 (f16 (f17 (f18 f19 ?v0) ?v2) ?v3)) f23)) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (not (= f21 (f37 (f38 f39 ?v0) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (not (= (f37 (f38 f39 ?v0) ?v1) f21))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (= (= (f37 (f38 f39 ?v0) ?v1) (f37 (f38 f39 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f23)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f5 f15 ?v1) ?v2)) (not (= (f7 (f8 f9 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S2)) (= (= (f3 f23 ?v0) f1) (= (f7 (f8 f9 ?v0) f23) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f13 ?v0) ?v1) f1) (= (f7 (f12 f41 ?v0) ?v1) f1))))
(assert (forall ((?v0 S25) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f42 f43 ?v0) (f4 (f5 f15 ?v1) f23)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S3) (?v1 S2)) (let ((?v_0 (f4 (f5 f15 ?v1) f23))) (=> (= (f7 (f12 f44 ?v0) ?v_0) f1) (or (= ?v0 f23) (= ?v0 ?v_0))))))
(assert (forall ((?v0 S1)) (= (f45 (f46 f47 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f7 (f12 f44 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 (f12 f44 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (f7 (f12 f44 f23) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (=> (= (f45 (f46 f47 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f46 f47 ?v2))) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (f45 ?v_0 ?v0) f1) (= (f45 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f44 ?v2))) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (f45 (f46 f47 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 (f12 f44 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f46 f47 ?v0))) (=> (= (f45 ?v_0 ?v1) f1) (=> (= (f45 (f46 f47 ?v1) ?v2) f1) (= (f45 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f44 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f44 ?v1) ?v2) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (f45 (f46 f47 ?v1) ?v0) f1) (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 (f12 f44 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (= ?v0 f1) (= ?v2 f1)) (= (f45 (f46 f47 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f7 (f12 f44 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f46 f47 ?v0))) (=> (= (f45 ?v_0 ?v1) f1) (=> (= (= ?v1 f1) (= ?v2 f1)) (= (f45 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f44 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f46 f47 ?v2))) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f45 ?v_0 ?v1) f1) (= (f45 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f44 ?v2))) (=> (= ?v0 ?v1) (=> (= (f7 ?v_0 ?v1) f1) (= (f7 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f45 (f46 f47 ?v1) ?v2) f1) (= (f45 (f46 f47 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f7 (f12 f44 ?v1) ?v2) f1) (= (f7 (f12 f44 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (= (= (f45 (f46 f47 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (= (= (f7 (f12 f44 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (= (f45 (f46 f47 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (= (f45 (f46 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f7 (f12 f44 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f7 (f8 f9 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f4 f33 ?v0) ?v0)))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (= ?v0 f1) (= ?v1 f1)) (and (= (f45 (f46 f47 ?v0) ?v1) f1) (= (f45 (f46 f47 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f7 (f12 f44 ?v0) ?v1) f1) (= (f7 (f12 f44 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 (f12 f44 ?v0) ?v1) f1) (forall ((?v2 S2)) (= (f45 (f46 f47 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f7 (f12 f44 ?v0) ?v2) f1) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (=> (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 (f12 f44 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f44 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f44 ?v1) ?v2) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f44 ?v1) ?v2) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f7 (f12 f44 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f7 (f12 f44 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f7 (f12 f44 ?v0) ?v1) f1) (= (f7 (f12 f44 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (f7 (f12 f44 ?v0) ?v0) f1)))
(assert (forall ((?v0 S25) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f42 f43 ?v0) ?v1) ?v2) f1) (not (= ?v1 f23)))))
(assert (forall ((?v0 S25) (?v1 S2)) (=> (= (f3 (f4 (f42 f43 ?v0) f23) ?v1) f1) false)))
(assert (forall ((?v0 S3)) (=> (= (f7 (f12 f44 ?v0) f23) f1) (= ?v0 f23))))
(assert (forall ((?v0 S1)) (=> (= (f45 (f46 f47 ?v0) f36) f1) (= (= ?v0 f1) (= f36 f1)))))
(assert (forall ((?v0 S3)) (= (= (f7 (f12 f44 ?v0) f23) f1) (= ?v0 f23))))
(assert (forall ((?v0 S1)) (= (= (f45 (f46 f47 ?v0) f36) f1) (= (= ?v0 f1) (= f36 f1)))))
(assert (forall ((?v0 S3)) (= (f7 (f12 f44 f23) ?v0) f1)))
(assert (forall ((?v0 S1)) (= (f45 (f46 f47 f36) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (= (f7 (f12 f44 ?v0) f23) f1) (= ?v0 f23))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f5 f15 ?v2))) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (= (f7 (f12 f44 (f4 ?v_0 ?v0)) (f4 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f12 f44 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (= (f7 ?v_0 (f4 (f5 f15 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f44 ?v1))) (=> (not (= (f7 (f8 f9 ?v0) ?v1) f1)) (= (= (f7 ?v_0 (f4 (f5 f15 ?v0) ?v2)) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (= (f7 (f12 f44 (f4 (f5 f15 ?v0) ?v1)) ?v2) f1) (and (= (f7 (f8 f9 ?v0) ?v2) f1) (= (f7 (f12 f44 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f7 (f12 f44 ?v0) (f4 (f5 f15 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f7 (f12 f13 ?v0) ?v1) f1) (=> (= (f7 (f12 f44 ?v0) ?v2) f1) (= (f7 (f12 f13 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f44 ?v2) ?v1) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (= (f7 (f12 f13 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1)))) (= (f7 (f12 f44 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (= (f45 (f46 f47 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)) (= (f7 (f12 f44 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (=> (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1))) (= (f7 (f12 f44 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (=> (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1))) (= (f7 (f12 f44 (f4 f33 ?v0)) (f4 f33 ?v1)) f1))))
(assert (forall ((?v0 S29) (?v1 S1) (?v2 S3) (?v3 S1)) (=> (= (f7 (f12 f44 (f48 ?v0 ?v1)) ?v2) f1) (=> (= (f45 (f46 f47 ?v3) ?v1) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v5) ?v4) f1) (= (f7 (f12 f44 (f48 ?v0 ?v5)) (f48 ?v0 ?v4)) f1))) (= (f7 (f12 f44 (f48 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S1) (?v3 S3)) (=> (= (f45 (f46 f47 (f7 ?v0 ?v1)) ?v2) f1) (=> (= (f7 (f12 f44 ?v3) ?v1) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v5) ?v4) f1) (= (f45 (f46 f47 (f7 ?v0 ?v5)) (f7 ?v0 ?v4)) f1))) (= (f45 (f46 f47 (f7 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S27) (?v2 S1) (?v3 S1)) (=> (= (= ?v0 f1) (= (f45 ?v1 ?v2) f1)) (=> (= (f45 (f46 f47 ?v3) ?v2) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v5) ?v4) f1) (= (f45 (f46 f47 (f45 ?v1 ?v5)) (f45 ?v1 ?v4)) f1))) (= (f45 (f46 f47 (f45 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3) (?v3 S3)) (=> (= ?v0 (f4 ?v1 ?v2)) (=> (= (f7 (f12 f44 ?v3) ?v2) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v5) ?v4) f1) (= (f7 (f12 f44 (f4 ?v1 ?v5)) (f4 ?v1 ?v4)) f1))) (= (f7 (f12 f44 (f4 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S29) (?v2 S1) (?v3 S1)) (let ((?v_0 (f12 f44 ?v0))) (=> (= (f7 ?v_0 (f48 ?v1 ?v2)) f1) (=> (= (f45 (f46 f47 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v4) ?v5) f1) (= (f7 (f12 f44 (f48 ?v1 ?v4)) (f48 ?v1 ?v5)) f1))) (= (f7 ?v_0 (f48 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S6) (?v2 S3) (?v3 S3)) (let ((?v_0 (f46 f47 ?v0))) (=> (= (f45 ?v_0 (f7 ?v1 ?v2)) f1) (=> (= (f7 (f12 f44 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v4) ?v5) f1) (= (f45 (f46 f47 (f7 ?v1 ?v4)) (f7 ?v1 ?v5)) f1))) (= (f45 ?v_0 (f7 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (forall ((?v2 S1)) (= (f45 (f46 f47 ?v0) ?v2) f1)) (= (= (f45 (f46 f49 ?v1) ?v0) f1) (= ?v1 f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S3)) (= (f7 (f12 f44 ?v0) ?v2) f1)) (= (f4 (f50 f51 ?v1) ?v0) ?v1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (forall ((?v2 S1)) (= (f45 (f46 f47 ?v0) ?v2) f1)) (= (= (f45 (f46 f49 ?v0) ?v1) f1) (= ?v1 f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S3)) (= (f7 (f12 f44 ?v0) ?v2) f1)) (= (f4 (f50 f51 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (forall ((?v2 S1)) (= (f45 (f46 f47 ?v0) ?v2) f1)) (= (= (f45 (f46 f52 ?v1) ?v0) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S3)) (= (f7 (f12 f44 ?v0) ?v2) f1)) (= (f4 (f50 f53 ?v1) ?v0) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (forall ((?v2 S1)) (= (f45 (f46 f47 ?v0) ?v2) f1)) (= (= (f45 (f46 f52 ?v0) ?v1) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S3)) (= (f7 (f12 f44 ?v0) ?v2) f1)) (= (f4 (f50 f53 ?v0) ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S6) (?v2 S3) (?v3 S3)) (=> (= (= ?v0 f1) (= (f7 ?v1 ?v2) f1)) (=> (= (f7 (f12 f44 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v4) ?v5) f1) (= (f45 (f46 f47 (f7 ?v1 ?v4)) (f7 ?v1 ?v5)) f1))) (= (f45 (f46 f47 ?v0) (f7 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S29) (?v2 S1) (?v3 S1)) (=> (= ?v0 (f48 ?v1 ?v2)) (=> (= (f45 (f46 f47 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v4) ?v5) f1) (= (f7 (f12 f44 (f48 ?v1 ?v4)) (f48 ?v1 ?v5)) f1))) (= (f7 (f12 f44 ?v0) (f48 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6) (?v3 S1)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f45 (f46 f47 (f7 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v4) ?v5) f1) (= (f45 (f46 f47 (f7 ?v2 ?v4)) (f7 ?v2 ?v5)) f1))) (= (f45 (f46 f47 (f7 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S29) (?v3 S3)) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (f7 (f12 f44 (f48 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v4) ?v5) f1) (= (f7 (f12 f44 (f48 ?v2 ?v4)) (f48 ?v2 ?v5)) f1))) (= (f7 (f12 f44 (f48 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6) (?v3 S1)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (= (f7 ?v2 ?v1) f1) (= ?v3 f1)) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v4) ?v5) f1) (= (f45 (f46 f47 (f7 ?v2 ?v4)) (f7 ?v2 ?v5)) f1))) (= (f45 (f46 f47 (f7 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S29) (?v3 S3)) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (f48 ?v2 ?v1) ?v3) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v4) ?v5) f1) (= (f7 (f12 f44 (f48 ?v2 ?v4)) (f48 ?v2 ?v5)) f1))) (= (f7 (f12 f44 (f48 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S27) (?v3 S1)) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (= (f45 ?v2 ?v0) f1) (= ?v3 f1)) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v5) ?v4) f1) (= (f45 (f46 f47 (f45 ?v2 ?v5)) (f45 ?v2 ?v4)) f1))) (= (f45 (f46 f47 ?v3) (f45 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4) (?v3 S3)) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f4 ?v2 ?v0) ?v3) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v5) ?v4) f1) (= (f7 (f12 f44 (f4 ?v2 ?v5)) (f4 ?v2 ?v4)) f1))) (= (f7 (f12 f44 ?v3) (f4 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S1) (?v3 S6)) (let ((?v_0 (f46 f47 ?v2))) (=> (= (f7 (f12 f44 ?v0) ?v1) f1) (=> (= (f45 ?v_0 (f7 ?v3 ?v0)) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f44 ?v5) ?v4) f1) (= (f45 (f46 f47 (f7 ?v3 ?v5)) (f7 ?v3 ?v4)) f1))) (= (f45 ?v_0 (f7 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S3) (?v3 S29)) (let ((?v_0 (f12 f44 ?v2))) (=> (= (f45 (f46 f47 ?v0) ?v1) f1) (=> (= (f7 ?v_0 (f48 ?v3 ?v0)) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f45 (f46 f47 ?v5) ?v4) f1) (= (f7 (f12 f44 (f48 ?v3 ?v5)) (f48 ?v3 ?v4)) f1))) (= (f7 ?v_0 (f48 ?v3 ?v1)) f1)))))))
(assert (= f49 (f54 f55 f47)))
(assert (= f51 (f56 f57 f44)))
(assert (forall ((?v0 S19)) (= (f31 f32 (f58 f59 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f58 f59 (f31 f32 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f58 f59 (f31 f32 ?v0)) 0))))
(check-sat)
(exit)

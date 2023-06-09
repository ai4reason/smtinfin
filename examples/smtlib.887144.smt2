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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S6 S5) S1)
(declare-fun f7 (S7 S5) S6)
(declare-fun f8 () S7)
(declare-fun f9 () S4)
(declare-fun f10 () S7)
(declare-fun f11 (S8 S9) S7)
(declare-fun f12 () S8)
(declare-fun f13 () S9)
(declare-fun f14 (S10 S5) S7)
(declare-fun f15 () S10)
(declare-fun f16 (S11 S7) S10)
(declare-fun f17 () S11)
(declare-fun f18 () S8)
(declare-fun f19 (S12 S7) S7)
(declare-fun f20 (S13 S1) S12)
(declare-fun f21 () S13)
(declare-fun f22 () S3)
(declare-fun f23 (S14 S3) S1)
(declare-fun f24 (S15 S3) S14)
(declare-fun f25 () S15)
(declare-fun f26 () S3)
(declare-fun f27 (S16 S3) S3)
(declare-fun f28 (S17 S2) S16)
(declare-fun f29 () S17)
(declare-fun f30 (S18 S9) S2)
(declare-fun f31 () S18)
(declare-fun f32 () S3)
(declare-fun f33 () S1)
(declare-fun f34 (S19 S7) S2)
(declare-fun f35 (S20 S9) S19)
(declare-fun f36 (S21 S7) S20)
(declare-fun f37 () S21)
(declare-fun f38 (S22 S2) S14)
(declare-fun f39 () S22)
(declare-fun f40 (S24 S2) S25)
(declare-fun f41 (S26 S23) S24)
(declare-fun f42 () S26)
(declare-fun f43 (S27 Int) S25)
(declare-fun f44 () S27)
(declare-fun f45 () S16)
(declare-fun f46 (S28 S25) Int)
(declare-fun f47 () S28)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f6 (f7 f8 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f9 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f6 (f7 f10 ?v0) ?v1) f1) (forall ((?v2 S5)) (=> (= (f6 (f7 (f11 f12 f13) ?v1) ?v2) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (= (f6 (f7 (f14 f15 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S5)) (= (f7 (f14 (f16 f17 ?v0) ?v1) ?v2) (f7 ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S5) (?v2 S5)) (= (= (f6 (f7 (f11 f18 ?v0) ?v1) ?v2) f1) (forall ((?v3 S5)) (=> (= (f6 (f7 (f11 f12 ?v0) ?v2) ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S1) (?v1 S7) (?v2 S5) (?v3 S5)) (= (= (f6 (f7 (f19 (f20 f21 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f6 (f7 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f22 ?v0) f1) false)))
(assert (not (= (f23 (f24 f25 f26) (f27 (f28 f29 (f30 f31 f13)) f32)) f1)))
(assert (= f33 f1))
(assert (= (f23 (f24 f25 f26) (f27 (f28 f29 (f34 (f35 (f36 f37 f10) f13) f8)) f32)) f1))
(assert (forall ((?v0 S3)) (= (f23 (f24 f25 ?v0) f32) f1)))
(assert (forall ((?v0 S9)) (= (f30 f31 ?v0) (f34 (f35 (f36 f37 f8) ?v0) (f11 f12 ?v0)))))
(assert (forall ((?v0 S7) (?v1 S9) (?v2 S7) (?v3 S7) (?v4 S9) (?v5 S7)) (= (= (f34 (f35 (f36 f37 ?v0) ?v1) ?v2) (f34 (f35 (f36 f37 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f25 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f24 f25 ?v0)) (?v_1 (f28 f29 ?v1))) (=> (= (f23 ?v_0 (f27 ?v_1 f32)) f1) (=> (= (f23 ?v_0 ?v2) f1) (= (f23 ?v_0 (f27 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f24 f25 ?v0)) (?v_1 (f28 f29 ?v1))) (=> (= (f23 ?v_0 (f27 ?v_1 ?v2)) f1) (and (= (f23 ?v_0 (f27 ?v_1 f32)) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S9)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 (f27 (f28 f29 (f30 f31 ?v1)) f32)) f1) (= (f23 ?v_0 (f27 (f28 f29 (f34 (f35 (f36 f37 (f11 f18 ?v1)) ?v1) f8)) f32)) f1)))))
(assert (forall ((?v0 S1) (?v1 S3) (?v2 S7) (?v3 S9) (?v4 S7)) (let ((?v_0 (f24 f25 ?v1))) (=> (=> (= ?v0 f1) (= (f23 ?v_0 (f27 (f28 f29 (f34 (f35 (f36 f37 ?v2) ?v3) ?v4)) f32)) f1)) (= (f23 ?v_0 (f27 (f28 f29 (f34 (f35 (f36 f37 (f19 (f20 f21 ?v0) ?v2)) ?v3) ?v4)) f32)) f1)))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S9) (?v3 S7)) (=> (forall ((?v4 S5) (?v5 S5)) (=> (= (f6 (f7 ?v0 ?v4) ?v5) f1) (= (f23 (f24 f25 ?v1) (f27 (f28 f29 (f34 (f35 (f36 f37 (f14 f15 ?v5)) ?v2) (f14 (f16 f17 ?v3) ?v4))) f32)) f1))) (= (f23 (f24 f25 ?v1) (f27 (f28 f29 (f34 (f35 (f36 f37 ?v0) ?v2) ?v3)) f32)) f1))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (let ((?v_0 (f24 f25 ?v0)) (?v_1 (f35 (f36 f37 ?v1) ?v2))) (=> (= (f23 ?v_0 (f27 (f28 f29 (f34 ?v_1 ?v3)) f32)) f1) (=> (forall ((?v5 S5) (?v6 S5)) (=> (= (f6 (f7 ?v3 ?v5) ?v6) f1) (= (f6 (f7 ?v4 ?v5) ?v6) f1))) (= (f23 ?v_0 (f27 (f28 f29 (f34 ?v_1 ?v4)) f32)) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 (f27 (f28 f29 (f34 (f35 (f36 f37 ?v1) ?v2) ?v3)) f32)) f1) (=> (forall ((?v5 S5) (?v6 S5)) (=> (= (f6 (f7 ?v4 ?v5) ?v6) f1) (= (f6 (f7 ?v1 ?v5) ?v6) f1))) (= (f23 ?v_0 (f27 (f28 f29 (f34 (f35 (f36 f37 ?v4) ?v2) ?v3)) f32)) f1))))))
(assert (= (= f33 f1) (exists ((?v0 S5) (?v1 S5)) (not (= ?v0 ?v1)))))
(assert (=> (= f33 f1) (forall ((?v0 S5)) (=> (forall ((?v1 S5)) (= ?v1 ?v0)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f23 ?v_0 (f27 (f28 f29 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f23 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f38 f39 ?v0))) (=> (=> (not (= (f23 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f23 ?v_0 (f27 (f28 f29 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7) (?v5 S7)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 (f27 (f28 f29 (f34 (f35 (f36 f37 ?v1) ?v2) ?v3)) f32)) f1) (=> (forall ((?v6 S5) (?v7 S5)) (=> (= (f6 (f7 ?v4 ?v6) ?v7) f1) (forall ((?v8 S5)) (=> (forall ((?v9 S5)) (=> (= (f6 (f7 ?v1 ?v9) ?v7) f1) (= (f6 (f7 ?v3 ?v9) ?v8) f1))) (= (f6 (f7 ?v5 ?v6) ?v8) f1))))) (= (f23 ?v_0 (f27 (f28 f29 (f34 (f35 (f36 f37 ?v4) ?v2) ?v5)) f32)) f1))))))
(assert (forall ((?v0 S2)) (=> (= (f23 (f38 f39 ?v0) f32) f1) false)))
(assert (forall ((?v0 S23) (?v1 S7) (?v2 S9) (?v3 S7)) (= (f40 (f41 f42 ?v0) (f34 (f35 (f36 f37 ?v1) ?v2) ?v3)) (f43 f44 0))))
(assert (forall ((?v0 S2)) (= (f27 f45 (f4 f5 ?v0)) (f27 (f28 f29 ?v0) f32))))
(assert (forall ((?v0 S2)) (= (f27 f45 (f4 f9 ?v0)) (f27 (f28 f29 ?v0) f32))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f32) (not (= (f23 (f38 f39 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f27 f45 ?v0) f32) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f23 (f38 f39 ?v0) f32) f1) false)))
(assert (forall ((?v0 S3)) (= (= f32 (f27 f45 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f23 (f38 f39 ?v1) f32) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f23 (f38 f39 ?v1) f32) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f23 (f38 f39 ?v1) ?v0) f1)) (not (= ?v0 f32)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f23 (f38 f39 ?v1) ?v0) f1))) (= ?v0 f32))))
(assert (= f32 (f27 f45 f22)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f23 (f38 f39 ?v0) ?v1) f1) (= (f27 (f28 f29 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 (f27 (f28 f29 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f38 f39 ?v0)) (?v_1 (f28 f29 ?v0))) (=> (not (= (f23 ?v_0 ?v1) f1)) (=> (not (= (f23 ?v_0 ?v2) f1)) (= (= (f27 ?v_1 ?v1) (f27 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S25)) (= (f43 f44 (f46 f47 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f46 f47 (f43 f44 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f46 f47 (f43 f44 ?v0)) 0))))
(check-sat)
(exit)

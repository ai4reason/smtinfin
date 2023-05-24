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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S2 S3) S1)
(declare-fun f7 (S2) S4)
(declare-fun f8 () S3)
(declare-fun f9 (S6 S5) S1)
(declare-fun f10 (S7 S5) S6)
(declare-fun f11 () S7)
(declare-fun f12 (S8 S5) S6)
(declare-fun f13 () S8)
(declare-fun f14 () S7)
(declare-fun f15 (S3 S3) S1)
(declare-fun f16 () S3)
(declare-fun f17 (S2) S4)
(declare-fun f18 (S9 S7) S2)
(declare-fun f19 (S10 S8) S9)
(declare-fun f20 (S11 S7) S10)
(declare-fun f21 () S11)
(declare-fun f22 (S13 S2) S14)
(declare-fun f23 (S15 S12) S13)
(declare-fun f24 () S15)
(declare-fun f25 (S16 Int) S14)
(declare-fun f26 () S16)
(declare-fun f27 (S3) S3)
(declare-fun f28 (S17 S3) S2)
(declare-fun f29 () S17)
(declare-fun f30 () S1)
(declare-fun f31 () S13)
(declare-fun f32 (S18) S4)
(declare-fun f33 (S18 S17) S1)
(declare-fun f34 (S14) S3)
(declare-fun f35 (S3 S3) S1)
(declare-fun f36 (S19 S18) S17)
(declare-fun f37 () S19)
(declare-fun f38 (S20 S14) Int)
(declare-fun f39 () S20)
(declare-fun f40 () S8)
(declare-fun f41 (S21 S8) S8)
(declare-fun f42 (S22 S8) S21)
(declare-fun f43 () S22)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f7 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f8 ?v0) f1) false)))
(assert (not (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (forall ((?v2 S5)) (=> (forall ((?v3 S5)) (=> (= ?v3 ?v1) (= (f9 (f12 f13 ?v3) ?v2) f1))) (= (f9 (f10 f14 ?v0) ?v2) f1)))))))
(assert (= (f15 f16 (f4 (f17 (f18 (f19 (f20 f21 f11) f13) f14)) f16)) f1))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S7) (?v3 S7) (?v4 S8) (?v5 S7)) (= (= (f18 (f19 (f20 f21 ?v0) ?v1) ?v2) (f18 (f19 (f20 f21 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f6 ?v0 (f4 (f17 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f6 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v0 (f4 (f17 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2)) (=> (= (f6 ?v0 f16) f1) false)))
(assert (forall ((?v0 S12) (?v1 S7) (?v2 S8) (?v3 S7)) (= (f22 (f23 f24 ?v0) (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) (f25 f26 0))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f16 (f4 (f17 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f17 ?v0) ?v1) f16))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 ?v0 (f4 (f17 ?v1) f16)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f17 ?v0) (f4 (f17 ?v1) f16)) (f4 (f17 ?v2) (f4 (f17 ?v3) f16))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 ?v0 (f4 (f17 ?v1) f16)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f17 ?v0) f16) (f4 (f17 ?v1) f16)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f16) (not (= (f6 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f27 ?v0) f16) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f6 ?v0 f16) f1) false)))
(assert (forall ((?v0 S3)) (= (= f16 (f27 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 ?v1 f16) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 ?v1 f16) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 ?v1 ?v0) f1)) (not (= ?v0 f16)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 ?v1 ?v0) f1))) (= ?v0 f16))))
(assert (= f16 (f27 f8)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (= (f4 (f17 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f6 ?v0 ?v1) f1) (= (f6 ?v0 (f4 (f17 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v0))) (=> (not (= (f6 ?v0 ?v1) f1)) (=> (not (= (f6 ?v0 ?v2) f1)) (= (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f17 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f6 ?v0 (f4 (f17 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f17 ?v0)) (?v_0 (f17 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f17 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f17 ?v0) (f27 ?v1)) (f27 (f4 (f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f17 ?v0) ?v1) (f27 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 ?v0 (f4 (f17 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2)) (= (f28 f29 (f4 (f17 ?v0) f16)) ?v0)))
(assert (forall ((?v0 S2)) (= (= (f3 f16 ?v0) f1) (= f30 f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f16 ?v0) f1) (= f30 f1))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S7)) (= (f22 f31 (f18 (f19 (f20 f21 ?v0) ?v1) ?v2)) (f25 f26 0))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S7) (?v2 S8) (?v3 S7)) (=> (= ?v0 (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f17 ?v0) ?v2)) (=> (not (= (f6 ?v0 ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f17 ?v0) ?v2)) (not (= (f6 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 ?v1 ?v0) f1) false)) (= ?v0 f16))))
(assert (forall ((?v0 S8) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f12 ?v0 ?v1))) (=> (= (f9 ?v_0 ?v2) f1) (=> (= (f9 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f16)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f17 ?v1) ?v2)) (not (= (f6 ?v1 ?v2) f1)))))))
(assert (forall ((?v0 S2)) (= (= (f3 f16 ?v0) f1) (= (f6 ?v0 f16) f1))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f32 ?v0) (f4 (f17 ?v1) f16)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S18) (?v1 S17) (?v2 S2)) (=> (= (f33 ?v0 ?v1) f1) (= (f28 ?v1 (f4 (f17 ?v2) f16)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 ?v0 ?v1) f1) (forall ((?v2 S14)) (=> (forall ((?v3 S2)) (=> (= (f6 ?v3 ?v0) f1) (= (f3 (f34 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f6 ?v3 ?v1) f1) (= (f3 (f34 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S8) (?v3 S7) (?v4 S7)) (let ((?v_0 (f19 (f20 f21 ?v1) ?v2))) (=> (= (f35 ?v0 (f4 (f17 (f18 ?v_0 ?v3)) f16)) f1) (=> (forall ((?v5 S5) (?v6 S5)) (=> (= (f9 (f10 ?v3 ?v5) ?v6) f1) (= (f9 (f10 ?v4 ?v5) ?v6) f1))) (= (f35 ?v0 (f4 (f17 (f18 ?v_0 ?v4)) f16)) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S8) (?v3 S7) (?v4 S7)) (=> (= (f35 ?v0 (f4 (f17 (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) f16)) f1) (=> (forall ((?v5 S5) (?v6 S5)) (=> (= (f9 (f10 ?v4 ?v5) ?v6) f1) (= (f9 (f10 ?v1 ?v5) ?v6) f1))) (= (f35 ?v0 (f4 (f17 (f18 (f19 (f20 f21 ?v4) ?v2) ?v3)) f16)) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f17 ?v1))) (=> (= (f35 ?v0 (f4 ?v_0 f16)) f1) (=> (= (f35 ?v0 ?v2) f1) (= (f35 ?v0 (f4 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f17 ?v1))) (=> (= (f35 ?v0 (f4 ?v_0 ?v2)) f1) (and (= (f35 ?v0 (f4 ?v_0 f16)) f1) (= (f35 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S2)) (= (f28 (f36 f37 ?v0) (f4 (f17 ?v1) f16)) ?v1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f35 ?v2 ?v0) f1) (= (f35 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S14)) (=> (forall ((?v2 S2)) (=> (= (f6 ?v2 ?v0) f1) (= (f3 (f34 (f25 f26 (+ (f38 f39 ?v1) 1))) ?v2) f1))) (forall ((?v2 S2)) (=> (= (f6 ?v2 ?v0) f1) (= (f3 (f34 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S2)) (=> (= (f3 (f34 (f25 f26 (+ (f38 f39 ?v0) 1))) ?v1) f1) (= (f3 (f34 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (f35 ?v0 f16) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f35 ?v0 ?v1) f1) (= (f15 ?v0 ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f32 ?v0) ?v1) ?v2) f1) (not (= ?v1 f16)))))
(assert (forall ((?v0 S18) (?v1 S2)) (=> (= (f3 (f4 (f32 ?v0) f16) ?v1) f1) false)))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S2)) (=> (= ?v0 (f36 f37 ?v1)) (= (f28 ?v0 (f4 (f17 ?v2) f16)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S8) (?v3 S7) (?v4 S7) (?v5 S7)) (=> (= (f35 ?v0 (f4 (f17 (f18 (f19 (f20 f21 ?v1) ?v2) ?v3)) f16)) f1) (=> (forall ((?v6 S5) (?v7 S5)) (=> (= (f9 (f10 ?v4 ?v6) ?v7) f1) (forall ((?v8 S5)) (=> (forall ((?v9 S5)) (=> (= (f9 (f10 ?v1 ?v9) ?v7) f1) (= (f9 (f10 ?v3 ?v9) ?v8) f1))) (= (f9 (f10 ?v5 ?v6) ?v8) f1))))) (= (f35 ?v0 (f4 (f17 (f18 (f19 (f20 f21 ?v4) ?v2) ?v5)) f16)) f1)))))
(assert (forall ((?v0 S3) (?v1 S7)) (= (f35 ?v0 (f4 (f17 (f18 (f19 (f20 f21 ?v1) f40) ?v1)) f16)) f1)))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S8) (?v3 S7) (?v4 S8) (?v5 S7)) (let ((?v_0 (f20 f21 ?v1))) (=> (= (f35 ?v0 (f4 (f17 (f18 (f19 ?v_0 ?v2) ?v3)) f16)) f1) (=> (= (f35 ?v0 (f4 (f17 (f18 (f19 (f20 f21 ?v3) ?v4) ?v5)) f16)) f1) (= (f35 ?v0 (f4 (f17 (f18 (f19 ?v_0 (f41 (f42 f43 ?v2) ?v4)) ?v5)) f16)) f1))))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S8) (?v3 S7)) (=> (forall ((?v4 S5) (?v5 S5)) (=> (= (f9 (f10 ?v0 ?v4) ?v5) f1) (exists ((?v6 S7) (?v7 S7)) (and (= (f35 ?v1 (f4 (f17 (f18 (f19 (f20 f21 ?v6) ?v2) ?v7)) f16)) f1) (forall ((?v8 S5)) (=> (forall ((?v9 S5)) (=> (= (f9 (f10 ?v6 ?v9) ?v5) f1) (= (f9 (f10 ?v7 ?v9) ?v8) f1))) (= (f9 (f10 ?v3 ?v4) ?v8) f1))))))) (= (f35 ?v1 (f4 (f17 (f18 (f19 (f20 f21 ?v0) ?v2) ?v3)) f16)) f1))))
(assert (forall ((?v0 S14)) (= (f25 f26 (f38 f39 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f38 f39 (f25 f26 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f38 f39 (f25 f26 ?v0)) 0))))
(check-sat)
(exit)

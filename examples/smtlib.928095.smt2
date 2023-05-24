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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S6 S5) S1)
(declare-fun f7 (S7 S6) S6)
(declare-fun f8 (S5) S7)
(declare-fun f9 (S5 S6) S1)
(declare-fun f10 (S5) S7)
(declare-fun f11 () S6)
(declare-fun f12 (S6 S6) S1)
(declare-fun f13 () S6)
(declare-fun f14 (S5) S7)
(declare-fun f15 (S8 S4) S5)
(declare-fun f16 (S9 S10) S8)
(declare-fun f17 (S11 S4) S9)
(declare-fun f18 () S11)
(declare-fun f19 () S4)
(declare-fun f20 () S10)
(declare-fun f21 () S4)
(declare-fun f22 (S10) S4)
(declare-fun f23 (S6 S6) S1)
(declare-fun f24 (S13 S5) S14)
(declare-fun f25 (S15 S12) S13)
(declare-fun f26 () S15)
(declare-fun f27 (S16 Int) S14)
(declare-fun f28 () S16)
(declare-fun f29 (S6) S6)
(declare-fun f30 (S17 S6) S5)
(declare-fun f31 () S17)
(declare-fun f32 () S1)
(declare-fun f33 () S10)
(declare-fun f34 (S18 S10) S10)
(declare-fun f35 (S19 S10) S18)
(declare-fun f36 () S19)
(declare-fun f37 () S13)
(declare-fun f38 (S14) S6)
(declare-fun f39 (S20 S14) Int)
(declare-fun f40 () S20)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f6 (f7 (f8 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f9 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f6 (f7 (f10 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f6 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5)) (= (= (f6 f11 ?v0) f1) false)))
(assert (not (= (f12 f13 (f7 (f14 (f15 (f16 (f17 f18 f19) f20) f21)) f13)) f1)))
(assert (= (f12 f13 (f7 (f14 (f15 (f16 (f17 f18 f5) f20) (f22 f20))) f13)) f1))
(assert (= (f23 f13 (f7 (f14 (f15 (f16 (f17 f18 f19) f20) f21)) f13)) f1))
(assert (forall ((?v0 S6)) (= (f12 ?v0 f13) f1)))
(assert (forall ((?v0 S4) (?v1 S10) (?v2 S4) (?v3 S4) (?v4 S10) (?v5 S4)) (= (= (f15 (f16 (f17 f18 ?v0) ?v1) ?v2) (f15 (f16 (f17 f18 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f12 ?v0 ?v1) f1) (= (f23 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f12 ?v0 ?v1) f1) (=> (= (f12 ?v2 ?v0) f1) (= (f12 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S5) (?v2 S6)) (let ((?v_0 (f14 ?v1))) (=> (= (f12 ?v0 (f7 ?v_0 f13)) f1) (=> (= (f12 ?v0 ?v2) f1) (= (f12 ?v0 (f7 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S6) (?v1 S5) (?v2 S6)) (let ((?v_0 (f14 ?v1))) (=> (= (f12 ?v0 (f7 ?v_0 ?v2)) f1) (and (= (f12 ?v0 (f7 ?v_0 f13)) f1) (= (f12 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S10) (?v3 S4) (?v4 S4)) (let ((?v_0 (f16 (f17 f18 ?v1) ?v2))) (=> (= (f12 ?v0 (f7 (f14 (f15 ?v_0 ?v3)) f13)) f1) (=> (forall ((?v5 S2) (?v6 S2)) (=> (= (f3 (f4 ?v3 ?v5) ?v6) f1) (= (f3 (f4 ?v4 ?v5) ?v6) f1))) (= (f12 ?v0 (f7 (f14 (f15 ?v_0 ?v4)) f13)) f1))))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S10) (?v3 S4) (?v4 S4)) (=> (= (f12 ?v0 (f7 (f14 (f15 (f16 (f17 f18 ?v1) ?v2) ?v3)) f13)) f1) (=> (forall ((?v5 S2) (?v6 S2)) (=> (= (f3 (f4 ?v4 ?v5) ?v6) f1) (= (f3 (f4 ?v1 ?v5) ?v6) f1))) (= (f12 ?v0 (f7 (f14 (f15 (f16 (f17 f18 ?v4) ?v2) ?v3)) f13)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (=> (= (f9 ?v0 (f7 (f14 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f9 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (=> (=> (not (= (f9 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f9 ?v0 (f7 (f14 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S10) (?v3 S4) (?v4 S4) (?v5 S4)) (=> (= (f12 ?v0 (f7 (f14 (f15 (f16 (f17 f18 ?v1) ?v2) ?v3)) f13)) f1) (=> (forall ((?v6 S2) (?v7 S2)) (=> (= (f3 (f4 ?v4 ?v6) ?v7) f1) (forall ((?v8 S2)) (=> (forall ((?v9 S2)) (=> (= (f3 (f4 ?v1 ?v9) ?v7) f1) (= (f3 (f4 ?v3 ?v9) ?v8) f1))) (= (f3 (f4 ?v5 ?v6) ?v8) f1))))) (= (f12 ?v0 (f7 (f14 (f15 (f16 (f17 f18 ?v4) ?v2) ?v5)) f13)) f1)))))
(assert (forall ((?v0 S5)) (=> (= (f9 ?v0 f13) f1) false)))
(assert (forall ((?v0 S12) (?v1 S4) (?v2 S10) (?v3 S4)) (= (f24 (f25 f26 ?v0) (f15 (f16 (f17 f18 ?v1) ?v2) ?v3)) (f27 f28 0))))
(assert (forall ((?v0 S5) (?v1 S6)) (not (= f13 (f7 (f14 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (not (= (f7 (f14 ?v0) ?v1) f13))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f9 ?v0 (f7 (f14 ?v1) f13)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S5)) (=> (= ?v0 f13) (not (= (f9 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6)) (= (= (f29 ?v0) f13) (forall ((?v1 S5)) (not (= (f6 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S5)) (= (= (f9 ?v0 f13) f1) false)))
(assert (forall ((?v0 S6)) (= (= f13 (f29 ?v0)) (forall ((?v1 S5)) (not (= (f6 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (forall ((?v1 S5)) (=> (= (f9 ?v1 f13) f1) (= (f6 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S6)) (= (exists ((?v1 S5)) (and (= (f9 ?v1 f13) f1) (= (f6 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S6)) (= (exists ((?v1 S5)) (= (f9 ?v1 ?v0) f1)) (not (= ?v0 f13)))))
(assert (forall ((?v0 S6)) (= (forall ((?v1 S5)) (not (= (f9 ?v1 ?v0) f1))) (= ?v0 f13))))
(assert (= f13 (f29 f11)))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f9 ?v0 ?v1) f1) (= (f7 (f14 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (=> (= (f9 ?v0 ?v1) f1) (= (f9 ?v0 (f7 (f14 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6)) (let ((?v_0 (f14 ?v0))) (=> (not (= (f9 ?v0 ?v1) f1)) (=> (not (= (f9 ?v0 ?v2) f1)) (= (= (f7 ?v_0 ?v1) (f7 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f6 (f7 (f14 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f6 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (= (= (f9 ?v0 (f7 (f14 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f9 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (let ((?v_1 (f14 ?v0)) (?v_0 (f14 ?v1))) (= (f7 ?v_1 (f7 ?v_0 ?v2)) (f7 ?v_0 (f7 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S6)) (let ((?v_0 (f14 ?v0))) (let ((?v_1 (f7 ?v_0 ?v1))) (= (f7 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f7 (f14 ?v0) (f29 ?v1)) (f29 (f7 (f10 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f7 (f14 ?v0) ?v1) (f29 (f7 (f8 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f9 ?v0 (f7 (f14 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f7 (f14 ?v0) f13) (f7 (f14 ?v1) f13)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 ?v0 (f7 (f14 ?v1) f13)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (= (= (f7 (f14 ?v0) (f7 (f14 ?v1) f13)) (f7 (f14 ?v2) (f7 (f14 ?v3) f13))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S5)) (= (f30 f31 (f7 (f14 ?v0) f13)) ?v0)))
(assert (forall ((?v0 S5)) (= (= (f6 f13 ?v0) f1) (= f32 f1))))
(assert (forall ((?v0 S5)) (= (= (f6 f13 ?v0) f1) (= f32 f1))))
(assert (forall ((?v0 S6) (?v1 S4)) (= (f12 ?v0 (f7 (f14 (f15 (f16 (f17 f18 ?v1) f33) ?v1)) f13)) f1)))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S10) (?v3 S4) (?v4 S10) (?v5 S4)) (let ((?v_0 (f17 f18 ?v1))) (=> (= (f12 ?v0 (f7 (f14 (f15 (f16 ?v_0 ?v2) ?v3)) f13)) f1) (=> (= (f12 ?v0 (f7 (f14 (f15 (f16 (f17 f18 ?v3) ?v4) ?v5)) f13)) f1) (= (f12 ?v0 (f7 (f14 (f15 (f16 ?v_0 (f34 (f35 f36 ?v2) ?v4)) ?v5)) f13)) f1))))))
(assert (forall ((?v0 S4) (?v1 S10) (?v2 S4)) (= (f24 f37 (f15 (f16 (f17 f18 ?v0) ?v1) ?v2)) (f27 f28 0))))
(assert (forall ((?v0 S5)) (=> (forall ((?v1 S4) (?v2 S10) (?v3 S4)) (=> (= ?v0 (f15 (f16 (f17 f18 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f9 ?v0 ?v1) f1) (=> (forall ((?v2 S6)) (=> (= ?v1 (f7 (f14 ?v0) ?v2)) (=> (not (= (f9 ?v0 ?v2) f1)) false))) false))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f9 ?v0 ?v1) f1) (exists ((?v2 S6)) (and (= ?v1 (f7 (f14 ?v0) ?v2)) (not (= (f9 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S5)) (=> (= (f9 ?v1 ?v0) f1) false)) (= ?v0 f13))))
(assert (forall ((?v0 S2)) (= (f3 (f4 (f22 f33) ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 (f22 f33) ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S10) (?v1 S2) (?v2 S2) (?v3 S10) (?v4 S2)) (=> (= (f3 (f4 (f22 ?v0) ?v1) ?v2) f1) (=> (= (f3 (f4 (f22 ?v3) ?v2) ?v4) f1) (= (f3 (f4 (f22 (f34 (f35 f36 ?v0) ?v3)) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (not (= (f34 (f35 f36 ?v0) ?v1) f33))))
(assert (forall ((?v0 S10) (?v1 S10)) (not (= f33 (f34 (f35 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 (f22 (f34 (f35 f36 ?v0) ?v1)) ?v2) ?v3) f1) (=> (forall ((?v4 S2)) (=> (= (f3 (f4 (f22 ?v0) ?v2) ?v4) f1) (=> (= (f3 (f4 (f22 ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S10) (?v3 S4)) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 ?v0 ?v4) ?v5) f1) (exists ((?v6 S4) (?v7 S4)) (and (= (f12 ?v1 (f7 (f14 (f15 (f16 (f17 f18 ?v6) ?v2) ?v7)) f13)) f1) (forall ((?v8 S2)) (=> (forall ((?v9 S2)) (=> (= (f3 (f4 ?v6 ?v9) ?v5) f1) (= (f3 (f4 ?v7 ?v9) ?v8) f1))) (= (f3 (f4 ?v3 ?v4) ?v8) f1))))))) (= (f12 ?v1 (f7 (f14 (f15 (f16 (f17 f18 ?v0) ?v2) ?v3)) f13)) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f34 (f35 f36 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f4 (f22 ?v0) ?v1))) (=> (= (f3 ?v_0 ?v2) f1) (=> (= (f3 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S6)) (= (not (= ?v0 f13)) (exists ((?v1 S5) (?v2 S6)) (and (= ?v0 (f7 (f14 ?v1) ?v2)) (not (= (f9 ?v1 ?v2) f1)))))))
(assert (forall ((?v0 S5)) (= (= (f6 f13 ?v0) f1) (= (f9 ?v0 f13) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f23 ?v0 ?v1) f1) (forall ((?v2 S14)) (=> (forall ((?v3 S5)) (=> (= (f9 ?v3 ?v0) f1) (= (f6 (f38 ?v2) ?v3) f1))) (forall ((?v3 S5)) (=> (= (f9 ?v3 ?v1) f1) (= (f6 (f38 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S14)) (= (f27 f28 (f39 f40 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f39 f40 (f27 f28 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f39 f40 (f27 f28 ?v0)) 0))))
(check-sat)
(exit)

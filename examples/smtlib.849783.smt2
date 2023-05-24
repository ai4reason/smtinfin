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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S2 S3) S1)
(declare-fun f6 () S3)
(declare-fun f7 (S4) S3)
(declare-fun f8 (S5 S3) S3)
(declare-fun f9 (S2) S5)
(declare-fun f10 (S6 S7) S2)
(declare-fun f11 (S8 S9) S6)
(declare-fun f12 (S10 S7) S8)
(declare-fun f13 () S10)
(declare-fun f14 () S7)
(declare-fun f15 () S9)
(declare-fun f16 () S7)
(declare-fun f17 () S3)
(declare-fun f18 (S13 S12) S1)
(declare-fun f19 (S7 S11) S13)
(declare-fun f20 (S3 S3) S1)
(declare-fun f21 (S14 Int) S4)
(declare-fun f22 () S14)
(declare-fun f23 (S15 S4) Int)
(declare-fun f24 () S15)
(declare-fun f25 (S17 S2) S4)
(declare-fun f26 (S18 S16) S17)
(declare-fun f27 () S18)
(declare-fun f28 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) false)))
(assert (not (forall ((?v0 S4)) (=> (forall ((?v1 S2)) (=> (= (f5 ?v1 f6) f1) (= (f3 (f7 ?v0) ?v1) f1))) (forall ((?v1 S2)) (=> (= (f5 ?v1 (f8 (f9 (f10 (f11 (f12 f13 f14) f15) f16)) f17)) f1) (= (f3 (f7 ?v0) ?v1) f1)))))))
(assert (forall ((?v0 S11) (?v1 S12)) (=> (= (f18 (f19 f14 ?v0) ?v1) f1) (exists ((?v2 S7) (?v3 S7)) (and (and (= (f20 f6 (f8 (f9 (f10 (f11 (f12 f13 ?v2) f15) ?v3)) f17)) f1) (forall ((?v4 S4)) (=> (forall ((?v5 S2)) (=> (= (f5 ?v5 f6) f1) (= (f3 (f7 ?v4) ?v5) f1))) (forall ((?v5 S2)) (=> (= (f5 ?v5 (f8 (f9 (f10 (f11 (f12 f13 ?v2) f15) ?v3)) f17)) f1) (= (f3 (f7 ?v4) ?v5) f1)))))) (forall ((?v4 S12)) (=> (forall ((?v5 S11)) (=> (= (f18 (f19 ?v2 ?v5) ?v1) f1) (= (f18 (f19 ?v3 ?v5) ?v4) f1))) (= (f18 (f19 f16 ?v0) ?v4) f1))))))))
(assert (forall ((?v0 S3)) (= (f20 ?v0 f17) f1)))
(assert (forall ((?v0 S7) (?v1 S9) (?v2 S7) (?v3 S7) (?v4 S9) (?v5 S7)) (= (= (f10 (f11 (f12 f13 ?v0) ?v1) ?v2) (f10 (f11 (f12 f13 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f20 ?v0 ?v1) f1) (=> (= (f20 ?v2 ?v0) f1) (= (f20 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (forall ((?v2 S2)) (=> (= (f5 ?v2 ?v0) f1) (= (f3 (f7 (f21 f22 (+ (f23 f24 ?v1) 1))) ?v2) f1))) (forall ((?v2 S2)) (=> (= (f5 ?v2 ?v0) f1) (= (f3 (f7 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f9 ?v1))) (=> (= (f20 ?v0 (f8 ?v_0 f17)) f1) (=> (= (f20 ?v0 ?v2) f1) (= (f20 ?v0 (f8 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f9 ?v1))) (=> (= (f20 ?v0 (f8 ?v_0 ?v2)) f1) (and (= (f20 ?v0 (f8 ?v_0 f17)) f1) (= (f20 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (=> (= (f3 (f7 (f21 f22 (+ (f23 f24 ?v0) 1))) ?v1) f1) (= (f3 (f7 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (let ((?v_0 (f11 (f12 f13 ?v1) ?v2))) (=> (= (f20 ?v0 (f8 (f9 (f10 ?v_0 ?v3)) f17)) f1) (=> (forall ((?v5 S11) (?v6 S12)) (=> (= (f18 (f19 ?v3 ?v5) ?v6) f1) (= (f18 (f19 ?v4 ?v5) ?v6) f1))) (= (f20 ?v0 (f8 (f9 (f10 ?v_0 ?v4)) f17)) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (=> (= (f20 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v1) ?v2) ?v3)) f17)) f1) (=> (forall ((?v5 S11) (?v6 S12)) (=> (= (f18 (f19 ?v4 ?v5) ?v6) f1) (= (f18 (f19 ?v1 ?v5) ?v6) f1))) (= (f20 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v4) ?v2) ?v3)) f17)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f5 ?v0 (f8 (f9 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f5 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f5 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f5 ?v0 (f8 (f9 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7) (?v5 S7)) (=> (= (f20 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v1) ?v2) ?v3)) f17)) f1) (=> (forall ((?v6 S11) (?v7 S12)) (=> (= (f18 (f19 ?v4 ?v6) ?v7) f1) (forall ((?v8 S12)) (=> (forall ((?v9 S11)) (=> (= (f18 (f19 ?v1 ?v9) ?v7) f1) (= (f18 (f19 ?v3 ?v9) ?v8) f1))) (= (f18 (f19 ?v5 ?v6) ?v8) f1))))) (= (f20 ?v0 (f8 (f9 (f10 (f11 (f12 f13 ?v4) ?v2) ?v5)) f17)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 f17) f1) false)))
(assert (forall ((?v0 S16) (?v1 S7) (?v2 S9) (?v3 S7)) (= (f25 (f26 f27 ?v0) (f10 (f11 (f12 f13 ?v1) ?v2) ?v3)) (f21 f22 0))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f17 (f8 (f9 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f8 (f9 ?v0) ?v1) f17))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 ?v0 (f8 (f9 ?v1) f17)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f17) (not (= (f5 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f28 ?v0) f17) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f5 ?v0 f17) f1) false)))
(assert (forall ((?v0 S3)) (= (= f17 (f28 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f5 ?v1 f17) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f5 ?v1 f17) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f5 ?v1 ?v0) f1)) (not (= ?v0 f17)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f5 ?v1 ?v0) f1))) (= ?v0 f17))))
(assert (= f17 (f28 f4)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f5 ?v0 ?v1) f1) (= (f8 (f9 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f5 ?v0 ?v1) f1) (= (f5 ?v0 (f8 (f9 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f9 ?v0))) (=> (not (= (f5 ?v0 ?v1) f1)) (=> (not (= (f5 ?v0 ?v2) f1)) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f8 (f9 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4)) (= (f21 f22 (f23 f24 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f23 f24 (f21 f22 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f23 f24 (f21 f22 ?v0)) 0))))
(check-sat)
(exit)
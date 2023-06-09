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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 () S2)
(declare-fun f5 (S5 S3) S3)
(declare-fun f6 (S6) S5)
(declare-fun f7 (S7 S8) S6)
(declare-fun f8 () S7)
(declare-fun f9 () S8)
(declare-fun f10 () S3)
(declare-fun f11 (S9 Int) S4)
(declare-fun f12 () S9)
(declare-fun f13 (S10 S4) Int)
(declare-fun f14 () S10)
(declare-fun f15 (S11 S12) S3)
(declare-fun f16 (S7) S11)
(declare-fun f17 () S12)
(declare-fun f18 () S4)
(declare-fun f19 (S12) S1)
(declare-fun f20 (S3 S3) S1)
(declare-fun f21 (S8 S12) S1)
(declare-fun f22 (S6 S3) S1)
(declare-fun f23 (S13 S12) S4)
(declare-fun f24 () S13)
(declare-fun f25 (S14 S12) S12)
(declare-fun f26 (S8) S14)
(declare-fun f27 (S3) S1)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 (f7 f8 f9)) f10)) (f11 f12 (- (f13 f14 (f3 f4 (f15 (f16 f8) f17))) (f13 f14 f18))))))
(assert (= (f19 f17) f1))
(assert (= (f20 f10 (f15 (f16 f8) f17)) f1))
(assert (<= (+ (f13 f14 f18) 1) (f13 f14 (f3 f4 (f15 (f16 f8) f17)))))
(assert (= (f3 f4 f10) (f11 f12 (- (f13 f14 (f3 f4 (f15 (f16 f8) f17))) (+ (f13 f14 f18) 1)))))
(assert (= (f21 f9 f17) f1))
(assert (not (= (f22 (f7 f8 f9) f10) f1)))
(assert (forall ((?v0 S12) (?v1 S8)) (=> (= (f19 ?v0) f1) (=> (not (= (f21 ?v1 ?v0) f1)) (= (f23 f24 (f25 (f26 ?v1) ?v0)) (f11 f12 (+ (f13 f14 (f23 f24 ?v0)) 1)))))))
(assert (forall ((?v0 S3) (?v1 S6)) (=> (= (f27 ?v0) f1) (=> (not (= (f22 ?v1 ?v0) f1)) (= (f3 f4 (f5 (f6 ?v1) ?v0)) (f11 f12 (+ (f13 f14 (f3 f4 ?v0)) 1)))))))
(assert (forall ((?v0 S4)) (= (f11 f12 (f13 f14 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f13 f14 (f11 f12 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f13 f14 (f11 f12 ?v0)) 0))))
(check-sat)
(exit)

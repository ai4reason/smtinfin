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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 () S2)
(declare-fun f5 (S5 S3) S3)
(declare-fun f6 (S6 S7) S5)
(declare-fun f7 () S6)
(declare-fun f8 () S7)
(declare-fun f9 () S3)
(declare-fun f10 (S8 Int) S4)
(declare-fun f11 () S8)
(declare-fun f12 (S9 S4) Int)
(declare-fun f13 () S9)
(declare-fun f14 (S6 S10) S3)
(declare-fun f15 () S10)
(declare-fun f16 () S4)
(declare-fun f17 (S10) S1)
(declare-fun f18 (S7 S10) S1)
(declare-fun f19 (S5 S3) S1)
(declare-fun f20 (S3) S1)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 f7 f8) f9)) (f10 f11 (- (f12 f13 (f3 f4 (f14 f7 f15))) (f12 f13 f16))))))
(assert (= (f17 f15) f1))
(assert (<= (+ (f12 f13 f16) 1) (f12 f13 (f3 f4 (f14 f7 f15)))))
(assert (= (f3 f4 f9) (f10 f11 (- (f12 f13 (f3 f4 (f14 f7 f15))) (+ (f12 f13 f16) 1)))))
(assert (= (f18 f8 f15) f1))
(assert (not (= (f19 (f6 f7 f8) f9) f1)))
(assert (= (f20 f9) f1))
(assert (forall ((?v0 S4)) (= (f10 f11 (f12 f13 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f12 f13 (f10 f11 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f12 f13 (f10 f11 ?v0)) 0))))
(check-sat)
(exit)

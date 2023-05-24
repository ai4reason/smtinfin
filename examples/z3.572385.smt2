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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 Int) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6 S5) S3)
(declare-fun f7 () S5)
(declare-fun f8 (S7) S6)
(declare-fun f9 () S7)
(declare-fun f10 () S5)
(declare-fun f11 (S8 S6) S2)
(declare-fun f12 () S8)
(declare-fun f13 () S6)
(declare-fun f14 (S6 S9 S2 S9) S1)
(declare-fun f15 (S10 S2) Int)
(declare-fun f16 () S10)
(declare-fun f17 (S11) S6)
(declare-fun f18 (S7) S11)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 0) (f6 f7 (f8 f9) f10)) f1)))
(assert (= (f11 f12 f13) (f4 f5 0)))
(assert (forall ((?v0 S7) (?v1 S9) (?v2 S2) (?v3 S9)) (=> (= (f14 (f8 ?v0) ?v1 ?v2 ?v3) f1) (=> (forall ((?v4 S2)) (=> (= ?v2 (f4 f5 (+ (f15 f16 ?v4) 1))) (=> (= (f14 (f17 (f18 ?v0)) ?v1 ?v4 ?v3) f1) false))) false))))
(assert (forall ((?v0 S2)) (= (f4 f5 (f15 f16 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f15 f16 (f4 f5 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f15 f16 (f4 f5 ?v0)) 0))))
(check-sat)
(exit)
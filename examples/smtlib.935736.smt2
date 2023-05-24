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
(declare-fun f13 (S3) S4)
(declare-fun f14 (S7) S8)
(declare-fun f15 (S2) S4)
(declare-fun f16 (S6) S8)
(declare-fun f17 () S3)
(declare-fun f18 () S7)
(declare-fun f19 (S10) S1)
(declare-fun f20 () S10)
(declare-fun f21 (S3) S5)
(declare-fun f22 () S3)
(declare-fun f23 (S2) S4)
(declare-fun f24 (S11 S10) S2)
(declare-fun f25 () S11)
(declare-fun f26 () S3)
(declare-fun f27 () S1)
(declare-fun f28 (S12) S7)
(declare-fun f29 () S12)
(declare-fun f30 (S13 S6) S10)
(declare-fun f31 () S13)
(declare-fun f32 (S6) S8)
(declare-fun f33 () S7)
(declare-fun f34 () S1)
(declare-fun f35 (S3) S3)
(declare-fun f36 (S7) S7)
(declare-fun f37 (S15 S3) S2)
(declare-fun f38 () S15)
(declare-fun f39 (S16 S7) S6)
(declare-fun f40 () S16)
(declare-fun f41 (S3) S5)
(declare-fun f42 (S18 S17) S2)
(declare-fun f43 (S19 S10) S18)
(declare-fun f44 (S20 S17) S19)
(declare-fun f45 () S20)
(declare-fun f46 (S21 S22) S10)
(declare-fun f47 () S21)
(declare-fun f48 (S12 S6) S22)
(declare-fun f49 (S23 S14) S1)
(declare-fun f50 (S17 S14) S23)
(declare-fun f51 (S24) S3)
(declare-fun f52 (S25 Int) S24)
(declare-fun f53 () S25)
(declare-fun f54 (S26 S24) Int)
(declare-fun f55 () S26)
(declare-fun f56 (S28 S2) S24)
(declare-fun f57 (S29 S27) S28)
(declare-fun f58 () S29)
(declare-fun f59 () S10)
(declare-fun f60 (S30 S10) S10)
(declare-fun f61 (S31 S10) S30)
(declare-fun f62 () S31)
(declare-fun f63 () S28)
(declare-fun f64 (S7) S1)
(declare-fun f65 (S32) S4)
(declare-fun f66 (S33) S8)
(declare-fun f67 (S32 S15) S1)
(declare-fun f68 (S33 S16) S1)
(declare-fun f69 (S3) S1)
(declare-fun f70 (S34 S2) S2)
(declare-fun f71 (S32 S2) S34)
(declare-fun f72 (S35 S6) S6)
(declare-fun f73 (S33 S6) S35)
(declare-fun f74 (S32 S15) S1)
(declare-fun f75 (S33 S16) S1)
(declare-fun f76 (S3) S4)
(declare-fun f77 (S7) S8)
(declare-fun f78 (S36 S2) S4)
(declare-fun f79 (S32) S36)
(declare-fun f80 (S37 S6) S8)
(declare-fun f81 (S33) S37)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 (f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (= (= (f8 (f9 (f10 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f11 (f12 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v2))) (= (= (f3 (f4 (f13 ?v0) ?v1) ?v2) f1) (and (= (f6 ?v_0 ?v0) f1) (not (= (f6 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S6)) (let ((?v_0 (f12 ?v2))) (= (= (f8 (f9 (f14 ?v0) ?v1) ?v2) f1) (and (= (f11 ?v_0 ?v0) f1) (not (= (f11 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f15 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (= (= (f8 (f9 (f16 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f8 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f17 ?v0) f1) false)))
(assert (forall ((?v0 S6)) (= (= (f8 f18 ?v0) f1) false)))
(assert (not (=> (= (f19 f20) f1) (= (f6 (f21 f22) (f4 (f23 (f24 f25 f20)) f26)) f1))))
(assert (= f27 f1))
(assert (forall ((?v0 S6)) (=> (= (f11 (f12 ?v0) (f28 f29)) f1) (= (f6 (f21 f22) (f4 (f23 (f24 f25 (f30 f31 ?v0))) f26)) f1))))
(assert (forall ((?v0 S3)) (= (f6 (f21 ?v0) f26) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 ?v2))) (=> (= (f6 (f21 ?v0) ?v1) f1) (=> (= (f6 ?v_0 ?v0) f1) (= (f6 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f21 ?v0)) (?v_1 (f23 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 f26)) f1) (=> (= (f6 ?v_0 ?v2) f1) (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f21 ?v0)) (?v_1 (f23 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f6 ?v_0 (f4 ?v_1 f26)) f1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f23 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 (f9 (f32 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f11 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (=> (not (= (f6 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v_0 (f4 (f23 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (let ((?v_0 (f12 ?v0))) (=> (=> (not (= (f11 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f11 ?v_0 (f9 (f32 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6)) (=> (= (f11 (f12 ?v0) f33) f1) false)))
(assert (forall ((?v0 S2)) (=> (= (f6 (f7 ?v0) f26) f1) false)))
(assert (= (= f27 f1) (exists ((?v0 S14) (?v1 S14)) (not (= ?v0 ?v1)))))
(assert (=> (= f27 f1) (forall ((?v0 S14)) (=> (forall ((?v1 S14)) (= ?v1 ?v0)) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f26 (f4 (f23 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (not (= f33 (f9 (f32 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f23 ?v0) ?v1) f26))))
(assert (forall ((?v0 S6) (?v1 S7)) (not (= (f9 (f32 ?v0) ?v1) f33))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 (f7 ?v0) (f4 (f23 ?v1) f26)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f11 (f12 ?v0) (f9 (f32 ?v1) f33)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f23 ?v0) (f4 (f23 ?v1) f26)) (f4 (f23 ?v2) (f4 (f23 ?v3) f26))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (= (f9 (f32 ?v0) (f9 (f32 ?v1) f33)) (f9 (f32 ?v2) (f9 (f32 ?v3) f33))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 (f7 ?v0) (f4 (f23 ?v1) f26)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f12 ?v0) (f9 (f32 ?v1) f33)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f23 ?v0) f26) (f4 (f23 ?v1) f26)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f9 (f32 ?v0) f33) (f9 (f32 ?v1) f33)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (= (= (f3 f26 ?v0) f1) (= f34 f1))))
(assert (forall ((?v0 S6)) (= (= (f8 f33 ?v0) f1) (= f34 f1))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= ?v0 f33) (not (= (f11 (f12 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f26) (not (= (f6 (f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f35 ?v0) f26) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (= (f36 ?v0) f33) (forall ((?v1 S6)) (not (= (f8 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (= (f11 (f12 ?v0) f33) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f6 (f7 ?v0) f26) f1) false)))
(assert (forall ((?v0 S3)) (= (= f26 (f35 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (= f33 (f36 ?v0)) (forall ((?v1 S6)) (not (= (f8 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (forall ((?v1 S6)) (=> (= (f11 (f12 ?v1) f33) f1) (= (f8 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) f26) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S7)) (= (exists ((?v1 S6)) (and (= (f11 (f12 ?v1) f33) f1) (= (f8 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 (f7 ?v1) f26) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S7)) (= (exists ((?v1 S6)) (= (f11 (f12 ?v1) ?v0) f1)) (not (= ?v0 f33)))))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 (f7 ?v1) ?v0) f1)) (not (= ?v0 f26)))))
(assert (forall ((?v0 S7)) (= (forall ((?v1 S6)) (not (= (f11 (f12 ?v1) ?v0) f1))) (= ?v0 f33))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 (f7 ?v1) ?v0) f1))) (= ?v0 f26))))
(assert (= f26 (f35 f17)))
(assert (= f33 (f36 f18)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f23 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f11 (f12 ?v0) ?v1) f1) (= (f9 (f32 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (= (f6 ?v_0 (f4 (f23 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (= (f11 ?v_0 (f9 (f32 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0)) (?v_1 (f23 ?v0))) (=> (not (= (f6 ?v_0 ?v1) f1)) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f12 ?v0)) (?v_1 (f32 ?v0))) (=> (not (= (f11 ?v_0 ?v1) f1)) (=> (not (= (f11 ?v_0 ?v2) f1)) (= (= (f9 ?v_1 ?v1) (f9 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f23 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6)) (= (= (f8 (f9 (f32 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f8 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f23 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (= (= (f11 ?v_0 (f9 (f32 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f11 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f23 ?v0)) (?v_0 (f23 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (let ((?v_1 (f32 ?v0)) (?v_0 (f32 ?v1))) (= (f9 ?v_1 (f9 ?v_0 ?v2)) (f9 ?v_0 (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f23 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (let ((?v_0 (f32 ?v0))) (let ((?v_1 (f9 ?v_0 ?v1))) (= (f9 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f23 ?v0) (f35 ?v1)) (f35 (f4 (f15 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f9 (f32 ?v0) (f36 ?v1)) (f36 (f9 (f16 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f23 ?v0) ?v1) (f35 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f9 (f32 ?v0) ?v1) (f36 (f9 (f10 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 (f7 ?v0) (f4 (f23 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f11 (f12 ?v0) (f9 (f32 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2)) (= (= (f3 f26 ?v0) f1) (= f34 f1))))
(assert (forall ((?v0 S6)) (= (= (f8 f33 ?v0) f1) (= f34 f1))))
(assert (forall ((?v0 S2)) (= (f37 f38 (f4 (f23 ?v0) f26)) ?v0)))
(assert (forall ((?v0 S6)) (= (f39 f40 (f9 (f32 ?v0) f33)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f23 ?v0) ?v2)) (=> (not (= (f6 (f7 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f11 (f12 ?v0) ?v1) f1) (=> (forall ((?v2 S7)) (=> (= ?v1 (f9 (f32 ?v0) ?v2)) (=> (not (= (f11 (f12 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f23 ?v0) ?v2)) (not (= (f6 (f7 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S6) (?v1 S7)) (=> (= (f11 (f12 ?v0) ?v1) f1) (exists ((?v2 S7)) (and (= ?v1 (f9 (f32 ?v0) ?v2)) (not (= (f11 (f12 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S6)) (=> (= (f11 (f12 ?v1) ?v0) f1) false)) (= ?v0 f33))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) ?v0) f1) false)) (= ?v0 f26))))
(assert (forall ((?v0 S10) (?v1 S17) (?v2 S17)) (let ((?v_0 (f21 f26)) (?v_1 (f4 (f23 (f42 (f43 (f44 f45 ?v1) ?v0) ?v2)) f26))) (=> (= (f6 ?v_0 (f4 (f23 (f24 f25 ?v0)) f26)) f1) (=> (= (f6 (f41 f26) ?v_1) f1) (= (f6 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f30 f31 ?v0) (f30 f31 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f26)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f23 ?v1) ?v2)) (not (= (f6 (f7 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S7)) (= (not (= ?v0 f33)) (exists ((?v1 S6) (?v2 S7)) (and (= ?v0 (f9 (f32 ?v1) ?v2)) (not (= (f11 (f12 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S6)) (= (= (f8 f33 ?v0) f1) (= (f11 (f12 ?v0) f33) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f26 ?v0) f1) (= (f6 (f7 ?v0) f26) f1))))
(assert (forall ((?v0 S17) (?v1 S6) (?v2 S17) (?v3 S3)) (let ((?v_0 (f44 f45 ?v0))) (let ((?v_1 (f23 (f42 (f43 ?v_0 (f30 f31 ?v1)) ?v2)))) (=> (= (f6 (f21 (f4 ?v_1 ?v3)) (f4 (f23 (f42 (f43 ?v_0 (f46 f47 (f48 f29 ?v1))) ?v2)) f26)) f1) (= (f6 (f21 ?v3) (f4 ?v_1 f26)) f1))))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S6) (?v3 S17)) (let ((?v_0 (f21 ?v0)) (?v_1 (f44 f45 ?v1))) (=> (= (f6 ?v_0 (f4 (f23 (f42 (f43 ?v_1 (f46 f47 (f48 f29 ?v2))) ?v3)) f26)) f1) (= (f6 ?v_0 (f4 (f23 (f42 (f43 ?v_1 (f30 f31 ?v2)) ?v3)) f26)) f1)))))
(assert (forall ((?v0 S17) (?v1 S10) (?v2 S17) (?v3 S17) (?v4 S10) (?v5 S17)) (= (= (f42 (f43 (f44 f45 ?v0) ?v1) ?v2) (f42 (f43 (f44 f45 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f6 (f21 ?v0) ?v1) f1) (= (f6 (f41 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S10) (?v3 S17) (?v4 S17)) (let ((?v_0 (f21 ?v0)) (?v_1 (f43 (f44 f45 ?v1) ?v2))) (=> (= (f6 ?v_0 (f4 (f23 (f42 ?v_1 ?v3)) f26)) f1) (=> (forall ((?v5 S14) (?v6 S14)) (=> (= (f49 (f50 ?v3 ?v5) ?v6) f1) (= (f49 (f50 ?v4 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f23 (f42 ?v_1 ?v4)) f26)) f1))))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S10) (?v3 S17) (?v4 S17)) (let ((?v_0 (f21 ?v0))) (=> (= (f6 ?v_0 (f4 (f23 (f42 (f43 (f44 f45 ?v1) ?v2) ?v3)) f26)) f1) (=> (forall ((?v5 S14) (?v6 S14)) (=> (= (f49 (f50 ?v4 ?v5) ?v6) f1) (= (f49 (f50 ?v1 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f23 (f42 (f43 (f44 f45 ?v4) ?v2) ?v3)) f26)) f1))))))
(assert (forall ((?v0 S24) (?v1 S17) (?v2 S6) (?v3 S17)) (let ((?v_0 (f44 f45 ?v1))) (= (= (f3 (f51 ?v0) (f42 (f43 ?v_0 (f46 f47 (f48 f29 ?v2))) ?v3)) f1) (= (f3 (f51 (f52 f53 (+ (f54 f55 ?v0) 1))) (f42 (f43 ?v_0 (f30 f31 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S10) (?v3 S17) (?v4 S17) (?v5 S17)) (let ((?v_0 (f21 ?v0))) (=> (= (f6 ?v_0 (f4 (f23 (f42 (f43 (f44 f45 ?v1) ?v2) ?v3)) f26)) f1) (=> (forall ((?v6 S14) (?v7 S14)) (=> (= (f49 (f50 ?v4 ?v6) ?v7) f1) (forall ((?v8 S14)) (=> (forall ((?v9 S14)) (=> (= (f49 (f50 ?v1 ?v9) ?v7) f1) (= (f49 (f50 ?v3 ?v9) ?v8) f1))) (= (f49 (f50 ?v5 ?v6) ?v8) f1))))) (= (f6 ?v_0 (f4 (f23 (f42 (f43 (f44 f45 ?v4) ?v2) ?v5)) f26)) f1))))))
(assert (forall ((?v0 S27) (?v1 S17) (?v2 S10) (?v3 S17)) (= (f56 (f57 f58 ?v0) (f42 (f43 (f44 f45 ?v1) ?v2) ?v3)) (f52 f53 0))))
(assert (forall ((?v0 S3) (?v1 S17)) (= (f6 (f21 ?v0) (f4 (f23 (f42 (f43 (f44 f45 ?v1) f59) ?v1)) f26)) f1)))
(assert (=> (= (f19 f59) f1) (=> false false)))
(assert (forall ((?v0 S3) (?v1 S24)) (=> (forall ((?v2 S2)) (=> (= (f6 (f7 ?v2) ?v0) f1) (= (f3 (f51 (f52 f53 (+ (f54 f55 ?v1) 1))) ?v2) f1))) (forall ((?v2 S2)) (=> (= (f6 (f7 ?v2) ?v0) f1) (= (f3 (f51 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S24) (?v1 S2)) (=> (= (f3 (f51 (f52 f53 (+ (f54 f55 ?v0) 1))) ?v1) f1) (= (f3 (f51 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6)) (not (= (f30 f31 ?v0) f59))))
(assert (forall ((?v0 S6)) (not (= f59 (f30 f31 ?v0)))))
(assert (= (f19 f59) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f41 ?v0) ?v1) f1) (forall ((?v2 S24)) (=> (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v0) f1) (= (f3 (f51 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v1) f1) (= (f3 (f51 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S17) (?v1 S6) (?v2 S17)) (= (f3 (f51 (f52 f53 0)) (f42 (f43 (f44 f45 ?v0) (f30 f31 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S10) (?v3 S17) (?v4 S10) (?v5 S17)) (let ((?v_0 (f21 ?v0)) (?v_1 (f44 f45 ?v1))) (=> (= (f6 ?v_0 (f4 (f23 (f42 (f43 ?v_1 ?v2) ?v3)) f26)) f1) (=> (= (f6 ?v_0 (f4 (f23 (f42 (f43 (f44 f45 ?v3) ?v4) ?v5)) f26)) f1) (= (f6 ?v_0 (f4 (f23 (f42 (f43 ?v_1 (f60 (f61 f62 ?v2) ?v4)) ?v5)) f26)) f1))))))
(assert (forall ((?v0 S17) (?v1 S10) (?v2 S17)) (= (f56 f63 (f42 (f43 (f44 f45 ?v0) ?v1) ?v2)) (f52 f53 0))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S17) (?v2 S10) (?v3 S17)) (=> (= ?v0 (f42 (f43 (f44 f45 ?v1) ?v2) ?v3)) false)) false)))
(assert (= (f64 (f28 f29)) f1))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S10) (?v3 S17)) (=> (forall ((?v4 S14) (?v5 S14)) (=> (= (f49 (f50 ?v0 ?v4) ?v5) f1) (exists ((?v6 S17) (?v7 S17)) (and (= (f6 (f21 ?v1) (f4 (f23 (f42 (f43 (f44 f45 ?v6) ?v2) ?v7)) f26)) f1) (forall ((?v8 S14)) (=> (forall ((?v9 S14)) (=> (= (f49 (f50 ?v6 ?v9) ?v5) f1) (= (f49 (f50 ?v7 ?v9) ?v8) f1))) (= (f49 (f50 ?v3 ?v4) ?v8) f1))))))) (= (f6 (f21 ?v1) (f4 (f23 (f42 (f43 (f44 f45 ?v0) ?v2) ?v3)) f26)) f1))))
(assert (forall ((?v0 S32) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f65 ?v0) (f4 (f23 ?v1) f26)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S33) (?v1 S6) (?v2 S6)) (= (= (f8 (f9 (f66 ?v0) (f9 (f32 ?v1) f33)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S2)) (=> (= (f67 ?v0 ?v1) f1) (= (f37 ?v1 (f4 (f23 ?v2) f26)) ?v2))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S6)) (=> (= (f68 ?v0 ?v1) f1) (= (f39 ?v1 (f9 (f32 ?v2) f33)) ?v2))))
(assert (= (f64 f33) f1))
(assert (= (f69 f26) f1))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f69 ?v0) f1) (= (f69 (f4 (f23 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= (f64 ?v0) f1) (= (f64 (f9 (f32 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f19 (f60 (f61 f62 ?v0) ?v1)) f1) (=> (=> (= (f19 ?v0) f1) (=> (= (f19 ?v1) f1) false)) false))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f11 (f12 ?v0) ?v1) f1) (= (f8 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f35 ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f36 ?v0) ?v0)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f60 (f61 f62 ?v0) ?v1) (f60 (f61 f62 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f69 (f4 (f23 ?v0) ?v1)) f1) (= (f69 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f64 (f9 (f32 ?v0) ?v1)) f1) (= (f64 ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S3) (?v3 S2)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f69 ?v2) f1) (=> (not (= (f6 (f7 ?v3) ?v2) f1)) (=> (not (= ?v2 f26)) (= (f37 ?v1 (f4 (f23 ?v3) ?v2)) (f70 (f71 ?v0 ?v3) (f37 ?v1 ?v2)))))))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S7) (?v3 S6)) (=> (= (f68 ?v0 ?v1) f1) (=> (= (f64 ?v2) f1) (=> (not (= (f11 (f12 ?v3) ?v2) f1)) (=> (not (= ?v2 f33)) (= (f39 ?v1 (f9 (f32 ?v3) ?v2)) (f72 (f73 ?v0 ?v3) (f39 ?v1 ?v2)))))))))
(assert (forall ((?v0 S6) (?v1 S10) (?v2 S10)) (not (= (f30 f31 ?v0) (f60 (f61 f62 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S6)) (not (= (f60 (f61 f62 ?v0) ?v1) (f30 f31 ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f19 ?v0) f1) (=> (= (f19 ?v1) f1) (= (f19 (f60 (f61 f62 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (not (= f59 (f60 (f61 f62 ?v0) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (not (= (f60 (f61 f62 ?v0) ?v1) f59))))
(assert (forall ((?v0 S32) (?v1 S2)) (=> (= (f3 (f4 (f65 ?v0) f26) ?v1) f1) false)))
(assert (forall ((?v0 S33) (?v1 S6)) (=> (= (f8 (f9 (f66 ?v0) f33) ?v1) f1) false)))
(assert (forall ((?v0 S32) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f65 ?v0) ?v1) ?v2) f1) (not (= ?v1 f26)))))
(assert (forall ((?v0 S33) (?v1 S7) (?v2 S6)) (=> (= (f8 (f9 (f66 ?v0) ?v1) ?v2) f1) (not (= ?v1 f33)))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S3)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f69 ?v2) f1) (=> (not (= ?v2 f26)) (=> (forall ((?v3 S2) (?v4 S2)) (= (f6 (f7 (f70 (f71 ?v0 ?v3) ?v4)) (f4 (f23 ?v3) (f4 (f23 ?v4) f26))) f1)) (= (f6 (f7 (f37 ?v1 ?v2)) ?v2) f1)))))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S7)) (=> (= (f68 ?v0 ?v1) f1) (=> (= (f64 ?v2) f1) (=> (not (= ?v2 f33)) (=> (forall ((?v3 S6) (?v4 S6)) (= (f11 (f12 (f72 (f73 ?v0 ?v3) ?v4)) (f9 (f32 ?v3) (f9 (f32 ?v4) f33))) f1)) (= (f11 (f12 (f39 ?v1 ?v2)) ?v2) f1)))))))
(assert (forall ((?v0 S7) (?v1 S33)) (=> (= (f64 ?v0) f1) (=> (not (= ?v0 f33)) (exists ((?v2 S6)) (= (f8 (f9 (f66 ?v1) ?v0) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S32)) (=> (= (f69 ?v0) f1) (=> (not (= ?v0 f26)) (exists ((?v2 S2)) (= (f3 (f4 (f65 ?v1) ?v0) ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (= (f69 ?v0) f1) (or (= ?v0 f26) (exists ((?v1 S3) (?v2 S2)) (and (= ?v0 (f4 (f23 ?v2) ?v1)) (= (f69 ?v1) f1)))))))
(assert (forall ((?v0 S7)) (= (= (f64 ?v0) f1) (or (= ?v0 f33) (exists ((?v1 S7) (?v2 S6)) (and (= ?v0 (f9 (f32 ?v2) ?v1)) (= (f64 ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f69 ?v0) f1) (=> (= (f6 ?v1 f26) f1) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f69 ?v3) f1) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f23 ?v2) ?v3)) f1))))) (= (f6 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S7) (?v1 S9)) (=> (= (f64 ?v0) f1) (=> (= (f11 ?v1 f33) f1) (=> (forall ((?v2 S6) (?v3 S7)) (=> (= (f64 ?v3) f1) (=> (not (= (f11 (f12 ?v2) ?v3) f1)) (=> (= (f11 ?v1 ?v3) f1) (= (f11 ?v1 (f9 (f32 ?v2) ?v3)) f1))))) (= (f11 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S3) (?v3 S2)) (=> (= (f74 ?v0 ?v1) f1) (=> (= (f69 ?v2) f1) (=> (not (= ?v2 f26)) (= (f37 ?v1 (f4 (f23 ?v3) ?v2)) (f70 (f71 ?v0 ?v3) (f37 ?v1 ?v2))))))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S7) (?v3 S6)) (=> (= (f75 ?v0 ?v1) f1) (=> (= (f64 ?v2) f1) (=> (not (= ?v2 f33)) (= (f39 ?v1 (f9 (f32 ?v3) ?v2)) (f72 (f73 ?v0 ?v3) (f39 ?v1 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f69 ?v0) f1) (=> (not (= ?v0 f26)) (=> (forall ((?v2 S2)) (= (f6 ?v1 (f4 (f23 ?v2) f26)) f1)) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f69 ?v3) f1) (=> (not (= ?v3 f26)) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f23 ?v2) ?v3)) f1)))))) (= (f6 ?v1 ?v0) f1)))))))
(assert (forall ((?v0 S7) (?v1 S9)) (=> (= (f64 ?v0) f1) (=> (not (= ?v0 f33)) (=> (forall ((?v2 S6)) (= (f11 ?v1 (f9 (f32 ?v2) f33)) f1)) (=> (forall ((?v2 S6) (?v3 S7)) (=> (= (f64 ?v3) f1) (=> (not (= ?v3 f33)) (=> (not (= (f11 (f12 ?v2) ?v3) f1)) (=> (= (f11 ?v1 ?v3) f1) (= (f11 ?v1 (f9 (f32 ?v2) ?v3)) f1)))))) (= (f11 ?v1 ?v0) f1)))))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S2)) (=> (= (f74 ?v0 ?v1) f1) (= (f70 (f71 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S6)) (=> (= (f75 ?v0 ?v1) f1) (= (f72 (f73 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S7) (?v3 S6)) (let ((?v_0 (f39 ?v1 ?v2))) (=> (= (f75 ?v0 ?v1) f1) (=> (= (f64 ?v2) f1) (=> (= (f11 (f12 ?v3) ?v2) f1) (= (f72 (f73 ?v0 ?v3) ?v_0) ?v_0)))))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S3) (?v3 S2)) (let ((?v_0 (f37 ?v1 ?v2))) (=> (= (f74 ?v0 ?v1) f1) (=> (= (f69 ?v2) f1) (=> (= (f6 (f7 ?v3) ?v2) f1) (= (f70 (f71 ?v0 ?v3) ?v_0) ?v_0)))))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S3) (?v3 S2)) (let ((?v_0 (f23 ?v3))) (let ((?v_1 (f4 (f76 ?v2) (f4 ?v_0 f26)))) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f69 ?v2) f1) (= (f37 ?v1 (f4 ?v_0 ?v2)) (ite (= ?v_1 f26) ?v3 (f70 (f71 ?v0 ?v3) (f37 ?v1 ?v_1))))))))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S7) (?v3 S6)) (let ((?v_0 (f32 ?v3))) (let ((?v_1 (f9 (f77 ?v2) (f9 ?v_0 f33)))) (=> (= (f68 ?v0 ?v1) f1) (=> (= (f64 ?v2) f1) (= (f39 ?v1 (f9 ?v_0 ?v2)) (ite (= ?v_1 f33) ?v3 (f72 (f73 ?v0 ?v3) (f39 ?v1 ?v_1))))))))))
(assert (forall ((?v0 S32) (?v1 S15) (?v2 S3) (?v3 S2)) (let ((?v_0 (f4 (f76 ?v2) (f4 (f23 ?v3) f26)))) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f69 ?v2) f1) (=> (= (f6 (f7 ?v3) ?v2) f1) (= (f37 ?v1 ?v2) (ite (= ?v_0 f26) ?v3 (f70 (f71 ?v0 ?v3) (f37 ?v1 ?v_0))))))))))
(assert (forall ((?v0 S33) (?v1 S16) (?v2 S7) (?v3 S6)) (let ((?v_0 (f9 (f77 ?v2) (f9 (f32 ?v3) f33)))) (=> (= (f68 ?v0 ?v1) f1) (=> (= (f64 ?v2) f1) (=> (= (f11 (f12 ?v3) ?v2) f1) (= (f39 ?v1 ?v2) (ite (= ?v_0 f33) ?v3 (f72 (f73 ?v0 ?v3) (f39 ?v1 ?v_0))))))))))
(assert (forall ((?v0 S32) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 (f4 (f78 (f79 ?v0) ?v1) ?v2) ?v3) f1) (=> (not (= (f6 (f7 ?v1) ?v2) f1)) (= (f3 (f4 (f65 ?v0) (f4 (f23 ?v1) ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S33) (?v1 S6) (?v2 S7) (?v3 S6)) (=> (= (f8 (f9 (f80 (f81 ?v0) ?v1) ?v2) ?v3) f1) (=> (not (= (f11 (f12 ?v1) ?v2) f1)) (= (f8 (f9 (f66 ?v0) (f9 (f32 ?v1) ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (=> (not (= (f11 ?v_0 ?v2) f1)) (= (f11 ?v_0 (f9 (f77 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (f6 ?v_0 (f4 (f76 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 (f9 (f77 ?v1) ?v2)) f1) (=> (=> (= (f11 ?v_0 ?v1) f1) (=> (not (= (f11 ?v_0 ?v2) f1)) false)) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f76 ?v1) ?v2)) f1) (=> (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) false)) false)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f64 ?v0) f1) (= (f64 (f9 (f77 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f69 ?v0) f1) (= (f69 (f4 (f76 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3)) (= (f4 (f76 ?v0) ?v0) f26)))
(assert (forall ((?v0 S7)) (= (f9 (f77 ?v0) ?v0) f33)))
(assert (forall ((?v0 S3)) (= (f4 (f76 ?v0) f26) ?v0)))
(assert (forall ((?v0 S7)) (= (f9 (f77 ?v0) f33) ?v0)))
(assert (forall ((?v0 S3)) (= (f4 (f76 f26) ?v0) f26)))
(assert (forall ((?v0 S7)) (= (f9 (f77 f33) ?v0) f33)))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f64 ?v0) f1) (= (= (f64 (f9 (f77 ?v1) ?v0)) f1) (= (f64 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f69 ?v0) f1) (= (= (f69 (f4 (f76 ?v1) ?v0)) f1) (= (f69 ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f9 (f77 ?v0) ?v1) (f36 (f9 (f14 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f4 (f76 ?v0) ?v1) (f35 (f4 (f13 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (= (= (f11 ?v_0 (f9 (f77 ?v1) ?v2)) f1) (and (= (f11 ?v_0 ?v1) f1) (not (= (f11 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f76 ?v1) ?v2)) f1) (and (= (f6 ?v_0 ?v1) f1) (not (= (f6 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f9 (f77 ?v0) ?v1))) (= (f9 (f77 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 (f76 ?v0) ?v1))) (= (f4 (f76 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 (f9 (f77 ?v1) ?v2)) f1) (= (f11 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f76 ?v1) ?v2)) f1) (= (f6 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f12 ?v0))) (=> (= (f11 ?v_0 (f9 (f77 ?v1) ?v2)) f1) (=> (= (f11 ?v_0 ?v2) f1) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f76 ?v1) ?v2)) f1) (=> (= (f6 ?v_0 ?v2) f1) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f23 ?v0)) (?v_1 (f4 (f76 ?v1) ?v2))) (= (f4 (f76 (f4 ?v_0 ?v1)) ?v2) (ite (= (f6 (f7 ?v0) ?v2) f1) ?v_1 (f4 ?v_0 ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (let ((?v_0 (f32 ?v0)) (?v_1 (f9 (f77 ?v1) ?v2))) (= (f9 (f77 (f9 ?v_0 ?v1)) ?v2) (ite (= (f11 (f12 ?v0) ?v2) f1) ?v_1 (f9 ?v_0 ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f76 (f4 (f23 ?v0) ?v2)) ?v1) (f4 (f76 ?v2) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7)) (=> (= (f11 (f12 ?v0) ?v1) f1) (= (f9 (f77 (f9 (f32 ?v0) ?v2)) ?v1) (f9 (f77 ?v2) ?v1)))))
(assert (forall ((?v0 S32) (?v1 S2)) (= (f3 (f4 (f78 (f79 ?v0) ?v1) f26) ?v1) f1)))
(assert (forall ((?v0 S33) (?v1 S6)) (= (f8 (f9 (f80 (f81 ?v0) ?v1) f33) ?v1) f1)))
(assert (forall ((?v0 S32) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f78 (f79 ?v0) ?v1) f26) ?v2) f1) (=> (=> (= ?v2 ?v1) false) false))))
(assert (forall ((?v0 S33) (?v1 S6) (?v2 S6)) (=> (= (f8 (f9 (f80 (f81 ?v0) ?v1) f33) ?v2) f1) (=> (=> (= ?v2 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S32) (?v3 S2) (?v4 S2)) (let ((?v_0 (f78 (f79 ?v2) ?v3))) (=> (not (= (f6 (f7 ?v0) ?v1) f1)) (=> (= (f3 (f4 ?v_0 ?v1) ?v4) f1) (= (f3 (f4 ?v_0 (f4 (f23 ?v0) ?v1)) (f70 (f71 ?v2 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S33) (?v3 S6) (?v4 S6)) (let ((?v_0 (f80 (f81 ?v2) ?v3))) (=> (not (= (f11 (f12 ?v0) ?v1) f1)) (=> (= (f8 (f9 ?v_0 ?v1) ?v4) f1) (= (f8 (f9 ?v_0 (f9 (f32 ?v0) ?v1)) (f72 (f73 ?v2 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f76 ?v0)) (?v_1 (f23 ?v1))) (= (f4 ?v_0 (f4 ?v_1 ?v2)) (f4 (f76 (f4 ?v_0 ?v2)) (f4 ?v_1 f26))))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (let ((?v_0 (f77 ?v0)) (?v_1 (f32 ?v1))) (= (f9 ?v_0 (f9 ?v_1 ?v2)) (f9 (f77 (f9 ?v_0 ?v2)) (f9 ?v_1 f33))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f76 ?v0)) (?v_1 (f23 ?v1))) (= (f4 ?v_0 (f4 ?v_1 ?v2)) (f4 (f76 (f4 ?v_0 (f4 ?v_1 f26))) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S7)) (let ((?v_0 (f77 ?v0)) (?v_1 (f32 ?v1))) (= (f9 ?v_0 (f9 ?v_1 ?v2)) (f9 (f77 (f9 ?v_0 (f9 ?v_1 f33))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f23 ?v0))) (= (f4 ?v_0 (f4 (f76 ?v1) (f4 ?v_0 f26))) (f4 ?v_0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (let ((?v_0 (f32 ?v0))) (= (f9 ?v_0 (f9 (f77 ?v1) (f9 ?v_0 f33))) (f9 ?v_0 ?v1)))))
(assert (forall ((?v0 S24)) (= (f52 f53 (f54 f55 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f54 f55 (f52 f53 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f54 f55 (f52 f53 ?v0)) 0))))
(check-sat)
(exit)
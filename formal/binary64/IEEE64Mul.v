(** Dekker's product and the double-word products in IEEE 754 binary64
    arithmetic. The split's head is its operand rounded to 26 bits (Flocq's
    [Veltkamp]), so it is no larger than the operand's power-of-two bound; with
    that, every operation's naive bound stays below [2^1024] on the stated
    domains, and each algorithm returns its binary64-model value. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Flocq.Pff Require Import Pff2Flocq.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add.
Require TwoProdBinary64.

Open Scope R_scope.

Lemma bpow_succ2 e : bpow radix2 (e + 1) = 2 * bpow radix2 e.
Proof. rewrite bpow_plus, bpow_1. simpl. ring. Qed.

(** [2^c <= 2^n] for [c <= n]: lets [lia] treat a power with a variable
    exponent as an atom with a known lower bound. *)
Lemma pow_ge c n : (0 <= c <= n)%Z -> (2 ^ c <= 2 ^ n)%Z.
Proof. intros H. apply Z.pow_le_mono_r; lia. Qed.

(** [2^27 + 1] is below [2^28]. *)
Lemma splitter_lt : bpow radix2 27 + 1 <= bpow radix2 28.
Proof.
  change 28%Z with (27 + 1)%Z. rewrite bpow_succ2.
  assert (1 <= bpow radix2 27) by (apply (bpow_le radix2 0 27); lia). lra.
Qed.

(** [2^27 + 1], the split's constant. *)
Definition splitter : f64 := binary_normalize 53 1024 eq_refl eq_refl mode_NE 134217729 0 false.

Lemma splitter_ok : finite splitter /\ B splitter = bpow radix2 27 + 1.
Proof.
  assert (V : F2R (Float radix2 134217729 0) = bpow radix2 27 + 1)
    by (unfold F2R; simpl; lra).
  assert (Fv : fmtF (F2R (Float radix2 134217729 0)))
    by (apply generic_format_FLT, (FLT_spec radix2 emin prec _ (Float radix2 134217729 0));
        [reflexivity | simpl; unfold prec; lia | simpl; unfold emin; lia]).
  assert (R : rndF (F2R (Float radix2 134217729 0)) = bpow radix2 27 + 1)
    by (rewrite round_generic; auto with typeclass_instances).
  pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE 134217729 0 false) as C.
  rewrite Rlt_bool_true in C.
  - destruct C as [C1 [C2 _]]. split; [exact C2 | ]. rewrite <- R. exact C1.
  - change (Rabs (rndF (F2R (Float radix2 134217729 0))) < bpow radix2 1024).
    rewrite R, Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 27); lra).
    apply Rle_lt_trans with (1 := splitter_lt). apply bpow_lt. lia.
Qed.

Definition split64 (x : f64) : f64 * f64 :=
  let p := fmul x splitter in
  let q := fsub x p in
  let h := fadd q p in
  (h, fsub x h).

Definition two_prod64 (a b : f64) : f64 * f64 :=
  let p := fmul a b in
  let '(ah, al) := split64 a in
  let '(bh, bl) := split64 b in
  let e := fadd (fadd (fadd (fsub (fmul ah bh) p) (fmul ah bl)) (fmul al bh)) (fmul al bl) in
  (p, e).

Lemma split64_ok E x : finite x -> bnd 1 E (B x) -> (-1074 <= E <= 994)%Z ->
  finite (fst (split64 x)) /\ finite (snd (split64 x))
  /\ B (fst (split64 x)) = TwoProdBinary64.split_head (B x)
  /\ B (snd (split64 x)) = TwoProdBinary64.split_tail (B x)
  /\ bnd 1 E (B (fst (split64 x))) /\ bnd 2 E (B (snd (split64 x))).
Proof.
  intros Fx Bx He. destruct splitter_ok as [Fc Ec].
  assert (Bc : bnd 1 28 (B splitter)).
  { unfold bnd. rewrite Ec, Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 27); lra).
    rewrite Rmult_1_l. exact splitter_lt. }
  unfold split64; cbn [fst snd].
  pose proof (pow_ge 2 (1024 - (E + 28)) ltac:(lia)) as P28.
  pose proof (pow_ge 2 (1024 - E) ltac:(lia)) as P0.
  change (2 ^ 2)%Z with 4%Z in P28, P0.
  step (fmul_bnd 1 (E + 28) x splitter Fx Fc) (bnd_mult _ _ _ _ _ _ Bx Bc).
  destruct S as [Fp [Ep Bp]]. set (p := fmul x splitter) in *.
  assert (Bx' : bnd 1 (E + 28) (B x)) by (apply (bnd_up 1 E); [lia | lia | exact Bx]).
  step (fsub_bnd 2 (E + 28) x p Fx Fp) (bnd_minus _ _ _ _ _ Bx' Bp).
  destruct S as [Fq [Eq Bq]]. set (q := fsub x p) in *.
  step (fadd_bnd 3 (E + 28) q p Fq Fp) (bnd_plus _ _ _ _ _ Bq Bp).
  destruct S as [Fh [Eh _]]. set (h := fadd q p) in *.
  (* The head is x rounded to 26 bits, so it is bounded by x's bound. *)
  assert (Hh : B h = TwoProdBinary64.split_head (B x)).
  { rewrite Eh, Eq, Ep, Ec. reflexivity. }
  assert (Bh : bnd 1 E (B h)).
  { destruct (Veltkamp radix2 emin prec ne 27 ltac:(unfold prec; lia) ltac:(unfold emin; lia)
                ltac:(lia) ltac:(unfold prec; lia) (B x) (B_fmt x)) as [ch V].
    unfold bnd. rewrite Rmult_1_l, Hh.
    unfold TwoProdBinary64.split_head. cbv zeta.
    change (TwoProdBinary64.rn (B x * (bpow radix2 27 + 1))) with (rndF (B x * (bpow radix2 27 + 1))).
    change (TwoProdBinary64.rn (B x - rndF (B x * (bpow radix2 27 + 1))))
      with (rndF (B x - rndF (B x * (bpow radix2 27 + 1)))).
    change (TwoProdBinary64.rn (rndF (B x - rndF (B x * (bpow radix2 27 + 1))) + rndF (B x * (bpow radix2 27 + 1))))
      with (rndF (rndF (B x - rndF (B x * (bpow radix2 27 + 1))) + rndF (B x * (bpow radix2 27 + 1)))).
    rewrite V.
    apply abs_round_le_generic; auto with typeclass_instances.
    - apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
    - unfold bnd in Bx. lra. }
  step (fsub_bnd 2 E x h Fx Fh) (bnd_minus _ _ _ _ _ Bx Bh).
  destruct S as [Ft [Et Bt]].
  repeat split; try assumption.
  unfold TwoProdBinary64.split_tail. rewrite Et, <- Hh. reflexivity.
Qed.

Lemma two_prod64_ok Ea Eb a b : finite a -> finite b -> bnd 1 Ea (B a) -> bnd 1 Eb (B b) ->
  (-537 <= Ea <= 994)%Z -> (-537 <= Eb <= 994)%Z -> (Ea + Eb <= 1020)%Z ->
  finite (fst (two_prod64 a b)) /\ finite (snd (two_prod64 a b))
  /\ (B (fst (two_prod64 a b)), B (snd (two_prod64 a b))) = two_prod (B a) (B b)
  /\ bnd 1 (Ea + Eb) (B (fst (two_prod64 a b))) /\ bnd 10 (Ea + Eb) (B (snd (two_prod64 a b))).
Proof.
  intros Fa Fb Ba Bb Ha Hb Hab.
  pose proof (pow_ge 4 (1024 - (Ea + Eb)) ltac:(lia)) as P. change (2 ^ 4)%Z with 16%Z in P.
  destruct (split64_ok Ea a Fa Ba ltac:(lia)) as [Fah [Fal [Hah [Hal [Bah Bal]]]]].
  destruct (split64_ok Eb b Fb Bb ltac:(lia)) as [Fbh [Fbl [Hbh [Hbl [Bbh Bbl]]]]].
  unfold two_prod64.
  destruct (split64 a) as [ah al]. destruct (split64 b) as [bh bl]. cbn [fst snd] in *.
  step (fmul_bnd 1 (Ea + Eb) a b Fa Fb) (bnd_mult _ _ _ _ _ _ Ba Bb).
  destruct S as [Fp [Ep Bp]].
  step (fmul_bnd 1 (Ea + Eb) ah bh Fah Fbh) (bnd_mult _ _ _ _ _ _ Bah Bbh).
  destruct S as [Fm1 [Em1 Bm1]].
  step (fsub_bnd 2 (Ea + Eb) (fmul ah bh) (fmul a b) Fm1 Fp) (bnd_minus _ _ _ _ _ Bm1 Bp).
  destruct S as [Fd1 [Ed1 Bd1]].
  step (fmul_bnd 2 (Ea + Eb) ah bl Fah Fbl) (bnd_mult _ _ _ _ _ _ Bah Bbl).
  destruct S as [Fm2 [Em2 Bm2]].
  step (fadd_bnd 4 (Ea + Eb) _ _ Fd1 Fm2) (bnd_plus _ _ _ _ _ Bd1 Bm2).
  destruct S as [Fd2 [Ed2 Bd2]].
  step (fmul_bnd 2 (Ea + Eb) al bh Fal Fbh) (bnd_mult _ _ _ _ _ _ Bal Bbh).
  destruct S as [Fm3 [Em3 Bm3]].
  step (fadd_bnd 6 (Ea + Eb) _ _ Fd2 Fm3) (bnd_plus _ _ _ _ _ Bd2 Bm3).
  destruct S as [Fd3 [Ed3 Bd3]].
  step (fmul_bnd 4 (Ea + Eb) al bl Fal Fbl) (bnd_mult _ _ _ _ _ _ Bal Bbl).
  destruct S as [Fm4 [Em4 Bm4]].
  step (fadd_bnd 10 (Ea + Eb) _ _ Fd3 Fm4) (bnd_plus _ _ _ _ _ Bd3 Bm4).
  destruct S as [Fe [Ee Be]].
  repeat split; try assumption.
  unfold two_prod, TwoProdBinary64.two_prod_e, TwoProdBinary64.two_prod_p. cbv zeta.
  rewrite <- Hah, <- Hal, <- Hbh, <- Hbl.
  rewrite Ee, Em4, Ed3, Em3, Ed2, Em2, Ed1, Em1, Ep.
  unfold Rminus. rewrite (Rplus_comm (- _)). reflexivity.
Qed.

Definition mul_f64_64 (xh xl y : f64) : f64 * f64 :=
  let '(ch, cl1) := two_prod64 xh y in
  let cl2 := fmul xl y in
  let '(th, tl1) := fast_two_sum64 ch cl2 in
  let tl2 := fadd tl1 cl1 in
  fast_two_sum64 th tl2.

Definition mul64 (xh xl yh yl : f64) : f64 * f64 :=
  let '(ch, cl1) := two_prod64 xh yh in
  let tl1 := fmul xh yl in
  let tl2 := fmul xl yh in
  let cl2 := fadd tl1 tl2 in
  let cl3 := fadd cl1 cl2 in
  fast_two_sum64 ch cl3.

Lemma mul_f64_64_ok Ex Ey xh xl y : finite xh -> finite xl -> finite y ->
  bnd 1 Ex (B xh) -> bnd 1 Ex (B xl) -> bnd 1 Ey (B y) ->
  (-537 <= Ex <= 994)%Z -> (-537 <= Ey <= 994)%Z -> (Ex + Ey <= 1018)%Z ->
  finite (fst (mul_f64_64 xh xl y)) /\ finite (snd (mul_f64_64 xh xl y))
  /\ (B (fst (mul_f64_64 xh xl y)), B (snd (mul_f64_64 xh xl y))) = mul_f64 (B xh) (B xl) (B y)
  /\ bnd 28 (Ex + Ey) (B (fst (mul_f64_64 xh xl y))) /\ bnd 56 (Ex + Ey) (B (snd (mul_f64_64 xh xl y))).
Proof.
  intros Fxh Fxl Fy Bxh Bxl By Hx Hy Hxy.
  pose proof (pow_ge 6 (1024 - (Ex + Ey)) ltac:(lia)) as P. change (2 ^ 6)%Z with 64%Z in P.
  destruct (two_prod64_ok Ex Ey xh y Fxh Fy Bxh By ltac:(lia) ltac:(lia) ltac:(lia))
    as [Fch [Fcl1 [Ec [Bch Bcl1]]]].
  unfold mul_f64_64, mul_f64. rewrite <- Ec.
  destruct (two_prod64 xh y) as [ch cl1]. cbn [fst snd] in *.
  step (fmul_bnd 1 (Ex + Ey) xl y Fxl Fy) (bnd_mult _ _ _ _ _ _ Bxl By).
  destruct S as [Fcl2 [Ecl2 Bcl2]].
  destruct (fast_two_sum64_ok 1 (Ex + Ey) ch (fmul xl y) Fch Fcl2 Bch Bcl2
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fth [Ftl1 [Et [Bth Btl1]]]].
  rewrite <- Ecl2, <- Et.
  destruct (fast_two_sum64 ch (fmul xl y)) as [th tl1]. cbn [fst snd] in *.
  step (fadd_bnd 14 (Ex + Ey) tl1 cl1 Ftl1 Fcl1) (bnd_plus _ _ _ _ _ Btl1 Bcl1).
  destruct S as [Ftl2 [Etl2 Btl2]].
  destruct (fast_two_sum64_ok 14 (Ex + Ey) th (fadd tl1 cl1) Fth Ftl2 (w 14%Z Bth) Btl2
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl [Ez [Bzh Bzl]]]].
  rewrite <- Etl2. repeat split; assumption.
Qed.

Lemma mul64_ok E xh xl yh yl : finite xh -> finite xl -> finite yh -> finite yl ->
  bnd 1 E (B xh) -> bnd 1 E (B xl) -> bnd 1 E (B yh) -> bnd 1 E (B yl) -> (-268 <= E <= 508)%Z ->
  finite (fst (mul64 xh xl yh yl)) /\ finite (snd (mul64 xh xl yh yl))
  /\ (B (fst (mul64 xh xl yh yl)), B (snd (mul64 xh xl yh yl))) = mul (B xh) (B xl) (B yh) (B yl).
Proof.
  intros Fxh Fxl Fyh Fyl Bxh Bxl Byh Byl He.
  pose proof (pow_ge 6 (1024 - (E + E)) ltac:(lia)) as P. change (2 ^ 6)%Z with 64%Z in P.
  destruct (two_prod64_ok E E xh yh Fxh Fyh Bxh Byh ltac:(lia) ltac:(lia) ltac:(lia))
    as [Fch [Fcl1 [Ec [Bch Bcl1]]]].
  unfold mul64, mul. rewrite <- Ec.
  destruct (two_prod64 xh yh) as [ch cl1]. cbn [fst snd] in *.
  step (fmul_bnd 1 (E + E) xh yl Fxh Fyl) (bnd_mult _ _ _ _ _ _ Bxh Byl).
  destruct S as [Ft1 [Et1 Bt1]].
  step (fmul_bnd 1 (E + E) xl yh Fxl Fyh) (bnd_mult _ _ _ _ _ _ Bxl Byh).
  destruct S as [Ft2 [Et2 Bt2]].
  step (fadd_bnd 2 (E + E) _ _ Ft1 Ft2) (bnd_plus _ _ _ _ _ Bt1 Bt2).
  destruct S as [Fc2 [Ec2 Bc2]].
  step (fadd_bnd 12 (E + E) _ _ Fcl1 Fc2) (bnd_plus _ _ _ _ _ Bcl1 Bc2).
  destruct S as [Fc3 [Ec3 Bc3]].
  destruct (fast_two_sum64_ok 12 (E + E) ch _ Fch Fc3 (w 12%Z Bch) Bc3
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl [Ez _]]].
  rewrite Ec3, Ec2, Et1, Et2 in Ez. repeat split; assumption.
Qed.

(** The bounds, for IEEE inputs with every word at most [2^508] in magnitude:
    no operation overflows. The underflow conditions are those of
    [Binary64Mul.v]. *)
Theorem mul_f64_ieee xh xl y :
  finite xh -> finite xl -> finite y -> B xh = rndF (B xh + B xl) ->
  Rabs (B xh) <= bpow radix2 508 -> Rabs (B xl) <= bpow radix2 508 -> Rabs (B y) <= bpow radix2 508 ->
  in_two_prod_domain (B xh) (B y) -> normal_or_zero (B xl * B y) ->
  let '(zh, zl) := mul_f64_64 xh xl y in
  finite zh /\ finite zl /\
  Rabs ((B zh + B zl - (B xh + B xl) * B y) / ((B xh + B xl) * B y))
    <= 3 / 2 * bpow radix2 (- prec) ^ 2 + 4 * bpow radix2 (- prec) ^ 3.
Proof.
  intros Fxh Fxl Fy E Bh Bl By Dh Dl.
  assert (U : forall v, Rabs v <= bpow radix2 508 -> bnd 1 508 v) by (intros v Hv; unfold bnd; lra).
  destruct (mul_f64_64_ok 508 508 xh xl y Fxh Fxl Fy (U _ Bh) (U _ Bl) (U _ By) ltac:(lia) ltac:(lia) ltac:(lia))
    as [Fzh [Fzl [Ez _]]].
  pose proof (mul_f64_bound (B xh) (B xl) (B y) (B_fmt xh) (B_fmt xl) (B_fmt y) E Dh Dl) as Bd.
  rewrite <- Ez in Bd.
  destruct (mul_f64_64 xh xl y) as [zh zl]. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

Theorem mul_ieee xh xl yh yl :
  finite xh -> finite xl -> B xh = rndF (B xh + B xl) ->
  finite yh -> finite yl -> B yh = rndF (B yh + B yl) ->
  Rabs (B xh) <= bpow radix2 508 -> Rabs (B xl) <= bpow radix2 508 ->
  Rabs (B yh) <= bpow radix2 508 -> Rabs (B yl) <= bpow radix2 508 ->
  in_two_prod_domain (B xh) (B yh) -> normal_or_zero (B xh * B yl) -> normal_or_zero (B xl * B yh) ->
  let '(zh, zl) := mul64 xh xl yh yl in
  finite zh /\ finite zl /\
  Rabs ((B zh + B zl - (B xh + B xl) * (B yh + B yl)) / ((B xh + B xl) * (B yh + B yl)))
    < 5 * (bpow radix2 (- prec) * bpow radix2 (- prec)).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Bxh Bxl Byh Byl Dhh Dhl Dlh.
  assert (U : forall v, Rabs v <= bpow radix2 508 -> bnd 1 508 v) by (intros v Hv; unfold bnd; lra).
  destruct (mul64_ok 508 xh xl yh yl Fxh Fxl Fyh Fyl (U _ Bxh) (U _ Bxl) (U _ Byh) (U _ Byl) ltac:(lia))
    as [Fzh [Fzl Ez]].
  pose proof (mul_bound (B xh) (B xl) (B yh) (B yl) (B_fmt xh) (B_fmt xl) Ex
                (B_fmt yh) (B_fmt yl) Ey Dhh Dhl Dlh) as Bd.
  rewrite <- Ez in Bd.
  destruct (mul64 xh xl yh yl) as [zh zl]. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

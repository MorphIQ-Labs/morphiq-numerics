(** Direct IEEE reciprocal-square correction in the large positive tail.
    All operations include gradual underflow; no normal-output assumption. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal ErfcxEntryTables.
Require erfcx_tail_correction.
Open Scope R_scope.

Definition three_quarters : f64 := b64_of_bits 4604930618986332160.
Definition fifteen_eighths : f64 := b64_of_bits 4611123068473966592.
Lemma three_quarters_ok : finite three_quarters /\ B three_quarters = 3/4.
Proof.
 split.
 - exact (bits_finite 4604930618986332160 false 6755399441055744 (-53) eq_refl).
 - pose proof (bits_val 4604930618986332160 false 6755399441055744 53 eq_refl) as V.
   unfold three_quarters. rewrite V. simpl. field.
Qed.
Lemma fifteen_eighths_ok : finite fifteen_eighths /\ B fifteen_eighths = 15/8.
Proof.
 split.
 - exact (bits_finite 4611123068473966592 false 8444249301319680 (-52) eq_refl).
 - pose proof (bits_val 4611123068473966592 false 8444249301319680 52 eq_refl) as V.
   unfold fifteen_eighths. rewrite V. simpl. field.
Qed.
Definition tail_polynomial t := t*(-(1/2)+t*((3/4)-(15/8)*t)).
Definition tail_correction64 x :=
 let y := fdiv one x in let t := fmul y y in
 fmul t (fadd neg_half (fmul t (fsub three_quarters (fmul fifteen_eighths t)))).

Lemma tail_correction_model Y : 0 <= Y <= /512 ->
 let y := rn Y in let t := rn (y*y) in
 let v := rn ((3/4)-rn ((15/8)*t)) in
 let w := rn (-(1/2)+rn (t*v)) in let u := rn (t*w) in
 - /2^69 <= u-tail_polynomial (Y*Y) <= /2^69 /\
 0 <= y <= /512 /\ 0 <= t <= /2^18 /\
 749/1000 <= v <= 3/4 /\ -(1/2) <= w <= -(499/1000) /\
 - /2^18 <= u <= 0.
Proof.
 intros H. cbv zeta. unfold tail_polynomial.
 repeat split; erfcx_goal (erfcx_tail_correction.l1 Y).
Qed.

Theorem tail_correction_ieee x : finite x -> 512 <= B x ->
 finite (tail_correction64 x) /\
 - /2^69 <= B (tail_correction64 x)-tail_polynomial ((1/B x)*(1/B x)) <= /2^69 /\
 - /2^18 <= B (tail_correction64 x) <= 0.
Proof.
 intros Fx X.
 assert (Y : 0 <= 1/B x <= /512).
 { unfold Rdiv. rewrite Rmult_1_l. split; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]. }
 destruct one_ok as [F1 B1].
 destruct three_quarters_ok as [Fc Bc]. destruct fifteen_eighths_ok as [Fd Bd].
 destruct neg_half_ok as [Fn [Bn _]].
 assert (NegHalf : neg_half_r = -(1/2)) by (unfold neg_half_r,float2R,F2R; simpl; bpow_num; field).
 rewrite NegHalf in Bn.
 pose proof (tail_correction_model (1/B x) Y) as M. cbv zeta in M.
 destruct M as [Me [My [Mt [Mv [Mw Mu]]]]].
 destruct (fdiv_ok 1 0 one x F1 ltac:(lra) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite B1,Rmult_1_l; change (bpow radix2 0) with 1; apply Rabs_le; lra)) as [Fy By].
 rewrite B1 in By. change (B (fdiv one x)=rn (1/B x)) in By.
 rewrite <- By in Me,My,Mt,Mv,Mw,Mu.
 set (y := fdiv one x) in *.
 destruct (fmul_ok 1 0 y y Fy Fy ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1; apply Rabs_le; nra)) as [Ft Bt].
 change (B (fmul y y)=rn (B y*B y)) in Bt.
 rewrite <- Bt in Me,Mt,Mv,Mw,Mu. set (t := fmul y y) in *.
 destruct (fmul_bnd 1 0 fifteen_eighths t Fd Ft ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Bd,Rmult_1_l; change (bpow radix2 0) with 1; apply Rabs_le; nra)) as [Fa [Ba A]].
 unfold bnd in A. rewrite Rmult_1_l in A. change (bpow radix2 0) with 1 in A.
 destruct (fsub_ok 2 0 three_quarters (fmul fifteen_eighths t) Fc Fa ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Bc; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        pose proof (Rabs_le_inv _ _ A); apply Rabs_le; lra)) as [Fv Bv].
 rewrite Ba,Bc,Bd in Bv.
 change (B (fsub three_quarters (fmul fifteen_eighths t))=rn ((3/4)-rn ((15/8)*B t))) in Bv.
 rewrite <- Bv in Me,Mv,Mw,Mu. set (v := fsub three_quarters (fmul fifteen_eighths t)) in *.
 destruct (fmul_bnd 1 0 t v Ft Fv ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1; apply Rabs_le; nra)) as [Fb [Bb Bnd]].
 unfold bnd in Bnd. rewrite Rmult_1_l in Bnd. change (bpow radix2 0) with 1 in Bnd.
 destruct (fadd_ok 2 0 neg_half (fmul t v) Fn Fb ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Bn; change (bpow radix2 0) with 1; rewrite Rmult_1_r;
        pose proof (Rabs_le_inv _ _ Bnd); apply Rabs_le; lra)) as [Fw Bw].
 rewrite Bb,Bn in Bw. change (B (fadd neg_half (fmul t v))=rn (-(1/2)+rn (B t*B v))) in Bw.
 rewrite <- Bw in Me,Mw,Mu. set (w := fadd neg_half (fmul t v)) in *.
 destruct (fmul_ok 1 0 t w Ft Fw ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 0) with 1; apply Rabs_le; nra)) as [Fu Bu].
 change (B (fmul t w)=rn (B t*B w)) in Bu. rewrite <- Bu in Me,Mu.
 unfold tail_correction64. change (finite (fmul t w) /\
  - /2^69 <= B (fmul t w)-tail_polynomial ((1/B x)*(1/B x)) <= /2^69 /\
  - /2^18 <= B (fmul t w) <= 0).
 repeat split; tauto.
Qed.

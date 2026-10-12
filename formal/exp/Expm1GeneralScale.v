(** The general fallback's powers of two and exact scaling, including the
    subnormal 2^-1024 constant and a low word scaled down to the binary64 grid. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 Grid Encodings RoundingTest.
Require Import Expm1Scale Ln1pLemmas StageGappa.
Open Scope R_scope.
Definition em_general_pow2 k :=
 if (-1022 <=? k)%Z then em_pow2 k else b64_of_bits (Z.shiftl 1 (k+1074)).
Lemma em_general_pow2_ok k : (-1024 <= k <= 1023)%Z ->
 finite (em_general_pow2 k) /\ B (em_general_pow2 k) = bpow radix2 k.
Proof.
 intros K. unfold em_general_pow2. destruct (-1022 <=? k)%Z eqn:E.
 - apply Z.leb_le in E. apply em_pow2_ok; lia.
 - apply Z.leb_gt in E. assert (k = -1024 \/ k = -1023)%Z by lia.
   destruct H as [-> | ->]; split.
   + exact (bits_finite 1125899906842624 false 1125899906842624 (-1074) eq_refl).
   + change (B (b64_of_bits 1125899906842624) = bpow radix2 (-1024)).
     rewrite (bits_val 1125899906842624 false 1125899906842624 1074 eq_refl). cbn [SpecFloat.cond_Zopp]. apply Rle_antisym; interval with (i_prec 64).
   + exact (bits_finite 2251799813685248 false 2251799813685248 (-1074) eq_refl).
   + change (B (b64_of_bits 2251799813685248) = bpow radix2 (-1023)).
     rewrite (bits_val 2251799813685248 false 2251799813685248 1074 eq_refl). cbn [SpecFloat.cond_Zopp]. apply Rle_antisym; interval with (i_prec 64).
Qed.

Lemma scaled_fmt_grid a q k : fmtF a -> on_grid q a -> (-1074 <= q+k)%Z ->
 fmtF (a*bpow radix2 k).
Proof.
 intros Fa G Q.
 destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (a*bpow radix2 k))) as [Normal | Small].
 - apply generic_format_FLT_FLX; [exact Normal | ].
   destruct (FLX_format_generic radix2 53 a (generic_format_FLX_FLT radix2 (-1074) 53 a Fa)) as [[m e] Val M].
   apply generic_format_FLX. apply (FLX_spec radix2 53 _ (Float radix2 m (e+k))).
   + rewrite Val. unfold F2R; cbn [Fnum Fexp]. rewrite bpow_plus. ring.
   + exact M.
 - apply generic_format_FLT_FIX; [exact _ | | ].
   + apply Rle_trans with (bpow radix2 (-1022)); [lra | apply bpow_le; unfold emin,prec; lia].
   + assert (Gk : on_grid k (bpow radix2 k)) by (exists 1%Z; ring).
     destruct (grid_le (q+k) (-1074) _ Q (grid_mult q k _ _ G Gk)) as [m V].
     apply generic_format_FIX. apply (FIX_spec radix2 (-1074) _ (Float radix2 m (-1074))); [exact V | reflexivity].
Qed.

Theorem em_scale_exact a q k : finite a -> on_grid q (B a) ->
 (-1024 <= q)%Z -> (-1074 <= q+k)%Z -> (-54 <= k <= 1024)%Z ->
 Rabs (B a*bpow radix2 k) < bpow radix2 1024 ->
 finite (scale a k) /\ B (scale a k) = B a*bpow radix2 k.
Proof.
 intros Fa G Q Qk K Ov.
 assert (Fmt : fmtF (B a*bpow radix2 k)) by (apply (scaled_fmt_grid _ q); [apply B_fmt | exact G | exact Qk]).
 unfold scale. destruct (Z.eqb_spec k 1024) as [-> | Ne].
 - destruct (pow2_f 1023 ltac:(lia)) as [B1 F1]. destruct (pow2_f 1 ltac:(lia)) as [B2 F2]. unfold pow2f.
   assert (Half : Rabs (B a*bpow radix2 1023) < bpow radix2 1024).
   { rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 1023)) by apply bpow_ge_0.
     apply Rle_lt_trans with (Rabs (B a)*bpow radix2 1024).
     - apply Rmult_le_compat_l; [apply Rabs_pos | apply bpow_le; lia].
     - rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 1024)) in Ov by apply bpow_ge_0. exact Ov. }
   destruct (fmul_exact a _ Fa F1) as [Fm Bm].
   + rewrite B1. apply (scaled_fmt_grid _ q); [apply B_fmt | exact G | lia].
   + rewrite B1. exact Half.
   + assert (E : B a*bpow radix2 1023*bpow radix2 1 = B a*bpow radix2 1024) by (rewrite Rmult_assoc, <- bpow_plus; reflexivity).
     destruct (fmul_exact _ _ Fm F2) as [Fv Bv].
     * rewrite Bm, B1, B2, E. exact Fmt.
     * rewrite Bm, B1, B2, E. exact Ov.
     * split; [exact Fv | rewrite Bv, Bm, B1, B2; exact E].
 - destruct (pow2_f k ltac:(lia)) as [Bp Fp]. unfold pow2f.
   destruct (fmul_exact a _ Fa Fp) as [Fv Bv].
   + rewrite Bp. exact Fmt.
   + rewrite Bp. exact Ov.
   + split; [exact Fv | rewrite Bv, Bp; reflexivity].
Qed.

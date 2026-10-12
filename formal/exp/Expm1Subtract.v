(** Compensated subtraction of 2^-k and the executable error budget. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid Encodings RoundingConstant RoundingTest.
Require Import StageGappa Ln1pLemmas Ln1pReduction Ln1pTest.
Open Scope R_scope.

Lemma small_power x e t : Rabs x <= bpow radix2 e -> (e <= t)%Z -> Rabs x <= bpow radix2 t.
Proof. intros H E. apply Rle_trans with (1 := H). apply bpow_le; lia. Qed.
Lemma round_power x e : Rabs x <= bpow radix2 e -> (-1074 <= e)%Z -> Rabs (rndF x) <= bpow radix2 e.
Proof. intros H E. apply abs_round_le_generic; try exact _; [apply generic_format_bpow; unfold FLT_exp, emin, prec; lia | exact H]. Qed.

Definition em_factor : f64 := b64_of_bits 4377498837804122112. (* 2^-51 *)
Lemma em_factor_ok : finite em_factor /\ B em_factor = bpow radix2 (-51).
Proof. exact (enc_pow2 (-51) ltac:(lia)). Qed.
Definition subtract_parts h l c base :=
 let '(s,e) := two_sum64 h (fneg c) in
 let lo := fadd e l in
 let eps := fadd base (fmul (fadd (b64_abs e) (b64_abs l)) em_factor) in
 (s,lo,eps).

Theorem subtract_parts_ok h l c base z :
 finite h -> finite l -> finite c -> finite base ->
 Rabs (B h) <= 4 -> Rabs (B l) <= bpow radix2 (-9) -> Rabs (B c) <= bpow radix2 54 ->
 bpow radix2 (-68) <= B base <= bpow radix2 (-59) ->
 Rabs (z - (B h + B l)) <= B base / 2 ->
 let '(s,lo,eps) := subtract_parts h l c base in
 finite s /\ finite lo /\ finite eps /\ 0 <= B eps /\
 Rabs (B s) <= bpow radix2 999 /\ Rabs (B lo) + B eps <= bpow radix2 999 /\
 Rabs ((z - B c) - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps.
Proof.
 intros Fh Fl Fc Fb Ah Al Ac Ab Ez.
 assert (Fn : finite (fneg c)) by (unfold fneg, b64_opp; rewrite is_finite_Bopp; exact Fc).
 assert (Bn : B (fneg c) = - B c) by apply B2R_Bopp.
 assert (Hh : Rabs (B h) <= bpow radix2 1020).
 { apply Rle_trans with (bpow radix2 2); [exact Ah | apply bpow_le; lia]. }
 assert (Hc : Rabs (B (fneg c)) <= bpow radix2 1020).
 { rewrite Bn, Rabs_Ropp. apply Rle_trans with (1 := Ac). apply bpow_le; lia. }
 pose proof (two_sum_ieee h (fneg c) Fh Fn Hh Hc) as TS.
 unfold subtract_parts. revert TS. generalize (two_sum64 h (fneg c)). intros [s e] [Fs [Fe [Bs Be]]].
 rewrite Bn in Bs, Be.
 assert (Sum : Rabs (B h + - B c) <= bpow radix2 55).
 { apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. bpow_num_all. lra. }
 assert (As : Rabs (B s) <= bpow radix2 55) by (rewrite Bs; apply round_power; [exact Sum | lia]).
 assert (Ae : Rabs (B e) <= 2).
 { pose proof (rnd_err_below (B h + - B c) 55 ltac:(lia) Sum) as E.
   rewrite <- Bs in E. replace (B s - (B h + - B c)) with (- B e) in E by lra.
   rewrite Rabs_Ropp in E. exact E. }
 set (a := Rabs (B e) + Rabs (B l)).
 assert (Aa : 0 <= a <= 4) by (unfold a; pose proof (Rabs_pos (B e)); pose proof (Rabs_pos (B l)); bpow_num_all; lra).
 assert (Slo : Rabs (B e + B l) <= a) by apply Rabs_triang.
 destruct (fadd_s e l Fe Fl) as [Flo Blo].
 { apply small_power with 2%Z; [change (bpow radix2 2) with 4; lra | lia]. }
 set (lo := fadd e l) in *.
 pose proof (rnd_sum_err (B e) (B l) (B_fmt e) (B_fmt l)) as Elo.
 rewrite <- Blo in Elo.
 assert (Dlo : Rabs (B lo - (B e + B l)) <= bpow radix2 (-53) * a).
 { apply Rle_trans with (1 := Elo). apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Slo]. }
 assert (Alo : Rabs (B lo) <= (1 + bpow radix2 (-53)) * a).
 { replace (B lo) with ((B lo - (B e + B l)) + (B e + B l)) by ring.
   apply Rle_trans with (1 := Rabs_triang _ _). nra. }
 assert (Fae : finite (b64_abs e)) by (unfold b64_abs; rewrite is_finite_Babs; exact Fe).
 assert (Fal : finite (b64_abs l)) by (unfold b64_abs; rewrite is_finite_Babs; exact Fl).
 destruct (fadd_s (b64_abs e) (b64_abs l) Fae Fal) as [Fa Ba].
 { rewrite !B_abs. change (Rabs a <= bpow radix2 1000).
   apply small_power with 2%Z; [rewrite Rabs_pos_eq by lra; exact (proj2 Aa) | lia]. }
 set (af := fadd (b64_abs e) (b64_abs l)) in *.
 rewrite !B_abs in Ba. change (B af = rndF a) in Ba.
 assert (Af : Rabs (B af) <= 4) by (rewrite Ba; apply (round_power a 2); [rewrite Rabs_pos_eq by lra; exact (proj2 Aa) | lia]).
 assert (Da : Rabs (B af - a) <= bpow radix2 (-52)).
 { rewrite Ba. apply (rnd_err_below a 2); [lia | rewrite Rabs_pos_eq by lra; exact (proj2 Aa)]. }
 destruct em_factor_ok as [Ff Bf].
 assert (Prod : Rabs (B af * B em_factor) <= bpow radix2 (-49)).
 { rewrite Bf, Rabs_mult, (Rabs_pos_eq (bpow radix2 _)) by apply bpow_ge_0. bpow_num_all. lra. }
 destruct (fmul_s af em_factor Fa Ff) as [Fp Bp]; [apply small_power with (-49)%Z; [exact Prod | lia] | ].
 set (p := fmul af em_factor) in *.
 assert (Ap : Rabs (B p) <= bpow radix2 (-49)) by (rewrite Bp; apply round_power; [exact Prod | lia]).
 assert (Dp : Rabs (B p - B af * bpow radix2 (-51)) <= bpow radix2 (-103)).
 { rewrite <- Bf, Bp. exact (rnd_err_below _ (-49) ltac:(lia) Prod). }
 assert (Sb : Rabs (B base + B p) <= bpow radix2 (-48)).
 { apply Rle_trans with (1 := Rabs_triang _ _). rewrite (Rabs_pos_eq (B base)); bpow_num_all; lra. }
 destruct (fadd_s base p Fb Fp) as [Fep Bep]; [apply small_power with (-48)%Z; [exact Sb | lia] | ].
 set (ep := fadd base p) in *.
 assert (Dep : Rabs (B ep - (B base + B p)) <= bpow radix2 (-102))
   by (rewrite Bep; exact (rnd_err_below _ (-48) ltac:(lia) Sb)).
 assert (Budget : Rabs (B ep - (B base + bpow radix2 (-51) * a)) <= bpow radix2 (-101)).
 { apply Rabs_le_inv in Da. apply Rabs_le_inv in Dp. apply Rabs_le_inv in Dep.
   apply Rabs_le. bpow_num_all. lra. }
 assert (Ep : 0 <= B ep <= bpow radix2 (-48)).
 { apply Rabs_le_inv in Budget. bpow_num_all. lra. }
 assert (Err : Rabs ((z - B c) - (B s + B lo)) <= B base / 2 + bpow radix2 (-53) * a).
 { replace ((z - B c) - (B s + B lo)) with ((z - (B h + B l)) - (B lo - (B e + B l))) by lra.
   apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
 repeat split; try assumption; try exact (proj1 Ep).
 - apply small_power with 55%Z; [exact As | lia].
 - apply Rle_trans with (bpow radix2 3); [bpow_num_all; lra | apply bpow_le; lia].
 - apply Rabs_le_inv in Budget. bpow_num_all. lra.
Qed.

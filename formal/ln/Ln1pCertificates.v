(** The certificates of [ln_1p]'s stages H and B over reals (docs/ln.md,
    section 7), written by generators/ln1p_certificates.py with the same bounds
    it writes into formal/ln/stage_*.g; do not edit. Each theorem is its
    certificate's, applied through the Coq proof Gappa writes for it: [rn] is
    Gappa's binary64 rounding, nearest-even, and each constant is [m·2^e] as
    Gappa reads it. *)

From Coq Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Gappa Require Gappa_definitions Gappa_pred_bnd Gappa_round_def.
Require ln_stage_h_q ln_stage_h_lr ln_stage_h_gz ln_stage_h_gs ln_stage_h_ga
  ln_stage_b_small_tail ln_stage_b_small ln_stage_b_lo ln_stage_b_total.

Open Scope R_scope.

Notation rn := (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE).

(** Normalizes a certificate's statement and ours alike, keeping the
    rounding, the real operators and the constants' [IZR] and [bpow]. *)
Ltac gnorm := cbv beta iota zeta delta -[round radix2 FLT_exp Gappa_round_def.rndNE Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult].
Ltac gnorm_in H := cbv beta iota zeta delta -[round radix2 FLT_exp Gappa_round_def.rndNE Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult] in H.
Ltac gnorm_all := repeat match goal with H : _ |- _ => progress gnorm_in H end; gnorm.

(** A goal [lo <= g <= hi] from certificate [l1], one side at a time: assume
    it fails, so the certificate's hypotheses hold and its conclusion fails.
    [gbound] for a certificate with one conclusion, [gbound_l] and [gbound_r]
    for the first or second of two. *)
Ltac gconcl := let Hb := fresh "Hb" in
  intros Hb; gnorm_in Hb; match goal with H : _ < _ |- _ => gnorm_in H end; lra.
Ltac ghyps := gnorm_all; repeat split; first [assumption | lra].
Ltac gbound l1 := split; (apply Rnot_lt_le; intros ?; apply l1; split; [ghyps | gconcl]).
Ltac gbound_l l1 := split; (apply Rnot_lt_le; intros ?; apply l1; split; [ghyps | left; gconcl]).
Ltac gbound_r l1 := split; (apply Rnot_lt_le; intros ?; apply l1; split; [ghyps | right; gconcl]).
(** * Stage H *)

Definition h3 : R := IZR 1501199875788995 * bpow radix2 (-52).
Definition h4 : R := IZR (-9007199254729289) * bpow radix2 (-55).
Definition h5 : R := IZR 3602889519051975 * bpow radix2 (-54).
Definition h6 : R := IZR (-6004817910265559) * bpow radix2 (-55).

(** [P(z)] by Estrin's scheme, rounded as the code rounds it, and exactly. *)
Definition h_p (z : R) : R :=
  let z2 := rn (z * z) in
  let t0 := rn (rn (z * h3) - IZR 1 * bpow radix2 (-1)) in
  let t1 := rn (rn (z * h5) + h4) in
  let a1 := rn (rn (z2 * h6) + t1) in
  rn (rn (z2 * a1) + t0).
Definition h_q (z : R) : R := rn (rn (z * z) * h_p z).
Definition h_Pz (z : R) : R := z * z * (z * z * h6 + (z * h5 + h4)) + (z * h3 - IZR 1 * bpow radix2 (-1)).

(** formal/ln/stage_h_q.g. *)
Theorem stage_h_q z : IZR 1 * bpow radix2 (-62) <= Rabs z <= IZR 1 * bpow radix2 (-9) ->
  (IZR (-577) * bpow radix2 (-61) <= (h_q z - z * z * h_Pz z) / (z * z) <= IZR 577 * bpow radix2 (-61)) /\
  (IZR (-513) * bpow radix2 (-10) <= h_Pz z <= IZR (-511) * bpow radix2 (-10)).
Proof.
  intros Hz. unfold h_q, h_p, h_Pz, h3, h4, h5, h6.
  split; [gbound_l (ln_stage_h_q.l1 z) | gbound_r (ln_stage_h_q.l1 z)].
Qed.

(** formal/ln/stage_h_lr.g. *)
Theorem stage_h_lr L z : IZR (-519) * bpow radix2 (-62) <= L <= IZR 519 * bpow radix2 (-62) -> IZR (-1) * bpow radix2 (-9) <= z <= IZR 1 * bpow radix2 (-9) ->
  (IZR (-1) * bpow radix2 (-104) <= rn (rn L * rn (1 - z)) - L * (1 - z) <= IZR 1 * bpow radix2 (-104)) /\
  (IZR (-263) * bpow radix2 (-61) <= rn (rn L * rn (1 - z)) <= IZR 263 * bpow radix2 (-61)).
Proof.
  intros HL Hz.
  split; [gbound_l (ln_stage_h_lr.l1 L z) | gbound_r (ln_stage_h_lr.l1 L z)].
Qed.

(** formal/ln/stage_h_gz.g. *)
Theorem stage_h_gz t4 t3 L z d3 Pz : IZR (-577) * bpow radix2 (-61) <= t4 <= IZR 577 * bpow radix2 (-61) -> IZR (-37) * bpow radix2 (-56) <= t3 <= IZR 37 * bpow radix2 (-56) ->
  IZR (-519) * bpow radix2 (-62) <= L <= IZR 519 * bpow radix2 (-62) -> IZR (-1) * bpow radix2 (-9) <= z <= IZR 1 * bpow radix2 (-9) -> IZR (-1) * bpow radix2 (-53) <= d3 <= IZR 1 * bpow radix2 (-53) -> IZR (-513) * bpow radix2 (-10) <= Pz <= IZR (-511) * bpow radix2 (-10) ->
  IZR (-543) * bpow radix2 (-59) <= - t4 + t3 + L / (1 + z) - d3 * (Pz + t4) <= IZR 543 * bpow radix2 (-59).
Proof. intros. gbound (ln_stage_h_gz.l1 t4 t3 L z d3 Pz). Qed.

(** formal/ln/stage_h_gs.g. *)
Theorem stage_h_gs tau kap eta d0 d1 d2 d3 : IZR (-183) * bpow radix2 (-94) <= tau <= IZR 183 * bpow radix2 (-94) -> IZR (-183) * bpow radix2 (-41) <= kap <= IZR 183 * bpow radix2 (-41) ->
  IZR (-1) * bpow radix2 (-53) <= eta <= IZR 1 * bpow radix2 (-53) -> IZR (-1) * bpow radix2 (-53) <= d0 <= IZR 1 * bpow radix2 (-53) -> IZR (-1) * bpow radix2 (-53) <= d1 <= IZR 1 * bpow radix2 (-53) -> IZR (-1) * bpow radix2 (-53) <= d2 <= IZR 1 * bpow radix2 (-53) ->
  IZR (-1) * bpow radix2 (-53) <= d3 <= IZR 1 * bpow radix2 (-53) ->
  IZR (-925) * bpow radix2 (-94) <= tau - d0 * kap / (1 + d0) - d1 * kap - d2 * (eta + kap * (1 + d1)) - d3 * (1 + d2) * (eta + kap * (1 + d1)) <= IZR 925 * bpow radix2 (-94).
Proof. intros. gbound (ln_stage_h_gs.l1 tau kap eta d0 d1 d2 d3). Qed.

(** formal/ln/stage_h_ga.g. *)
Theorem stage_h_ga t5 t6 lrt d1 d2 d3 : IZR (-1) * bpow radix2 (-104) <= t5 <= IZR 1 * bpow radix2 (-104) -> IZR (-267) * bpow radix2 (-114) <= t6 <= IZR 267 * bpow radix2 (-114) ->
  IZR (-263) * bpow radix2 (-61) <= lrt <= IZR 263 * bpow radix2 (-61) -> IZR (-1) * bpow radix2 (-53) <= d1 <= IZR 1 * bpow radix2 (-53) -> IZR (-1) * bpow radix2 (-53) <= d2 <= IZR 1 * bpow radix2 (-53) -> IZR (-1) * bpow radix2 (-53) <= d3 <= IZR 1 * bpow radix2 (-53) ->
  IZR (-263) * bpow radix2 (-111) <= - t5 + t6 - d1 * lrt - d2 * lrt * (1 + d1) - d3 * (1 + d2) * lrt * (1 + d1) <= IZR 263 * bpow radix2 (-111).
Proof. intros. gbound (ln_stage_h_ga.l1 t5 t6 lrt d1 d2 d3). Qed.

(** * Stage B *)

Definition b3 : R := IZR 6004799503160661 * bpow radix2 (-54).
Definition b4 : R := IZR (-1) * bpow radix2 (-2).
Definition b5 : R := IZR 3602879702233179 * bpow radix2 (-54).
Definition b6 : R := IZR (-1501199875835923) * bpow radix2 (-53).
Definition b7 : R := IZR 1286711445149333 * bpow radix2 (-53).
Definition b8 : R := IZR (-9007114324328199) * bpow radix2 (-56).

(** [W(v)] by Horner's scheme, rounded as the code rounds it, and exactly. *)
Definition b_w (v : R) : R :=
  let w4 := rn (rn (v * b8) + b7) in
  let w3 := rn (rn (v * w4) + b6) in
  let w2 := rn (rn (v * w3) + b5) in
  let w1 := rn (rn (v * w2) + b4) in
  rn (rn (v * w1) + b3).
Definition b_W (v : R) : R := v * (v * (v * (v * (v * b8 + b7) + b6) + b5) + b4) + b3.

(** formal/ln/stage_b_small_tail.g: [tail = RN(RN(x RN(x^2)) W)]. *)
Theorem stage_b_small_tail x : IZR 1 * bpow radix2 (-54) <= Rabs x <= IZR 1 * bpow radix2 (-9) ->
  (IZR (-655) * bpow radix2 (-62) <= (rn (rn (x * rn (x * x)) * b_w x) - x * x * x * b_W x) / (x * x * x) <= IZR 655 * bpow radix2 (-62)) /\
  (IZR 681 * bpow radix2 (-11) <= b_W x <= IZR 171 * bpow radix2 (-9)).
Proof.
  intros Hx. unfold b_w, b_W, b3, b4, b5, b6, b7, b8.
  split; [gbound_l (ln_stage_b_small_tail.l1 x) | gbound_r (ln_stage_b_small_tail.l1 x)].
Qed.

(** formal/ln/stage_b_small.g. *)
Theorem stage_b_small al be W pi eta m d1 d2 : IZR (-691) * bpow radix2 (-65) <= al <= IZR 691 * bpow radix2 (-65) -> IZR (-655) * bpow radix2 (-62) <= be <= IZR 655 * bpow radix2 (-62) ->
  IZR 681 * bpow radix2 (-11) <= W <= IZR 171 * bpow radix2 (-9) -> IZR (-259) * bpow radix2 (-61) <= pi <= IZR 259 * bpow radix2 (-61) -> IZR (-519) * bpow radix2 (-62) <= eta <= IZR 519 * bpow radix2 (-62) -> IZR (-1) * bpow radix2 (-9) <= m <= IZR 1 * bpow radix2 (-9) ->
  IZR (-1) * bpow radix2 (-53) <= d1 <= IZR 1 * bpow radix2 (-53) -> IZR (-1) * bpow radix2 (-53) <= d2 <= IZR 1 * bpow radix2 (-53) ->
  (IZR (-137) * bpow radix2 (-59) <= al - be - d1 * (W + be) - d2 * (1 + d1) * (W + be) <= IZR 137 * bpow radix2 (-59)) /\
  (IZR (-263) * bpow radix2 (-114) <= m * (d1 + d2 * (1 + d1)) * pi / 2 - d2 * eta <= IZR 263 * bpow radix2 (-114)).
Proof.
  intros.
  split; [gbound_l (ln_stage_b_small.l1 al be W pi eta m d1 d2) | gbound_r (ln_stage_b_small.l1 al be W pi eta m d1 d2)].
Qed.

(** [lo] of stage B's table branch, rounded as the code rounds it. *)
Definition b_lo (e1 e2 ln0 L z : R) : R :=
  let p := rn (z * z) in
  let pl := z * z - p in
  let zp := rn (z * p) in
  let tail := rn (zp * b_w z) in
  let r1 := rn (tail - pl / 2) in
  let lrt := rn (rn L * rn (rn (rn (1 - z) + p) - zp)) in
  let r2 := rn (ln0 + lrt) in
  let r3 := rn (r2 + r1) in
  let r4 := rn (e1 + e2) in
  rn (r4 + r3).
Definition b_ideal (e1 e2 ln0 L z : R) : R :=
  e1 + e2 + ln0 + L * (1 - z + z * z - z * z * z) - (z * z - rn (z * z)) / 2 + z * z * z * b_W z.

(** formal/ln/stage_b_lo.g. *)
Theorem stage_b_lo e1 e2 ln0 L z : IZR (-1) * bpow radix2 (-9) <= z <= IZR 1 * bpow radix2 (-9) -> IZR (-519) * bpow radix2 (-62) <= L <= IZR 519 * bpow radix2 (-62) ->
  IZR (-1) * bpow radix2 (-44) <= e1 <= IZR 1 * bpow radix2 (-44) -> IZR (-1) * bpow radix2 (-44) <= e2 <= IZR 1 * bpow radix2 (-44) -> IZR (-1) * bpow radix2 (-34) <= ln0 <= IZR 1 * bpow radix2 (-34) ->
  Gappa_definitions.FIX e1 (-1074) -> Gappa_definitions.FIX e2 (-1074) -> Gappa_definitions.FIX ln0 (-1074) ->
  (IZR (-415) * bpow radix2 (-88) <= b_lo e1 e2 ln0 L z - b_ideal e1 e2 ln0 L z <= IZR 415 * bpow radix2 (-88)) /\
  (IZR (-1) * bpow radix2 (-28) <= b_lo e1 e2 ln0 L z <= IZR 1 * bpow radix2 (-28)).
Proof.
  intros. unfold b_lo, b_ideal, b_w, b_W, b3, b4, b5, b6, b7, b8.
  split; [gbound_l (ln_stage_b_lo.l1 e1 e2 ln0 L z) | gbound_r (ln_stage_b_lo.l1 e1 e2 ln0 L z)].
Qed.

(** formal/ln/stage_b_total.g. *)
Theorem stage_b_total t1 ap lt g : IZR (-533) * bpow radix2 (-95) <= t1 <= IZR 533 * bpow radix2 (-95) -> IZR (-349) * bpow radix2 (-91) <= ap <= IZR 349 * bpow radix2 (-91) ->
  IZR (-263) * bpow radix2 (-97) <= lt <= IZR 263 * bpow radix2 (-97) -> IZR (-415) * bpow radix2 (-88) <= g <= IZR 415 * bpow radix2 (-88) ->
  IZR (-117) * bpow radix2 (-86) <= t1 + ap + lt - g <= IZR 117 * bpow radix2 (-86).
Proof. intros. gbound (ln_stage_b_total.l1 t1 ap lt g). Qed.

(** The mathematical function atan2 uses: the angle of the point [(x, y)], in [(-pi, pi]],
    and its reduction to the magnitude [angle_real] of two positive reals and a sign. *)
From Coq Require Import Reals Lra Psatz.
Open Scope R_scope.

Definition atan2R (y x : R) : R :=
  if Rlt_dec 0 x then atan (y / x)
  else if Rlt_dec x 0 then (if Rle_dec 0 y then atan (y / x) + PI else atan (y / x) - PI)
  else if Rlt_dec 0 y then PI / 2 else if Rlt_dec y 0 then - (PI / 2) else 0.

(** The magnitude, for [a, b > 0], with the quadrant of [x] given by [neg]. *)
Definition angle_real (a b : R) (neg : bool) : R :=
  if Rle_dec a b then (if neg then PI - atan (a / b) else atan (a / b))
  else (if neg then PI / 2 + atan (b / a) else PI / 2 - atan (b / a)).

Lemma atan_ratio_inv a b : 0 < a -> 0 < b -> atan (a / b) = PI / 2 - atan (b / a).
Proof.
  intros Ha Hb.
  assert (E : a / b = / (b / a)) by (field; lra).
  rewrite E. apply atan_inv. apply Rdiv_lt_0_compat; lra.
Qed.

Lemma atan2R_q1 a b : 0 < a -> 0 < b -> atan2R a b = angle_real a b false.
Proof.
  intros Ha Hb. unfold atan2R, angle_real.
  destruct (Rlt_dec 0 b) as [_ | N]; [ | lra].
  destruct (Rle_dec a b) as [L | G]; [reflexivity | ].
  exact (atan_ratio_inv a b Ha Hb).
Qed.

Lemma atan2R_q2 a b : 0 < a -> 0 < b -> atan2R a (- b) = angle_real a b true.
Proof.
  intros Ha Hb. unfold atan2R, angle_real.
  destruct (Rlt_dec 0 (- b)) as [N | _]; [lra | ].
  destruct (Rlt_dec (- b) 0) as [_ | N]; [ | lra].
  destruct (Rle_dec 0 a) as [_ | N]; [ | lra].
  assert (E : a / - b = - (a / b)) by (field; lra). rewrite E, atan_opp.
  destruct (Rle_dec a b) as [L | G]; [lra | ].
  rewrite (atan_ratio_inv a b Ha Hb). lra.
Qed.

Lemma atan2R_q3 a b : 0 < a -> 0 < b -> atan2R (- a) b = - angle_real a b false.
Proof.
  intros Ha Hb. unfold atan2R, angle_real.
  destruct (Rlt_dec 0 b) as [_ | N]; [ | lra].
  assert (E : - a / b = - (a / b)) by (field; lra). rewrite E, atan_opp.
  destruct (Rle_dec a b) as [L | G]; [reflexivity | ].
  rewrite (atan_ratio_inv a b Ha Hb). lra.
Qed.

Lemma atan2R_q4 a b : 0 < a -> 0 < b -> atan2R (- a) (- b) = - angle_real a b true.
Proof.
  intros Ha Hb. unfold atan2R, angle_real.
  destruct (Rlt_dec 0 (- b)) as [N | _]; [lra | ].
  destruct (Rlt_dec (- b) 0) as [_ | N]; [ | lra].
  destruct (Rle_dec 0 (- a)) as [N | _]; [lra | ].
  assert (E : - a / - b = a / b) by (field; lra). rewrite E.
  destruct (Rle_dec a b) as [L | G]; [lra | ].
  rewrite (atan_ratio_inv a b Ha Hb). lra.
Qed.

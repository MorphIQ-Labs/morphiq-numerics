(** The computed exponent argument of one quadrature node.

    For [S = sin theta] and [C = cos theta] of the node angle the Rust
    computes [((sh * xy) - hs) / (ch * ch)] with [sh], [ch] the rounded sine
    and cosine, [xy = x*y] and [hs = (x*x + y*y)/2], every operation rounded
    to binary64. This file bounds its distance from [-Q(S)],
    [Q(S) = (r/2 - p S)/(1 - S^2)], [r = x^2 + y^2], [p = x y], by a multiple
    of [Q(S)] (the relative error of the exponent, cancellation in
    [1 - kappa S] included), plus [z] for a subnormal final quotient. The
    inputs are zero or at least [2^-400] in magnitude, so no operation but the
    last underflows (a nonzero [x] below that is outside this statement). *)
From Coq Require Import Reals Lra Psatz.
Require Import BvnRound.
Open Scope R_scope.

Definition Qf (r p S : R) : R := (r / 2 - p * S) / (1 - S * S).

Definition hsf (x y : R) : R := rndF (rndF (rndF (x * x) + rndF (y * y)) / 2).

Definition argf (x y sh ch : R) : R :=
  rndF (rndF (rndF (sh * rndF (x * y)) - hsf x y) / rndF (ch * ch)).

Definition dom (x : R) : Prop := x = 0 \/ bpow radix2 (-400) <= Rabs x.

Lemma sq_ok x : dom x -> x * x = 0 \/ bpow radix2 (-1022) <= Rabs (x * x).
Proof.
  intros [H | H].
  - left. subst. ring.
  - right. rewrite Rabs_mult.
    assert (Hp : bpow radix2 (-800) = bpow radix2 (-400) * bpow radix2 (-400)).
    { rewrite <- bpow_plus. reflexivity. }
    assert (0 < bpow radix2 (-400)) by apply bpow_gt_0.
    assert (bpow radix2 (-1022) <= bpow radix2 (-800)) by (apply bpow_le; lia).
    nra.
Qed.

Lemma M_ok x y : dom x -> dom y ->
  x * x + y * y = 0 \/ bpow radix2 (-800) <= x * x + y * y.
Proof.
  intros Hx Hy.
  assert (H800 : bpow radix2 (-800) = bpow radix2 (-400) * bpow radix2 (-400)).
  { rewrite <- bpow_plus. reflexivity. }
  pose proof (bpow_gt_0 radix2 (-400)) as Hp.
  destruct Hx as [Hx0 | Hxn].
  - destruct Hy as [Hy0 | Hyn].
    + left. subst. ring.
    + right. rewrite Hx0. rewrite H800.
      pose proof (Rabs_pos y). pose proof (Rabs_sq y). nra.
  - right. rewrite H800. pose proof (Rabs_sq x). pose proof (Rabs_sq y). nra.
Qed.

(** [hs] is within [(2u + u^2)] of [(x^2 + y^2)/2], relative. *)
Lemma hs_err x y : dom x -> dom y ->
  Rabs (hsf x y - (x * x + y * y) / 2) <= (x * x + y * y) / 2 * (2 * u + u * u).
Proof.
  intros Hx Hy. pose proof u_pos as Hu. pose proof u_val as Huv.
  destruct (M_ok x y Hx Hy) as [M0 | M1].
  - assert (x = 0) by nra. assert (y = 0) by nra. subst x y. unfold hsf.
    replace (0 * 0) with 0 by ring.
    rewrite round_0 by auto with typeclass_instances.
    replace (0 + 0) with 0 by ring. rewrite round_0 by auto with typeclass_instances.
    replace (0 / 2) with 0 by ring. rewrite round_0 by auto with typeclass_instances.
    replace (0 - (0 * 0 + 0 * 0) / 2) with 0 by ring. rewrite Rabs_R0. right. ring.
  - unfold hsf.
    destruct (rnd_delta (x * x) (sq_ok x Hx)) as [a1 [Ha1 E1]].
    destruct (rnd_delta (y * y) (sq_ok y Hy)) as [a2 [Ha2 E2]].
    rewrite E1, E2.
    set (M := x * x + y * y) in *.
    set (w := x * x * (1 + a1) + y * y * (1 + a2)).
    assert (Hx2 : 0 <= x * x) by apply Rle_0_sqr.
    assert (Hy2 : 0 <= y * y) by apply Rle_0_sqr.
    apply Rabs_le in Ha1. apply Rabs_le in Ha2.
    assert (Hwl : (1 - u) * M <= w) by (unfold w, M; nra).
    assert (Hwu : w <= (1 + u) * M) by (unfold w, M; nra).
    assert (H800 : bpow radix2 (-1022) <= bpow radix2 (-800)) by (apply bpow_le; lia).
    assert (Hw : bpow radix2 (-1022) <= Rabs w).
    { rewrite Rabs_pos_eq by nra. nra. }
    destruct (rnd_delta w (or_intror Hw)) as [a3 [Ha3 E3]].
    rewrite E3. apply Rabs_le in Ha3.
    assert (Hw3 : bpow radix2 (-1021) <= Rabs (w * (1 + a3))).
    { assert (bpow radix2 (-1021) = 2 * bpow radix2 (-1022)).
      { replace (-1021)%Z with (-1022 + 1)%Z by reflexivity. rewrite bpow_plus.
        change (bpow radix2 1) with 2%R. ring. }
      assert (bpow radix2 (-800) = bpow radix2 (-1022) * bpow radix2 222).
      { rewrite <- bpow_plus. reflexivity. }
      assert (bpow radix2 222 >= 4).
      { replace 4 with (bpow radix2 2) by reflexivity. apply Rle_ge, bpow_le. lia. }
      pose proof (bpow_gt_0 radix2 (-1022)).
      rewrite Rabs_pos_eq by nra. nra. }
    assert (Hf : fmtF (rndF w)) by apply fmtF_rnd.
    rewrite E3 in Hf.
    rewrite (rnd_half (w * (1 + a3)) Hf Hw3).
    rewrite Rabs_le_between. split; unfold M in *; nra.
Qed.

(** The relative bound of the quotient, with [zt] bounding
    [|ch^2 - C^2| / C^2] and [Eh] the relative size of the numerator's error. *)
Definition ar0 (zt Eh sg : R) : R :=
  (zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)) / ((1 - zt) * (1 - u)).

Lemma arg_core r p S C sh ch hs n1 n2 dh sg hs_ hc_ zt Eh phi b3 b4 :
  0 <= r -> Rabs p <= r / 2 -> S * S + C * C = 1 -> 0 < C ->
  Rabs S <= sg -> sg < 1 -> Rabs sh <= 1 ->
  Rabs (sh - S) <= hs_ -> Rabs (ch - C) <= hc_ -> 0 <= hs_ -> 0 <= hc_ ->
  zt = hc_ * (2 + hc_) / (1 - sg * sg) -> zt <= / 2 ->
  Eh = hs_ + 2 * (2 * u + u * u) ->
  Rabs phi <= 2 * u + u * u -> Rabs (hs - r / 2) <= r / 2 * (2 * u + u * u) ->
  n1 = sh * p * (1 + phi) -> n2 = (n1 - hs) * (1 + b3) -> Rabs b3 <= u ->
  dh = ch * ch * (1 + b4) -> Rabs b4 <= u ->
  Rabs (n2 / dh + Qf r p S) <= ar0 zt Eh sg * Qf r p S.
Proof.
  intros Hr Hp HSC HC HS Hsg Hsh Hshe Hche Hhs Hhc Hzt Hzh HEh Hphi Hhsr Hn1 Hn2 Hb3 Hdh Hb4.
  pose proof u_pos as Hu. pose proof u_val as Huv.
  assert (Hu1 : u < / 2) by (rewrite Huv; lra).
  set (Nabs := r / 2 - p * S).
  set (C2 := 1 - S * S).
  assert (HC2 : C2 = C * C) by (unfold C2; lra).
  assert (HC2p : 0 < C2) by (rewrite HC2; nra).
  pose proof (Rabs_pos S) as HSa. 
  assert (HS2 : S * S <= sg * sg) by (pose proof (Rabs_sq S); nra).
  assert (Hsg0 : 0 <= sg) by lra.
  assert (HC2lb : 1 - sg * sg <= C2) by (unfold C2; lra).
  assert (H1s : 0 < 1 - sg) by lra.
  assert (H1ss : 0 < 1 - sg * sg) by nra.
  (* Nabs >= (r/2)(1 - sg) *)
  assert (HpS : Rabs (p * S) <= r / 2 * sg).
  { rewrite Rabs_mult. pose proof (Rabs_pos p). nra. }
  apply Rabs_le in HpS.
  assert (HNabs : r / 2 * (1 - sg) <= Nabs) by (unfold Nabs; nra).
  assert (Hr2 : r / 2 <= Nabs / (1 - sg)).
  { apply Rmult_le_reg_r with (1 - sg); [exact H1s |]. field_simp. nra. }
  assert (HNabs0 : 0 <= Nabs) by nra.
  (* E0 *)
  set (E0 := n1 - hs + Nabs).
  assert (HE0 : E0 = (sh - S) * p + sh * p * phi + (r / 2 - hs)).
  { unfold E0, Nabs. rewrite Hn1. ring. }
  assert (HE0b : Rabs E0 <= r / 2 * Eh).
  { rewrite HE0.
    set (t1 := (sh - S) * p). set (t2 := sh * p * phi). set (t3 := r / 2 - hs).
    assert (Ht1 : Rabs t1 <= r / 2 * hs_).
    { unfold t1. rewrite Rabs_mult. pose proof (Rabs_pos p). pose proof (Rabs_pos (sh - S)). nra. }
    assert (Ht2 : Rabs t2 <= r / 2 * (2 * u + u * u)).
    { unfold t2. rewrite !Rabs_mult. pose proof (Rabs_pos p). pose proof (Rabs_pos sh). pose proof (Rabs_pos phi).
      assert (Rabs sh * Rabs p <= r / 2) by nra.
      assert (0 <= 2 * u + u * u) by nra. nra. }
    assert (Ht3 : Rabs t3 <= r / 2 * (2 * u + u * u)).
    { unfold t3. rewrite Rabs_minus_sym. exact Hhsr. }
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
    rewrite HEh. nra. }
  (* the denominator *)
  assert (Hch2 : Rabs (ch * ch - C2) <= zt * C2).
  { rewrite HC2.
    assert (E : ch * ch - C * C = (ch - C) * (ch + C)) by ring. rewrite E.
    rewrite Rabs_mult.
    assert (Hs1 : Rabs (ch + C) <= 2 + hc_).
    { assert (ch + C = (ch - C) + 2 * C) by ring. rewrite H.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_mult.
      assert (Rabs 2 = 2) by (apply Rabs_pos_eq; lra). rewrite H0.
      assert (C <= 1) by nra. rewrite (Rabs_pos_eq C) by lra. nra. }
    assert (Hs2 : Rabs (ch - C) * Rabs (ch + C) <= hc_ * (2 + hc_)).
    { pose proof (Rabs_pos (ch - C)). pose proof (Rabs_pos (ch + C)). nra. }
    assert (Hz : hc_ * (2 + hc_) <= zt * (C * C)).
    { rewrite Hzt. assert (hc_ * (2 + hc_) / (1 - sg * sg) * (1 - sg * sg) = hc_ * (2 + hc_)) by (field; lra).
      pose proof (Rmult_le_compat_l (hc_ * (2 + hc_) / (1 - sg * sg)) (1 - sg * sg) (C * C)) as M.
      assert (0 <= hc_ * (2 + hc_) / (1 - sg * sg)) by (apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; lra]).
      rewrite <- HC2 in HC2lb |- *. nra. }
    nra. }
  assert (Hzt0 : 0 <= zt).
  { rewrite Hzt. apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
  assert (Hch2l : C2 * (1 - zt) <= ch * ch) by (apply Rabs_le in Hch2; nra).
  assert (Hdhl : C2 * (1 - zt) * (1 - u) <= dh).
  { rewrite Hdh. apply Rabs_le in Hb4. assert (0 <= ch * ch) by nra. nra. }
  assert (Hdhp : 0 < dh) by (assert (0 < C2 * (1 - zt) * (1 - u)) by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | lra]); lra).
  (* v + Nabs/C2 = [n2 C2 + Nabs dh] / (dh C2) *)
  set (T := n2 * C2 + Nabs * dh).
  assert (HT : T = Nabs * (ch * ch * (1 + b4) - C2 * (1 + b3)) + E0 * (1 + b3) * C2).
  { unfold T. rewrite Hn2, Hdh. unfold E0. ring. }
  assert (HTb : Rabs T <= Nabs * C2 * (zt * (1 + u) + 2 * u) + Rabs E0 * (1 + u) * C2).
  { rewrite HT.
    eapply Rle_trans; [apply Rabs_triang |].
    apply Rplus_le_compat.
    - rewrite Rabs_mult. rewrite (Rabs_pos_eq Nabs) by exact HNabs0.
      assert (Hd : Rabs (ch * ch * (1 + b4) - C2 * (1 + b3)) <= C2 * (zt * (1 + u) + 2 * u)).
      { assert (E : ch * ch * (1 + b4) - C2 * (1 + b3) = (ch * ch - C2) * (1 + b4) + C2 * (b4 - b3)) by ring.
        rewrite E. eapply Rle_trans; [apply Rabs_triang |].
        rewrite !Rabs_mult.
        assert (Rabs (1 + b4) <= 1 + u) by (apply Rabs_le in Hb4; apply Rabs_le; split; nra).
        assert (Rabs C2 = C2) by (apply Rabs_pos_eq; lra). rewrite H0.
        assert (Rabs (b4 - b3) <= 2 * u) by (apply Rabs_le in Hb4; apply Rabs_le in Hb3; apply Rabs_le; split; nra).
        pose proof (Rabs_pos (ch * ch - C2)). pose proof (Rabs_pos (1 + b4)). pose proof (Rabs_pos (b4 - b3)).
        nra. }
      nra.
    - rewrite !Rabs_mult.
      assert (Rabs (1 + b3) <= 1 + u) by (apply Rabs_le in Hb3; apply Rabs_le; split; nra).
      assert (Rabs C2 = C2) by (apply Rabs_pos_eq; lra). rewrite H0.
      pose proof (Rabs_pos E0). pose proof (Rabs_pos (1 + b3)). nra. }
  assert (Hv : n2 / dh + Nabs / C2 = T / (dh * C2)).
  { unfold T. field. split; lra. }
  unfold Qf. fold Nabs. fold C2.
  rewrite Hv. rewrite Rabs_div by (apply Rgt_not_eq; nra).
  rewrite (Rabs_pos_eq (dh * C2)) by nra.
  apply Rmult_le_reg_r with (dh * C2); [nra |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; nra). rewrite Rmult_1_r.
  unfold ar0.
  assert (Hden : 0 < (1 - zt) * (1 - u)) by (apply Rmult_lt_0_compat; lra).
  assert (Hgoal : Rabs T <= (zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)) / ((1 - zt) * (1 - u)) * (Nabs / C2) * (dh * C2)).
  { assert (Hq : (zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)) / ((1 - zt) * (1 - u)) * ((1 - zt) * (1 - u)) = zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)) by (field; lra).
    set (Kq := (zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)) / ((1 - zt) * (1 - u))) in *.
    assert (HEh0 : 0 <= Eh) by (rewrite HEh; nra).
    assert (HE0c : Rabs E0 <= Nabs / (1 - sg) * Eh).
    { eapply Rle_trans; [exact HE0b |]. apply Rmult_le_compat_r; [exact HEh0 | exact Hr2]. }
    assert (HKq0 : 0 <= Kq).
    { unfold Kq. apply Rmult_le_pos.
      - apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat; nra | ].
        apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; lra].
      - apply Rlt_le, Rinv_0_lt_compat. exact Hden. }
    assert (Hbn : Rabs T <= Nabs * C2 * (zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg))).
    { eapply Rle_trans; [exact HTb |].
      assert (Hx1 : Rabs E0 * (1 + u) * C2 <= Nabs / (1 - sg) * Eh * (1 + u) * C2).
      { pose proof (Rabs_pos E0). apply Rmult_le_compat_r; [lra |].
        apply Rmult_le_compat_r; [lra | exact HE0c]. }
      assert (E : Nabs / (1 - sg) * Eh * (1 + u) * C2 = Nabs * C2 * ((1 + u) * Eh / (1 - sg))) by (field; lra).
      nra. }
    assert (HR : Kq * (Nabs / C2) * (dh * C2) = Kq * Nabs * dh) by (field; lra).
    rewrite HR.
    assert (Hk2 : Kq * ((1 - zt) * (1 - u)) = zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)) by exact Hq.
    assert (Hlow : Nabs * (C2 * ((1 - zt) * (1 - u))) <= Nabs * dh) by (apply Rmult_le_compat_l; [exact HNabs0 | nra]).
    assert (Hm : Kq * (Nabs * (C2 * ((1 - zt) * (1 - u)))) <= Kq * (Nabs * dh))
      by (apply Rmult_le_compat_l; [exact HKq0 | exact Hlow]).
    assert (E2 : Kq * (Nabs * (C2 * ((1 - zt) * (1 - u)))) = Nabs * C2 * (zt * (1 + u) + 2 * u + (1 + u) * Eh / (1 - sg)))
      by (rewrite <- Hk2; ring).
    nra. }
  exact Hgoal.
Qed.


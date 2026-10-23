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
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Flocq Require Import Core.
From Flocq Require Import Relative.
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
  - assert (x = 0) by nra. assert (y = 0) by nra. subst x y.
    assert (Hr0 : rndF 0 = 0) by (apply round_0; auto with typeclass_instances).
    unfold hsf. rewrite !Rmult_0_l, Hr0, Rplus_0_l, Hr0.
    unfold Rdiv. rewrite Rmult_0_l, Hr0.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. nra.
  - unfold hsf.
    destruct (rnd_delta (x * x) (sq_ok x Hx)) as [a1 [Ha1 E1]].
    destruct (rnd_delta (y * y) (sq_ok y Hy)) as [a2 [Ha2 E2]].
    rewrite E1, E2.
    set (M := x * x + y * y) in *.
    set (w := x * x * (1 + a1) + y * y * (1 + a2)).
    assert (Hx2 : 0 <= x * x) by apply Rle_0_sqr.
    assert (Hy2 : 0 <= y * y) by apply Rle_0_sqr.
    apply Rabs_le_inv in Ha1. apply Rabs_le_inv in Ha2.
    destruct Ha1 as [Ha1l Ha1u]. destruct Ha2 as [Ha2l Ha2u].
    assert (h1 : 0 <= x * x * (a1 + u)) by (apply Rmult_le_pos; lra).
    assert (h2 : 0 <= y * y * (a2 + u)) by (apply Rmult_le_pos; lra).
    assert (h3 : 0 <= x * x * (u - a1)) by (apply Rmult_le_pos; lra).
    assert (h4 : 0 <= y * y * (u - a2)) by (apply Rmult_le_pos; lra).
    assert (Hwl : (1 - u) * M <= w) by (unfold w, M; nra).
    assert (Hwu : w <= (1 + u) * M) by (unfold w, M; nra).
    assert (H800 : bpow radix2 (-1022) <= bpow radix2 (-800)) by (apply bpow_le; lia).
    assert (HuH : u < / 2) by (rewrite Huv; lra).
    assert (HM0 : 0 <= M) by (unfold M; nra).
    assert (HmM : / 2 * M <= (1 - u) * M).
    { assert (0 <= (/ 2 - u) * M) by (apply Rmult_le_pos; lra). nra. }
    assert (Hb2 : 4 * bpow radix2 (-1022) <= bpow radix2 (-800)).
    { replace 4 with (bpow radix2 2) by reflexivity. rewrite <- bpow_plus. apply bpow_le. lia. }
    pose proof (bpow_gt_0 radix2 (-1022)) as Hb0.
    assert (Hw : bpow radix2 (-1022) <= Rabs w).
    { rewrite Rabs_pos_eq by nra. nra. }
    destruct (rnd_delta w (or_intror Hw)) as [a3 [Ha3 E3]].
    rewrite E3. apply Rabs_le_inv in Ha3.
    assert (Hw3 : bpow radix2 (-1021) <= Rabs (w * (1 + a3))).
    { assert (bpow radix2 (-1021) = 2 * bpow radix2 (-1022)).
      { replace (-1021)%Z with (-1022 + 1)%Z by reflexivity. rewrite bpow_plus.
        change (bpow radix2 1) with 2%R. ring. }
      destruct Ha3 as [Ha3l Ha3u].
      assert (Hww : 0 <= w) by nra.
      assert (H1a : / 4 * w <= w * (1 + a3)) by nra.
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
  apply Rabs_le_inv in HpS.
  assert (HNabs : r / 2 * (1 - sg) <= Nabs) by (unfold Nabs; nra).
  assert (Hr2 : r / 2 <= Nabs / (1 - sg)).
  { assert (E : Nabs / (1 - sg) = r / 2 + (Nabs - r / 2 * (1 - sg)) / (1 - sg)) by (field; lra).
    rewrite E. assert (0 <= (Nabs - r / 2 * (1 - sg)) / (1 - sg)).
    { apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
    lra. }
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
    { assert (Ez : zt * (1 - sg * sg) = hc_ * (2 + hc_)) by (rewrite Hzt; field; lra).
      assert (Hzt0' : 0 <= zt).
      { rewrite Hzt. apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
      assert (zt * (1 - sg * sg) <= zt * C2) by (apply Rmult_le_compat_l; [exact Hzt0' | exact HC2lb]).
      rewrite HC2 in H. lra. }
    nra. }
  assert (Hzt0 : 0 <= zt).
  { rewrite Hzt. apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
  assert (Hch2l : C2 * (1 - zt) <= ch * ch) by (apply Rabs_le_inv in Hch2; nra).
  assert (Hdhl : C2 * (1 - zt) * (1 - u) <= dh).
  { rewrite Hdh. apply Rabs_le_inv in Hb4. assert (0 <= ch * ch) by nra. nra. }
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
        assert (Rabs (1 + b4) <= 1 + u) by (apply Rabs_le_inv in Hb4; apply Rabs_le; split; nra).
        assert (Rabs C2 = C2) by (apply Rabs_pos_eq; lra). rewrite H0.
        assert (Rabs (b4 - b3) <= 2 * u) by (apply Rabs_le_inv in Hb4; apply Rabs_le_inv in Hb3; apply Rabs_le; split; nra).
        pose proof (Rabs_pos (ch * ch - C2)). pose proof (Rabs_pos (1 + b4)). pose proof (Rabs_pos (b4 - b3)).
        nra. }
      nra.
    - rewrite !Rabs_mult.
      assert (Rabs (1 + b3) <= 1 + u) by (apply Rabs_le_inv in Hb3; apply Rabs_le; split; nra).
      assert (Rabs C2 = C2) by (apply Rabs_pos_eq; lra). rewrite H0.
      assert (Hq1 : Rabs E0 * Rabs (1 + b3) <= Rabs E0 * (1 + u))
        by (apply Rmult_le_compat_l; [apply Rabs_pos | exact H]).
      apply Rmult_le_compat_r; [lra | exact Hq1]. }
  assert (Hv : n2 / dh + Nabs / C2 = T / (dh * C2)).
  { unfold T. field. split; lra. }
  unfold Qf. fold Nabs. fold C2.
  rewrite Hv. rewrite Rabs_div_pos by nra.
  apply Rmult_le_reg_r with (dh * C2); [nra |].
  unfold Rdiv at 1. rewrite Rmult_assoc, Rinv_l by (apply Rgt_not_eq; nra). rewrite Rmult_1_r.
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


Lemma prod_ok x y : dom x -> dom y -> x * y = 0 \/ bpow radix2 (-800) <= Rabs (x * y).
Proof.
  intros Hx Hy.
  assert (H800 : bpow radix2 (-800) = bpow radix2 (-400) * bpow radix2 (-400)).
  { rewrite <- bpow_plus. reflexivity. }
  pose proof (bpow_gt_0 radix2 (-400)) as Hp.
  destruct Hx as [Hx0 | Hxn]; [left; subst; ring |].
  destruct Hy as [Hy0 | Hyn]; [left; subst; ring |].
  right. rewrite Rabs_mult, H800.
  pose proof (Rabs_pos x). pose proof (Rabs_pos y). nra.
Qed.

Lemma arg_err x y sh S C ch sg hs_ hc_ zt Eh :
  dom x -> dom y -> bpow radix2 (-100) <= Rabs sh -> Rabs sh <= 1 ->
  S * S + C * C = 1 -> 0 < C -> Rabs S <= sg -> sg < 1 ->
  Rabs (sh - S) <= hs_ -> Rabs (ch - C) <= hc_ -> 0 <= hs_ -> 0 <= hc_ ->
  bpow radix2 (-100) <= ch ->
  zt = hc_ * (2 + hc_) / (1 - sg * sg) -> zt <= / 2 ->
  Eh = hs_ + 2 * (2 * u + u * u) ->
  Rabs (argf x y sh ch + Qf (x * x + y * y) (x * y) S)
    <= (ar0 zt Eh sg * (1 + u) + u) * Qf (x * x + y * y) (x * y) S + z.
Proof.
  intros Hx Hy Hsh1 Hsh2 HSC HC HS Hsg Hshe Hche Hhs Hhc Hch Hzt Hzh HEh.
  pose proof u_pos as Hu. pose proof u_val as Huv.
  set (r := x * x + y * y). set (p := x * y).
  assert (Hr : 0 <= r) by (unfold r; nra).
  assert (Hp : Rabs p <= r / 2).
  { unfold p, r. pose proof (Rle_0_sqr (x - y)) as h1. pose proof (Rle_0_sqr (x + y)) as h2.
    unfold Rsqr in h1, h2. apply Rabs_le. split; nra. }
  (* p-hat *)
  assert (Hp1022 : p = 0 \/ bpow radix2 (-1022) <= Rabs p).
  { destruct (prod_ok x y Hx Hy) as [H | H]; [left; exact H | right].
    eapply Rle_trans; [| exact H]. apply bpow_le. lia. }
  destruct (rnd_delta p Hp1022) as [b1 [Hb1 E1]].
  (* n1 *)
  assert (Hn1ok : sh * rndF p = 0 \/ bpow radix2 (-1022) <= Rabs (sh * rndF p)).
  { rewrite E1.
    destruct (prod_ok x y Hx Hy) as [H0 | H1].
    - left. fold p in H0. rewrite H0. ring.
    - right. fold p in H1. rewrite Rabs_mult, Rabs_mult.
      assert (Hb : Rabs (1 + b1) >= 1 / 2) by (apply Rabs_le_inv in Hb1; rewrite Rabs_pos_eq by nra; nra).
      assert (Hpp : bpow radix2 (-800) <= Rabs p) by exact H1.
      assert (Hq : bpow radix2 (-1022) <= bpow radix2 (-100) * (bpow radix2 (-800) * (1 / 2))).
      { assert (E1' : bpow radix2 (-100) * bpow radix2 (-800) = bpow radix2 (-900)) by (rewrite <- bpow_plus; reflexivity).
        assert (E2' : bpow radix2 (-900) = 2 * bpow radix2 (-901)).
        { replace (-900)%Z with (-901 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2%R. ring. }
        assert (bpow radix2 (-1022) <= bpow radix2 (-901)) by (apply bpow_le; lia).
        nra. }
      pose proof (bpow_gt_0 radix2 (-100)). pose proof (bpow_gt_0 radix2 (-800)).
      pose proof (Rabs_pos sh). pose proof (Rabs_pos p).
      assert (Hbd : bpow radix2 (-100) * (bpow radix2 (-800) * (1 / 2)) <= Rabs sh * (Rabs p * Rabs (1 + b1))).
      { apply Rmult_le_compat; [lra | nra | exact Hsh1 | ].
        apply Rmult_le_compat; [lra | lra | lra | lra]. }
      lra. }
  destruct (rnd_delta (sh * rndF p) Hn1ok) as [b2 [Hb2 E2]].
  set (n1 := rndF (sh * rndF p)).
  assert (Hn1 : n1 = sh * p * (1 + ((1 + b1) * (1 + b2) - 1))).
  { unfold n1. rewrite E2, E1. ring. }
  assert (Hphi : Rabs ((1 + b1) * (1 + b2) - 1) <= 2 * u + u * u).
  { apply Rabs_le_inv in Hb1. apply Rabs_le_inv in Hb2. apply Rabs_le. split; nra. }
  (* n2 *)
  assert (Fn1 : fmtF n1) by apply fmtF_rnd.
  assert (Fhs : fmtF (hsf x y)) by apply fmtF_rnd.
  destruct (rnd_sub_delta n1 (hsf x y) Fn1 Fhs) as [b3 [Hb3 E3]].
  set (n2 := rndF (n1 - hsf x y)).
  (* denominator *)
  assert (Hdok : bpow radix2 (-1022) <= Rabs (ch * ch)).
  { rewrite Rabs_pos_eq by nra.
    assert (E : bpow radix2 (-1022) = bpow radix2 (-100) * bpow radix2 (-100) * bpow radix2 (-822)).
    { rewrite <- !bpow_plus. reflexivity. }
    pose proof (bpow_gt_0 radix2 (-822)). pose proof (bpow_gt_0 radix2 (-100)).
    assert (bpow radix2 (-822) <= 1) by (replace 1 with (bpow radix2 0) by reflexivity; apply bpow_le; lia).
    assert (bpow radix2 (-100) * bpow radix2 (-100) <= ch * ch) by nra. nra. }
  destruct (rnd_delta (ch * ch) (or_intror Hdok)) as [b4 [Hb4 E4]].
  set (dh := rndF (ch * ch)).
  assert (Hdh : dh = ch * ch * (1 + b4)) by (unfold dh; rewrite E4; ring).
  assert (Hn2 : n2 = (n1 - hsf x y) * (1 + b3)) by (unfold n2; rewrite E3; ring).
  pose proof (arg_core r p S C sh ch (hsf x y) n1 n2 dh sg hs_ hc_ zt Eh ((1 + b1) * (1 + b2) - 1) b3 b4
    Hr Hp HSC HC HS Hsg ltac:(lra) Hshe Hche Hhs Hhc Hzt Hzh HEh Hphi (hs_err x y Hx Hy) Hn1 Hn2 Hb3 Hdh Hb4) as Hcore.
  (* the last rounding *)
  unfold argf. fold n1. fold n2. fold dh.
  pose proof (rnd_rel_z (n2 / dh)) as Hz.
  set (v := n2 / dh) in *.
  set (Q := Qf r p S) in *.
  set (ar := ar0 zt Eh sg) in *.
  assert (HQ0 : 0 <= Q).
  { unfold Q, Qf. apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat; nra].
    assert (Hpa : Rabs (p * S) <= r / 2 * sg).
    { rewrite Rabs_mult. pose proof (Rabs_pos p). pose proof (Rabs_pos S). nra. }
    apply Rabs_le_inv in Hpa. assert (0 <= sg) by (pose proof (Rabs_pos S); lra). nra. }
  assert (Hvq : Rabs v <= Q + ar * Q).
  { assert (Hs : Rabs v <= Rabs (v + Q) + Rabs Q).
    { assert (E0 : v = (v + Q) + - Q) by ring.
      rewrite E0 at 1. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    rewrite (Rabs_pos_eq Q HQ0) in Hs. lra. }
  change (Rabs (rndF v + Q) <= (ar * (1 + u) + u) * Q + z).
  assert (E : rndF v + Q = (rndF v - v) + (v + Q)) by ring.
  rewrite E. eapply Rle_trans; [apply Rabs_triang |].
  assert (Hu0 : 0 <= u * Rabs v) by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
  assert (Hu1 : u * Rabs v <= u * (Q + ar * Q)) by (apply Rmult_le_compat_l; lra).
  nra.
Qed.

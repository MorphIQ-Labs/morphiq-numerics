(** The accurate path's Newton step, in real arithmetic: from a start within
    [2^-62] of the root, the step's value is within [2^-124] of it, whatever the
    roundings do within their contracts. Direct branch: [y1 = r + (x - sin r)/cos r]
    with [sin] and [cos] computed within [1e-58] relatively and the reciprocal
    within [1e-58]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Open Scope R_scope.

Definition tiny : R := / 10000000000000000000000000000000000000000000000000000000000.
Definition eta62 : R := / 4611686018427387904 * 1.0001.

Lemma newton_direct_real Y r d x sn cs ri res prod y1 sin_r cos_r sigma gamma e d3 g2 g3 rr :
  Y = r + d -> Y <= 0.7854 -> / 67108864 <= Y ->
  Rabs d <= eta62 * Y ->
  0.7071 <= cos_r -> cos_r <= 1 -> 0 <= sin_r -> sin_r <= 0.70711 ->
  x = sin_r + cos_r * d - rr * (d * d) -> - / 1152921504606846976 <= rr <= 0.5000001 ->
  sn = sin_r * (1 + sigma) -> Rabs sigma <= tiny ->
  cs = cos_r * (1 + gamma) -> Rabs gamma <= tiny ->
  cs * ri = 1 + e -> Rabs e <= tiny ->
  res = (x - sn) + g2 -> Rabs g2 <= tiny ->
  prod = res * ri * (1 + d3) -> Rabs d3 <= tiny ->
  y1 = r + prod + g3 -> Rabs g3 <= tiny * Y ->
  Rabs (y1 - Y) <= / 21267647932558653966460912964485513216 * Y.
Proof.
  intros HY HY1 HY0 Hd Hc1 Hc2 Hs1 Hs2 Hx Hrr Hsn Hsig Hcs Hgam Hcr He Hres Hg2 Hprod Hd3 Hy1 Hg3.
  assert (Ht : 0 < tiny <= / 1000000) by (unfold tiny; split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]).
  pose proof Hsig as Hsig0. pose proof Hgam as Hgam0. pose proof He as He0. pose proof Hd3 as Hd30.
  apply Rabs_le_inv in Hsig0. apply Rabs_le_inv in Hgam0. apply Rabs_le_inv in He0. apply Rabs_le_inv in Hd30.
  (* res = cos_r * d - rr d^2 - sin_r sigma + g2 *)
  assert (Hres' : res = cos_r * d - rr * (d * d) - sin_r * sigma + g2).
  { rewrite Hres, Hx, Hsn. ring. }
  (* cos_r ri (1 + gamma) = 1 + e *)
  assert (Hcri : cos_r * ri * (1 + gamma) = 1 + e) by (rewrite <- Hcr, Hcs; ring).
  set (Bq := (- (rr * (d * d)) - sin_r * sigma + g2)).
  assert (Hcp : cos_r <> 0) by lra.
  assert (Hri : ri * (1 + gamma) = (1 + e) / cos_r) by (rewrite <- Hcri; field; exact Hcp).
  assert (Hprod' : prod * (1 + gamma) = (1 + d3) * (1 + e) * (d + Bq / cos_r)).
  { rewrite Hprod, Hres'.
    replace ((cos_r * d - rr * (d * d) - sin_r * sigma + g2) * ri * (1 + d3) * (1 + gamma))
      with ((1 + d3) * ((cos_r * d) * (ri * (1 + gamma)) + Bq * (ri * (1 + gamma)))) by (unfold Bq; ring).
    rewrite Hri. unfold Bq. field. exact Hcp. }
  set (K := (1 + d3) * (1 + e)).
  set (Z := prod - d).
  assert (S1 : Z * ((1 + gamma) * cos_r) = d * (K - 1 - gamma) * cos_r + K * Bq).
  { unfold Z. assert (E : prod * (1 + gamma) * cos_r = K * (d * cos_r + Bq)).
    { rewrite Hprod'. unfold K. field. exact Hcp. }
    nra. }
  assert (S2 : Rabs (K - 1 - gamma) <= 3.01 * tiny).
  { unfold K. replace ((1 + d3) * (1 + e) - 1 - gamma) with (d3 + e + d3 * e - gamma) by ring.
    assert (Rabs (d3 * e) <= tiny * tiny) by (rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hd3 | exact He]).
    apply Rabs_le_inv in H. apply Rabs_le. destruct Ht as [Ht0 Ht1]. nra. }
  assert (S3 : Rabs K <= 1.0001).
  { unfold K. apply Rabs_le. destruct Ht as [Ht0 Ht1]. nra. }
  assert (Hd2 : d * d <= eta62 * eta62 * (Y * Y)).
  { apply Rabs_le_inv in Hd. assert (0 <= eta62) by (unfold eta62; lra). nra. }
  assert (S4 : Rabs Bq <= 0.5000001 * (eta62 * eta62 * (Y * Y)) + 2 * tiny).
  { unfold Bq. 
    assert (Rabs (rr * (d * d)) <= 0.5000001 * (eta62 * eta62 * (Y * Y))).
    { rewrite Rabs_mult. rewrite (Rabs_pos_eq (d * d)) by nra.
      assert (Rabs rr <= 0.5000001) by (apply Rabs_le; split; [ | lra]; lra).
      pose proof (Rabs_pos rr). nra. }
    assert (Rabs (sin_r * sigma) <= tiny) by (rewrite Rabs_mult, (Rabs_pos_eq sin_r) by lra; destruct Ht; pose proof (Rabs_pos sigma); nra).
    apply Rle_trans with (Rabs (- (rr * (d * d)) - sin_r * sigma) + Rabs g2).
    - replace (- (rr * (d * d)) - sin_r * sigma + g2) with ((- (rr * (d * d)) - sin_r * sigma) + g2) by ring. apply Rabs_triang.
    - apply Rle_trans with (Rabs (rr * (d * d)) + Rabs (sin_r * sigma) + Rabs g2); [ | lra].
      assert (Rabs (- (rr * (d * d)) - sin_r * sigma) <= Rabs (rr * (d * d)) + Rabs (sin_r * sigma)).
      { replace (- (rr * (d * d)) - sin_r * sigma) with (- (rr * (d * d) + sin_r * sigma)) by ring.
        rewrite Rabs_Ropp. apply Rabs_triang. }
      lra. }
  assert (S5 : 0.7070 <= (1 + gamma) * cos_r) by nra.
  assert (S6 : Rabs Z * 0.7070 <= Rabs (d * (K - 1 - gamma) * cos_r + K * Bq)).
  { rewrite <- S1. rewrite Rabs_mult. rewrite (Rabs_pos_eq ((1 + gamma) * cos_r)) by lra.
    apply Rmult_le_compat_l; [apply Rabs_pos | exact S5]. }
  assert (S7 : Rabs (d * (K - 1 - gamma) * cos_r + K * Bq) <= Rabs d * (3.01 * tiny) + 1.0001 * (0.5000001 * (eta62 * eta62 * (Y * Y)) + 2 * tiny)).
  { apply Rle_trans with (Rabs (d * (K - 1 - gamma) * cos_r) + Rabs (K * Bq)); [apply Rabs_triang | ].
    assert (A1 : Rabs (d * (K - 1 - gamma) * cos_r) <= Rabs d * (3.01 * tiny)).
    { rewrite !Rabs_mult. rewrite (Rabs_pos_eq cos_r) by lra.
      pose proof (Rabs_pos d). pose proof (Rabs_pos (K - 1 - gamma)).
      assert (Rabs d * Rabs (K - 1 - gamma) <= Rabs d * (3.01 * tiny)) by (apply Rmult_le_compat_l; [apply Rabs_pos | exact S2]).
      apply Rle_trans with (Rabs d * Rabs (K - 1 - gamma) * 1);
        [apply Rmult_le_compat_l; [apply Rmult_le_pos; apply Rabs_pos | lra] | lra]. }
    assert (A2 : Rabs (K * Bq) <= 1.0001 * (0.5000001 * (eta62 * eta62 * (Y * Y)) + 2 * tiny)).
    { rewrite Rabs_mult. pose proof (Rabs_pos K). pose proof (Rabs_pos Bq).
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact S3 | exact S4]. }
    lra. }
  assert (Hyz : y1 - Y = Z + g3) by (unfold Z; rewrite Hy1, HY; ring).
  rewrite Hyz.
  apply Rle_trans with (Rabs Z + Rabs g3); [apply Rabs_triang | ].
  assert (Hy2 : Y * Y <= 0.7854 * Y) by nra.
  assert (Hy3 : 1 <= 67108864 * Y) by lra.
  assert (Hy0 : 0 < Y) by lra.
  assert (Hetap : 0 <= eta62) by (unfold eta62; lra).
  assert (F1 : Rabs d * (3.01 * tiny) <= (eta62 * Y) * (3.01 * tiny)) by (apply Rmult_le_compat_r; [lra | exact Hd]).
  assert (F2 : eta62 * eta62 * (Y * Y) <= eta62 * eta62 * 0.7854 * Y) by nra.
  assert (F3 : 2 * tiny <= 2 * tiny * (67108864 * Y)) by nra.
  assert (HZ : Rabs Z * 0.7070 <= Y * (eta62 * (3.01 * tiny) + 1.0001 * (0.5000001 * (eta62 * eta62 * 0.7854)) + 1.0001 * (2 * tiny * 67108864))) by nra.
  set (Cn := eta62 * (3.01 * tiny) + 1.0001 * (0.5000001 * (eta62 * eta62 * 0.7854)) + 1.0001 * (2 * tiny * 67108864)) in *.
  assert (Hnum : Cn / 0.7070 + tiny <= / 21267647932558653966460912964485513216)
    by (unfold Cn, eta62, tiny; interval with (i_prec 200)).
  assert (HCn : Cn <= 0.7070 * (/ 21267647932558653966460912964485513216 - tiny)).
  { unfold Rdiv in Hnum. nra. }
  assert (Hg3' : Rabs g3 <= tiny * Y) by exact Hg3.
  nra.
Qed.

(** The complement branch: [d1 = d0 + (cos d0 - x)/sin d0] for [D = acos x]. *)
Lemma newton_complement_real D r d x sn cs ri res prod dl sin_r cos_r sigma gamma e d3 g2 g3 rr :
  D = r + d -> D <= 0.7854 -> / 134217728 <= D ->
  Rabs d <= eta62 * D ->
  0.7071 <= cos_r -> cos_r <= 1 -> 0.88 * D <= sin_r -> sin_r <= 0.70711 ->
  x = cos_r - sin_r * d - rr * (d * d) -> - / 1152921504606846976 <= rr <= 0.5000001 ->
  sn = sin_r * (1 + sigma) -> Rabs sigma <= tiny ->
  cs = cos_r * (1 + gamma) -> Rabs gamma <= tiny ->
  sn * ri = 1 + e -> Rabs e <= tiny ->
  res = (cs - x) + g2 -> Rabs g2 <= tiny ->
  prod = res * ri * (1 + d3) -> Rabs d3 <= tiny ->
  dl = r + prod + g3 -> Rabs g3 <= tiny * D ->
  Rabs (dl - D) <= / 21267647932558653966460912964485513216 * D.
Proof.
  intros HD HD1 HD0 Hd Hc1 Hc2 Hs1 Hs2 Hx Hrr Hsn Hsig Hcs Hgam Hcr He Hres Hg2 Hprod Hd3 Hdl Hg3.
  assert (Ht : 0 < tiny <= / 1000000) by (unfold tiny; split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]).
  pose proof Hsig as Hsig0. pose proof Hgam as Hgam0. pose proof He as He0. pose proof Hd3 as Hd30.
  apply Rabs_le_inv in Hsig0. apply Rabs_le_inv in Hgam0. apply Rabs_le_inv in He0. apply Rabs_le_inv in Hd30.
  assert (Hres' : res = sin_r * d + (cos_r * gamma + rr * (d * d) + g2)).
  { rewrite Hres, Hx, Hcs. ring. }
  assert (Hsp : 0 < sin_r) by (assert (0 < D) by lra; nra).
  assert (Hsnp : sin_r <> 0) by lra.
  assert (Hcri : sin_r * ri * (1 + sigma) = 1 + e) by (rewrite <- Hcr, Hsn; ring).
  assert (Hri : ri * (1 + sigma) = (1 + e) / sin_r) by (rewrite <- Hcri; field; exact Hsnp).
  set (Bc := cos_r * gamma + rr * (d * d) + g2) in *.
  assert (Hprod' : prod * (1 + sigma) = (1 + d3) * (1 + e) * (d + Bc / sin_r)).
  { rewrite Hprod, Hres'.
    replace ((sin_r * d + Bc) * ri * (1 + d3) * (1 + sigma))
      with ((1 + d3) * ((sin_r * d) * (ri * (1 + sigma)) + Bc * (ri * (1 + sigma)))) by ring.
    rewrite Hri. field. exact Hsnp. }
  set (K := (1 + d3) * (1 + e)).
  set (Z := prod - d).
  assert (S1 : Z * ((1 + sigma) * sin_r) = d * (K - 1 - sigma) * sin_r + K * Bc).
  { unfold Z. assert (E : prod * (1 + sigma) * sin_r = K * (d * sin_r + Bc)).
    { rewrite Hprod'. unfold K. field. exact Hsnp. }
    nra. }
  assert (S2 : Rabs (K - 1 - sigma) <= 3.01 * tiny).
  { unfold K. replace ((1 + d3) * (1 + e) - 1 - sigma) with (d3 + e + d3 * e - sigma) by ring.
    assert (Rabs (d3 * e) <= tiny * tiny) by (rewrite Rabs_mult; apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hd3 | exact He]).
    apply Rabs_le_inv in H. apply Rabs_le. destruct Ht as [Ht0 Ht1]. nra. }
  assert (S3 : Rabs K <= 1.0001).
  { unfold K. apply Rabs_le. destruct Ht as [Ht0 Ht1]. nra. }
  assert (Hd2 : d * d <= eta62 * eta62 * (D * D)).
  { apply Rabs_le_inv in Hd. assert (0 <= eta62) by (unfold eta62; lra). nra. }
  assert (S4 : Rabs Bc <= 0.5000001 * (eta62 * eta62 * (D * D)) + 2 * tiny).
  { unfold Bc.
    assert (Rabs (rr * (d * d)) <= 0.5000001 * (eta62 * eta62 * (D * D))).
    { rewrite Rabs_mult. rewrite (Rabs_pos_eq (d * d)) by nra.
      assert (Rabs rr <= 0.5000001) by (apply Rabs_le; split; [ | lra]; lra).
      pose proof (Rabs_pos rr). nra. }
    assert (Rabs (cos_r * gamma) <= tiny) by (rewrite Rabs_mult, (Rabs_pos_eq cos_r) by lra; destruct Ht; pose proof (Rabs_pos gamma); nra).
    apply Rle_trans with (Rabs (cos_r * gamma + rr * (d * d)) + Rabs g2).
    - replace (cos_r * gamma + rr * (d * d) + g2) with ((cos_r * gamma + rr * (d * d)) + g2) by ring. apply Rabs_triang.
    - assert (Rabs (cos_r * gamma + rr * (d * d)) <= Rabs (cos_r * gamma) + Rabs (rr * (d * d))) by apply Rabs_triang.
      lra. }
  assert (S5 : 0.9999 * sin_r <= (1 + sigma) * sin_r) by nra.
  assert (S6 : Rabs Z * (0.9999 * sin_r) <= Rabs (d * (K - 1 - sigma) * sin_r + K * Bc)).
  { rewrite <- S1. rewrite Rabs_mult. rewrite (Rabs_pos_eq ((1 + sigma) * sin_r)) by nra.
    apply Rmult_le_compat_l; [apply Rabs_pos | exact S5]. }
  assert (S7 : Rabs (d * (K - 1 - sigma) * sin_r + K * Bc) <= Rabs d * (3.01 * tiny) + 1.0001 * (0.5000001 * (eta62 * eta62 * (D * D)) + 2 * tiny)).
  { apply Rle_trans with (Rabs (d * (K - 1 - sigma) * sin_r) + Rabs (K * Bc)); [apply Rabs_triang | ].
    assert (A1 : Rabs (d * (K - 1 - sigma) * sin_r) <= Rabs d * (3.01 * tiny)).
    { rewrite !Rabs_mult. rewrite (Rabs_pos_eq sin_r) by lra.
      pose proof (Rabs_pos d). pose proof (Rabs_pos (K - 1 - sigma)).
      assert (Rabs d * Rabs (K - 1 - sigma) <= Rabs d * (3.01 * tiny)) by (apply Rmult_le_compat_l; [apply Rabs_pos | exact S2]).
      apply Rle_trans with (Rabs d * Rabs (K - 1 - sigma) * 1);
        [apply Rmult_le_compat_l; [apply Rmult_le_pos; apply Rabs_pos | lra] | lra]. }
    assert (A2 : Rabs (K * Bc) <= 1.0001 * (0.5000001 * (eta62 * eta62 * (D * D)) + 2 * tiny)).
    { rewrite Rabs_mult. pose proof (Rabs_pos K). pose proof (Rabs_pos Bc).
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact S3 | exact S4]. }
    lra. }
  assert (Hyz : dl - D = Z + g3) by (unfold Z; rewrite Hdl, HD; ring).
  rewrite Hyz.
  apply Rle_trans with (Rabs Z + Rabs g3); [apply Rabs_triang | ].
  assert (Hy3 : 1 <= 134217728 * D) by lra.
  assert (Hd0 : 0 < D) by lra.
  assert (Hetap : 0 <= eta62) by (unfold eta62; lra).
  assert (F1 : Rabs d * (3.01 * tiny) <= D * D * (3.01 * tiny * eta62 * 134217728)).
  { assert (Rabs d * (3.01 * tiny) <= (eta62 * D) * (3.01 * tiny)) by (apply Rmult_le_compat_r; [lra | exact Hd]).
    destruct Ht as [Ht0 Ht1].
    assert (Hpos : 0 <= eta62 * D * (3.01 * tiny)) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]).
    assert (eta62 * D * (3.01 * tiny) * 1 <= eta62 * D * (3.01 * tiny) * (134217728 * D)) by (apply Rmult_le_compat_l; lra).
    nra. }
  assert (F3 : 1.0001 * (2 * tiny) <= D * D * (1.0001 * 2 * tiny * 134217728 * 134217728)).
  { destruct Ht as [Ht0 Ht1].
    assert (Hsq : 1 <= (134217728 * D) * (134217728 * D)) by nra.
    assert (1.0001 * (2 * tiny) * 1 <= 1.0001 * (2 * tiny) * ((134217728 * D) * (134217728 * D))) by (apply Rmult_le_compat_l; [lra | exact Hsq]).
    nra. }
  assert (HS : Rabs Z * (0.8799 * D) <= D * D * (3.01 * tiny * eta62 * 134217728 + 1.0001 * 0.5000001 * (eta62 * eta62) + 1.0001 * 2 * tiny * 134217728 * 134217728)).
  { assert (Rabs Z * (0.8799 * D) <= Rabs Z * (0.9999 * sin_r)) by (apply Rmult_le_compat_l; [apply Rabs_pos | nra]).
    nra. }
  set (Cn := 3.01 * tiny * eta62 * 134217728 + 1.0001 * 0.5000001 * (eta62 * eta62) + 1.0001 * 2 * tiny * 134217728 * 134217728) in *.
  assert (HZ : Rabs Z * 0.8799 <= D * Cn).
  { apply (Rmult_le_reg_r D); [exact Hd0 | ]. nra. }
  assert (Hnum : Cn / 0.8799 + tiny <= / 21267647932558653966460912964485513216)
    by (unfold Cn, eta62, tiny; interval with (i_prec 200)).
  assert (HCn : Cn <= 0.8799 * (/ 21267647932558653966460912964485513216 - tiny)).
  { unfold Rdiv in Hnum. nra. }
  assert (Hg3' : Rabs g3 <= tiny * D) by exact Hg3.
  nra.
Qed.

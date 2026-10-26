From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound.
Open Scope R_scope.

Lemma u_lt : u < 12 / 10 ^ 17. Proof. pose proof u_small. lra. Qed.

Lemma rel_mono x y t t' : rel x y t -> t <= t' -> rel x y t'.
Proof. unfold rel. intros H Ht. pose proof (Rabs_pos x). nra. Qed.

Lemma rel_lo x y t : 0 < x -> rel x y t -> (1 - t) * x <= y.
Proof. unfold rel. intros Hx H. rewrite (Rabs_right x) in H by lra. apply Rabs_le_inv in H. lra. Qed.

Lemma rel_hi x y t : 0 < x -> rel x y t -> y <= (1 + t) * x.
Proof. unfold rel. intros Hx H. rewrite (Rabs_right x) in H by lra. apply Rabs_le_inv in H. lra. Qed.

Lemma rel_trans x y z t1 t2 : 0 <= t1 -> 0 <= t2 -> rel x y t1 -> rel y z t2 -> rel x z (t1 + t2 * (1 + t1)).
Proof.
  unfold rel. intros H1 H2 Hxy Hyz.
  pose proof (Rabs_triang (z - y) (y - x)) as Ht. replace (z - y + (y - x)) with (z - x) in Ht by ring.
  assert (Hy : Rabs y <= (1 + t1) * Rabs x).
  { pose proof (Rabs_triang (y - x) x) as H3. replace (y - x + x) with y in H3 by ring. nra. }
  assert (t2 * Rabs y <= t2 * ((1 + t1) * Rabs x)) by (apply Rmult_le_compat_l; assumption).
  nra.
Qed.

Lemma sqrt_aux d S r t : 0 < r -> 0 <= t -> d * S <= t * (r * r) -> 199 / 100 * r <= S -> d <= 51 / 100 * t * r.
Proof.
  intros Hr Ht H1 H2.
  destruct (Rle_dec d 0) as [Hd|Hd].
  - nra.
  - assert (Hd' : 0 < d) by lra.
    assert (h : d * (199 / 100 * r) <= d * S) by (apply Rmult_le_compat_l; lra).
    assert (h2 : d * (199 / 100) * r <= t * r * r) by nra.
    assert (h3 : d * (199 / 100) <= t * r).
    { apply Rmult_le_reg_r with r; [exact Hr|]. nra. }
    nra.
Qed.

Lemma rel_sqrt a a' t : 0 < a -> 0 < a' -> 0 <= t -> t <= 1 / 100 -> rel a a' t -> rel (sqrt a) (sqrt a') (51 / 100 * t).
Proof.
  intros Ha Ha' Ht Ht1 H. unfold rel in *.
  rewrite (Rabs_right a) in H by lra. rewrite (Rabs_right (sqrt a)) by (left; apply sqrt_lt_R0; lra).
  pose proof (sqrt_lt_R0 a Ha) as Hsa. pose proof (sqrt_lt_R0 a' Ha') as Hsa'.
  pose proof (sqrt_sqrt a ltac:(lra)) as Ea. pose proof (sqrt_sqrt a' ltac:(lra)) as Ea'.
  apply Rabs_le_inv in H.
  assert (Hp : (sqrt a' - sqrt a) * (sqrt a' + sqrt a) = a' - a).
  { replace ((sqrt a' - sqrt a) * (sqrt a' + sqrt a)) with (sqrt a' * sqrt a' - sqrt a * sqrt a) by ring. rewrite Ea, Ea'. reflexivity. }
  assert (Hlow : 99 / 100 * sqrt a <= sqrt a').
  { apply Rnot_lt_le. intro Hc.
    assert (sqrt a' * sqrt a' < (99 / 100 * sqrt a) * (99 / 100 * sqrt a)) by nra. nra. }
  assert (Hs : (199 / 100) * sqrt a <= sqrt a' + sqrt a) by lra.
  apply Rabs_le. split.
  - assert (Hq : (sqrt a - sqrt a') * (sqrt a' + sqrt a) <= t * (sqrt a * sqrt a)) by (rewrite Ea; nra).
    pose proof (sqrt_aux (sqrt a - sqrt a') (sqrt a' + sqrt a) (sqrt a) t Hsa Ht Hq Hs). nra.
  - assert (Hq : (sqrt a' - sqrt a) * (sqrt a' + sqrt a) <= t * (sqrt a * sqrt a)) by (rewrite Ea; nra).
    pose proof (sqrt_aux (sqrt a' - sqrt a) (sqrt a' + sqrt a) (sqrt a) t Hsa Ht Hq Hs). nra.
Qed.

(** Relative closeness with an additive part. *)
Definition rela (x y t e : R) : Prop := Rabs (y - x) <= t * Rabs x + e.

Lemma rela_rnd x y t e : 0 <= t -> 0 <= e -> rela x y t e -> rela x (rnd y) (t + u + u * t) (e + eta + u * e).
Proof.
  unfold rela. intros Ht He H.
  pose proof (rnd_abs y) as Hr.
  pose proof (Rabs_triang (rnd y - y) (y - x)) as Htr. replace (rnd y - y + (y - x)) with (rnd y - x) in Htr by ring.
  assert (Hy : Rabs y <= (1 + t) * Rabs x + e).
  { pose proof (Rabs_triang (y - x) x) as H2. replace (y - x + x) with y in H2 by ring. nra. }
  assert (Hu : u * Rabs y <= u * ((1 + t) * Rabs x + e)) by (apply Rmult_le_compat_l; [left; apply u_pos | assumption]).
  nra.
Qed.

Lemma rela_div_rel a a' b b' t1 e1 t2 :
  0 < b -> 0 <= t1 -> 0 <= e1 -> 0 <= t2 -> t2 <= 1 / 2 -> rel b b' t2 -> rela a a' t1 e1 ->
  rela (a / b) (a' / b') ((t1 + t2) / (1 - t2)) (e1 / ((1 - t2) * b)).
Proof.
  intros Hb Ht1 He1 Ht2 Ht2' Hbb Haa. unfold rel, rela in *.
  rewrite (Rabs_right b) in Hbb by lra.
  apply Rabs_le_inv in Hbb.
  assert (Hb'lo : (1 - t2) * b <= b') by lra.
  assert (Hb'0 : 0 < b') by nra.
  assert (E : a' / b' - a / b = (a' - a) / b' + a * (b - b') / (b * b')) by (field; split; lra).
  rewrite E.
  pose proof (Rabs_triang ((a' - a) / b') (a * (b - b') / (b * b'))) as Ht.
  assert (H1 : Rabs ((a' - a) / b') <= (t1 * Rabs a + e1) / b').
  { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_right b') by lra.
    apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact Haa]. }
  assert (H2 : Rabs (a * (b - b') / (b * b')) <= Rabs a * (t2 * b) / (b * b')).
  { unfold Rdiv. rewrite Rabs_mult, Rabs_mult, Rabs_Rinv by (apply Rgt_not_eq; nra).
    rewrite (Rabs_right (b * b')) by nra.
    assert (Rabs (b - b') <= t2 * b) by (rewrite Rabs_minus_sym; apply Rabs_le; lra).
    apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; nra|].
    apply Rmult_le_compat_l; [apply Rabs_pos | assumption]. }
  assert (E2 : Rabs a * (t2 * b) / (b * b') = t2 * Rabs a / b') by (field; split; lra).
  assert (E3 : (t1 * Rabs a + e1) / b' + t2 * Rabs a / b' = ((t1 + t2) * Rabs a + e1) / b') by (field; lra).
  assert (H4 : ((t1 + t2) * Rabs a + e1) / b' <= ((t1 + t2) * Rabs a + e1) / ((1 - t2) * b)).
  { unfold Rdiv. apply Rmult_le_compat_l.
    - apply Rplus_le_le_0_compat; [apply Rmult_le_pos; [lra | apply Rabs_pos] | lra].
    - apply Rinv_le_contravar; [nra | lra]. }
  assert (E4 : ((t1 + t2) * Rabs a + e1) / ((1 - t2) * b)
               = (t1 + t2) / (1 - t2) * Rabs (a / b) + e1 / ((1 - t2) * b)).
  { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_right b) by lra. field. split; lra. }
  rewrite E2 in H2. lra.
Qed.

Lemma nrm_of x : 1 / 10 ^ 100 <= Rabs x -> nrm x.
Proof. intros H. right. assert (/ 10 ^ 300 <= 1 / 10 ^ 100) by interval. lra. Qed.

Lemma nrm_pos x : 1 / 10 ^ 100 <= x -> nrm x.
Proof. intros H. apply nrm_of. rewrite Rabs_right by (assert (0 < 1 / 10 ^ 100) by interval; lra). exact H. Qed.

(** xs = s^2 xu, as rounded: [s2T * xuT]. *)
Lemma st_xs s xu s2T xuT :
  3 / 1000 < s <= 381 / 1000 -> 1 / 4 <= xu <= 1 -> rel (s * s) s2T u -> rel xu xuT u ->
  rel (s * s * xu) (rnd (s2T * xuT)) (31 / 10 * u).
Proof.
  intros [Hs Hs'] [Hxu Hxu'] H1 H2. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hss : 9 / 1000000 <= s * s).
  { pose proof (Rmult_le_compat (3 / 1000) s (3 / 1000) s ltac:(lra) ltac:(lra) (Rlt_le _ _ Hs) (Rlt_le _ _ Hs)). lra. }
  pose proof (rel_lo (s * s) s2T u ltac:(lra) H1) as L1.
  pose proof (rel_lo xu xuT u ltac:(lra) H2) as L2.
  pose proof (rel_mul (s * s) s2T xu xuT u u (Rlt_le _ _ Hu) (Rlt_le _ _ Hu) H1 H2) as Hm.
  assert (Hn : nrm (s2T * xuT)).
  { apply nrm_pos. assert (1 / 10 ^ 100 <= 1 / 1000000) by interval.
    assert (A1 : 8 / 1000000 <= s2T) by nra.
    assert (A2 : 24 / 100 <= xuT) by nra.
    pose proof (Rmult_le_compat (8 / 1000000) s2T (24 / 100) xuT ltac:(lra) ltac:(lra) A1 A2). lra. }
  pose proof (rel_rnd (s * s * xu) (s2T * xuT) (u + u + u * u) Hn ltac:(nra) Hm) as Hr.
  eapply rel_mono; [exact Hr|]. nra.
Qed.

Lemma st_om xs xsT :
  0 < xs <= 1453 / 10000 -> rel xs xsT (31 / 10 * u) -> rel (1 - xs) (rnd (1 - xsT)) (18 / 10 * u).
Proof.
  intros [Hx0 Hx1] H. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (H1 : rel (1 - xs) (1 - xsT) (53 / 100 * u)).
  { unfold rel in *. rewrite (Rabs_right xs) in H by lra. rewrite (Rabs_right (1 - xs)) by lra.
    replace (1 - xsT - (1 - xs)) with (xs - xsT) by ring. rewrite Rabs_minus_sym.
    eapply Rle_trans; [exact H|]. nra. }
  assert (Hn : nrm (1 - xsT)).
  { apply nrm_pos. pose proof (rel_hi xs xsT (31 / 10 * u) Hx0 H). assert (1 / 10 ^ 100 <= 1 / 2) by interval. nra. }
  pose proof (rel_rnd (1 - xs) (1 - xsT) (53 / 100 * u) Hn ltac:(nra) H1) as Hr.
  eapply rel_mono; [exact Hr|]. nra.
Qed.

Lemma eta_small : eta <= / 10 ^ 300.
Proof.
  unfold eta. cbv [bpow]. cbn [radix2 radix_val Z.pow_pos].
  apply Rinv_le_contravar.
  - apply pow_lt; lra.
  - replace ((10:R) ^ 300) with (IZR (10 ^ 300)%Z) by (rewrite pow_IZR; reflexivity).
    apply IZR_le. vm_compute. discriminate.
Qed.

Section Steps.
Variable sqrtT : R -> R.
Hypothesis Hsq : forall x, 8 / 10 <= x -> x <= 1 -> rel (sqrt x) (sqrtT x) u.

Lemma st_rs xs xsT omT :
  0 < xs <= 1453 / 10000 -> rel xs xsT (31 / 10 * u) -> omT = rnd (1 - xsT) ->
  rel (1 - xs) omT (18 / 10 * u) -> rel (sqrt (1 - xs)) (sqrtT omT) (192 / 100 * u).
Proof.
  intros [Hx0 Hx1] H1 Eo H2. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  pose proof (rel_lo (1 - xs) omT (18 / 10 * u) ltac:(lra) H2) as L.
  assert (Hom1 : omT <= 1).
  { rewrite Eo.
    pose proof (rel_lo xs xsT (31 / 10 * u) Hx0 H1) as Hl.
    assert (Hxs0 : 0 <= xsT) by nra.
    pose proof (rnd_le (1 - xsT) 1 ltac:(lra)) as Hm. rewrite rnd_one in Hm. exact Hm. }
  assert (Hom0 : 8 / 10 <= omT) by nra.
  pose proof (rel_sqrt (1 - xs) omT (18 / 10 * u) ltac:(lra) ltac:(lra) ltac:(nra) ltac:(nra) H2) as Hs.
  pose proof (Hsq omT Hom0 Hom1) as Hc.
  pose proof (rel_trans (sqrt (1 - xs)) (sqrt omT) (sqrtT omT) (51 / 100 * (18 / 10 * u)) u ltac:(nra) ltac:(nra) Hs Hc) as Ht.
  eapply rel_mono; [exact Ht|]. nra.
Qed.

Lemma st_o rs rsT :
  924 / 1000 <= rs <= 1 -> rel rs rsT (192 / 100 * u) -> rel (1 + rs) (rnd (1 + rsT)) (2 * u).
Proof.
  intros [R0 R1] H. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (H1 : rel (1 + rs) (1 + rsT) (96 / 100 * u)).
  { unfold rel in *. rewrite (Rabs_right rs) in H by lra. rewrite (Rabs_right (1 + rs)) by lra.
    replace (1 + rsT - (1 + rs)) with (rsT - rs) by ring.
    eapply Rle_trans; [exact H|]. nra. }
  assert (Hn : nrm (1 + rsT)).
  { apply nrm_pos. pose proof (rel_lo rs rsT (192 / 100 * u) ltac:(lra) H). assert (1 / 10 ^ 100 <= 1 / 2) by interval. nra. }
  pose proof (rel_rnd (1 + rs) (1 + rsT) (96 / 100 * u) Hn ltac:(nra) H1) as Hr.
  eapply rel_mono; [exact Hr|]. nra.
Qed.
End Steps.

Lemma st_q bs bsT xs xsT e0 :
  2 / 1000000 <= xs <= 1453 / 10000 -> 0 <= e0 <= / 10 ^ 200 -> rel xs xsT (31 / 10 * u) ->
  rela bs bsT (31 / 10 * u) e0 ->
  rela (bs / (2 * xs)) (rnd (bsT / (2 * xsT))) (74 / 10 * u) (1 / 10 ^ 190).
Proof.
  intros [Hx0 Hx1] [He0 He1] H1 H2. pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  assert (Hxs2 : rel (2 * xs) (2 * xsT) (31 / 10 * u)).
  { unfold rel in *. rewrite (Rabs_right xs) in H1 by lra. rewrite (Rabs_right (2 * xs)) by lra.
    replace (2 * xsT - 2 * xs) with (2 * (xsT - xs)) by ring. rewrite Rabs_mult, (Rabs_right 2) by lra. nra. }
  pose proof (rela_div_rel bs bsT (2 * xs) (2 * xsT) (31 / 10 * u) e0 (31 / 10 * u) ltac:(lra) ltac:(nra) He0 ltac:(nra) ltac:(nra) Hxs2 H2) as Hd.
  assert (Ht : 0 <= (31 / 10 * u + 31 / 10 * u) / (1 - 31 / 10 * u)).
  { unfold Rdiv. apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; nra]. }
  assert (He : 0 <= e0 / ((1 - 31 / 10 * u) * (2 * xs))).
  { apply Rmult_le_pos; [exact He0 | left; apply Rinv_0_lt_compat; nra]. }
  pose proof (rela_rnd _ _ _ _ Ht He Hd) as Hr.
  unfold rela in *.
  assert (Hc1 : (31 / 10 * u + 31 / 10 * u) / (1 - 31 / 10 * u) + u + u * ((31 / 10 * u + 31 / 10 * u) / (1 - 31 / 10 * u)) <= 74 / 10 * u).
  { assert (Hq : (31 / 10 * u + 31 / 10 * u) / (1 - 31 / 10 * u) <= 63 / 10 * u).
    { apply Rmult_le_reg_r with (1 - 31 / 10 * u); [nra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by nra. nra. }
    nra. }
  assert (Hc2 : e0 / ((1 - 31 / 10 * u) * (2 * xs)) + eta + u * (e0 / ((1 - 31 / 10 * u) * (2 * xs))) <= 1 / 10 ^ 190).
  { assert (HH : 39 / 10 ^ 7 <= (1 - 31 / 10 * u) * (2 * xs)) by nra.
    assert (Hinv : / ((1 - 31 / 10 * u) * (2 * xs)) <= 3 * 10 ^ 5).
    { apply Rle_trans with (/ (39 / 10 ^ 7)).
      - apply Rinv_le_contravar; [apply Rdiv_lt_0_compat; [lra | apply pow_lt; lra] | exact HH].
      - assert (E0 : / (39 / 10 ^ 7) = 10 ^ 7 / 39) by (field). rewrite E0. interval. }
    assert (Hq : e0 / ((1 - 31 / 10 * u) * (2 * xs)) <= / 10 ^ 200 * (3 * 10 ^ 5)).
    { unfold Rdiv. apply Rle_trans with (/ 10 ^ 200 * / ((1 - 31 / 10 * u) * (2 * xs))).
      - apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; nra | exact He1].
      - apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat; apply pow_lt; lra | exact Hinv]. }
    assert (E1 : / 10 ^ 200 * (3 * 10 ^ 5) = 3 / 10 ^ 195) by (field).
    assert (E2 : 3 / 10 ^ 195 + / 10 ^ 300 + 1 / 10 ^ 10 * (3 / 10 ^ 195) <= 1 / 10 ^ 190) by interval.
    assert (Hp : 0 <= e0 / ((1 - 31 / 10 * u) * (2 * xs))) by (apply Rmult_le_pos; [exact He0 | left; apply Rinv_0_lt_compat; nra]).
    nra. }
  pose proof (Rmult_le_compat_r (Rabs (bs / (2 * xs))) _ _ (Rabs_pos _) Hc1) as Hm.
  lra.
Qed.

Lemma st_r2 hk hkT rs oT e0 :
  9244 / 10000 <= rs <= 1 -> 0 <= e0 <= / 10 ^ 200 -> rela hk hkT u e0 -> rel (1 + rs) oT (2 * u) ->
  rela (hk / (1 + rs)) (rnd (hkT / oT)) (41 / 10 * u) (1 / 10 ^ 190).
Proof.
  intros [R0 R1] [He0 He1] H1 H2. pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof (rela_div_rel hk hkT (1 + rs) oT u e0 (2 * u) ltac:(lra) (Rlt_le _ _ Hu) He0 ltac:(nra) ltac:(nra) H2 H1) as Hd.
  assert (Ht : 0 <= (u + 2 * u) / (1 - 2 * u)).
  { unfold Rdiv. apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; nra]. }
  assert (He : 0 <= e0 / ((1 - 2 * u) * (1 + rs))).
  { apply Rmult_le_pos; [exact He0 | left; apply Rinv_0_lt_compat; nra]. }
  pose proof (rela_rnd _ _ _ _ Ht He Hd) as Hr.
  unfold rela in *.
  assert (Hc1 : (u + 2 * u) / (1 - 2 * u) + u + u * ((u + 2 * u) / (1 - 2 * u)) <= 41 / 10 * u).
  { assert (Hq : (u + 2 * u) / (1 - 2 * u) <= 301 / 100 * u).
    { apply Rmult_le_reg_r with (1 - 2 * u); [nra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by nra. nra. }
    nra. }
  assert (Hc2 : e0 / ((1 - 2 * u) * (1 + rs)) + eta + u * (e0 / ((1 - 2 * u) * (1 + rs))) <= 1 / 10 ^ 190).
  { assert (Hinv : / ((1 - 2 * u) * (1 + rs)) <= 1).
    { rewrite <- Rinv_1. apply Rinv_le_contravar; [lra | nra]. }
    assert (Hq : e0 / ((1 - 2 * u) * (1 + rs)) <= / 10 ^ 200).
    { unfold Rdiv. apply Rle_trans with (/ 10 ^ 200 * / ((1 - 2 * u) * (1 + rs))).
      - apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; nra | exact He1].
      - assert (0 <= / 10 ^ 200) by (left; apply Rinv_0_lt_compat; apply pow_lt; lra). nra. }
    assert (E2 : / 10 ^ 200 + / 10 ^ 300 + 1 / 10 ^ 10 * / 10 ^ 200 <= 1 / 10 ^ 190) by interval.
    assert (Hp : 0 <= e0 / ((1 - 2 * u) * (1 + rs))) by exact He.
    nra. }
  pose proof (Rmult_le_compat_r (Rabs (hk / (1 + rs))) _ _ (Rabs_pos _) Hc1) as Hm.
  lra.
Qed.

Lemma st_phi q qT r2 r2T :
  0 <= q -> rela q qT (74 / 10 * u) (1 / 10 ^ 190) -> rela r2 r2T (41 / 10 * u) (1 / 10 ^ 190) ->
  Rabs (rnd (qT + r2T) - (q + r2)) <= 85 / 10 * u * (q + Rabs r2) + 1 / 10 ^ 189.
Proof.
  intros Hq H1 H2. unfold rela in *. pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  rewrite (Rabs_right q) in H1 by lra.
  pose proof (rnd_abs (qT + r2T)) as Hr.
  assert (Hs : Rabs (qT + r2T - (q + r2)) <= 74 / 10 * u * q + 41 / 10 * u * Rabs r2 + 2 / 10 ^ 190).
  { pose proof (Rabs_triang (qT - q) (r2T - r2)).
    replace (qT + r2T - (q + r2)) with ((qT - q) + (r2T - r2)) by ring. lra. }
  assert (Hy : Rabs (qT + r2T) <= (1 + 74 / 10 * u) * q + (1 + 41 / 10 * u) * Rabs r2 + 2 / 10 ^ 190).
  { pose proof (Rabs_triang (qT + r2T - (q + r2)) (q + r2)). pose proof (Rabs_triang q r2).
    replace (qT + r2T - (q + r2) + (q + r2)) with (qT + r2T) in H by ring.
    rewrite (Rabs_right q) in H0 by lra. nra. }
  pose proof (Rabs_triang (rnd (qT + r2T) - (qT + r2T)) (qT + r2T - (q + r2))) as Ht.
  replace (rnd (qT + r2T) - (qT + r2T) + (qT + r2T - (q + r2))) with (rnd (qT + r2T) - (q + r2)) in Ht by ring.
  assert (Hu' : u * Rabs (qT + r2T) <= u * ((1 + 74 / 10 * u) * q + (1 + 41 / 10 * u) * Rabs r2 + 2 / 10 ^ 190))
    by (apply Rmult_le_compat_l; [left; exact Hu | exact Hy]).
  pose proof (Rabs_pos r2).
  assert (E : 2 / 10 ^ 190 + u * (2 / 10 ^ 190) + eta <= 1 / 10 ^ 189).
  { assert (2 / 10 ^ 190 + 1 / 10 ^ 10 * (2 / 10 ^ 190) + / 10 ^ 300 <= 1 / 10 ^ 189) by interval. nra. }
  assert (A0 : 0 <= u * q) by nra.
  assert (B0 : 0 <= u * Rabs r2) by nra.
  assert (A1 : u * (u * q) <= (1 / 100) * (u * q)) by nra.
  assert (B1 : u * (u * Rabs r2) <= (1 / 100) * (u * Rabs r2)) by nra.
  assert (Ex : u * ((1 + 74 / 10 * u) * q + (1 + 41 / 10 * u) * Rabs r2 + 2 / 10 ^ 190)
               = u * q + 74 / 10 * (u * (u * q)) + u * Rabs r2 + 41 / 10 * (u * (u * Rabs r2)) + u * (2 / 10 ^ 190)) by ring.
  assert (Ex2 : 85 / 10 * u * (q + Rabs r2) = 85 / 10 * (u * q) + 85 / 10 * (u * Rabs r2)) by ring.
  assert (Ex3 : 74 / 10 * u * q = 74 / 10 * (u * q)) by ring.
  assert (Ex4 : 41 / 10 * u * Rabs r2 = 41 / 10 * (u * Rabs r2)) by ring.
  lra.
Qed.

Lemma xe_bound x : 0 <= x -> x * exp (- x) <= 3679 / 10000.
Proof.
  intros Hx.
  pose proof (exp_ineq1_le (x - 1)) as H. replace (1 + (x - 1)) with x in H by ring.
  assert (E : exp (x - 1) = exp x * exp (-1)) by (rewrite <- exp_plus; f_equal; ring).
  assert (Hm : exp (- 1) <= 36788 / 100000) by interval.
  assert (Hp : 0 < exp x) by apply exp_pos. assert (Hp' : 0 < exp (-1)) by apply exp_pos.
  rewrite exp_Ropp. 
  assert (Hx2 : x * / exp x <= exp (-1)).
  { apply Rmult_le_reg_r with (exp x); [exact Hp|]. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  lra.
Qed.

Lemma rs_bounds xs : 0 < xs <= 1453 / 10000 -> 9244 / 10000 <= sqrt (1 - xs) <= 1.
Proof.
  intros [H0 H1].
  pose proof (sqrt_sqrt (1 - xs) ltac:(lra)) as E.
  pose proof (sqrt_pos (1 - xs)) as P.
  split.
  - apply Rnot_lt_le. intro Hc. nra.
  - apply Rnot_lt_le. intro Hc. nra.
Qed.

Lemma F_mag xs bs hk :
  2 / 10 ^ 6 <= xs <= 1453 / 10000 -> 0 <= bs -> - (4 * hk) <= bs ->
  let rs := sqrt (1 - xs) in let q := bs / (2 * xs) in let r2 := hk / (1 + rs) in
  0 <= q + r2 /\ q + Rabs r2 <= 1157 / 1000 * (q + r2) /\ exp (- (q + r2)) * (q + Rabs r2) <= 426 / 1000.
Proof.
  intros [Hx0 Hx1] Hbs Hc rs q r2.
  assert (Hx0' : 0 < xs) by (assert (0 < 2 / 10 ^ 6) by interval; lra).
  pose proof (rs_bounds xs (conj Hx0' Hx1)) as [R0 R1].
  change (9244 / 10000 <= rs) in R0. change (rs <= 1) in R1.
  assert (Hq0 : 0 <= q) by (unfold q; apply Rmult_le_pos; [exact Hbs | left; apply Rinv_0_lt_compat; lra]).
  assert (Hq : q * (2 * xs) = bs) by (unfold q; field; lra).
  destruct (Rle_dec 0 hk) as [Hk|Hk].
  - assert (Hr : 0 <= r2) by (unfold r2; apply Rmult_le_pos; [exact Hk | left; apply Rinv_0_lt_compat; lra]).
    rewrite (Rabs_right r2) by lra.
    repeat split.
    + lra.
    + nra.
    + pose proof (xe_bound (q + r2) ltac:(lra)). 
      assert (E : exp (- (q + r2)) * (q + r2) = (q + r2) * exp (- (q + r2))) by ring. lra.
  - assert (Hr : r2 <= 0).
    { unfold r2. assert (0 < / (1 + rs)) by (apply Rinv_0_lt_compat; lra). nra. }
    assert (Habs : Rabs r2 = - r2) by (apply Rabs_left1; exact Hr).
    assert (Hr2 : - r2 <= - hk).
    { unfold r2. assert (H1 : 1 <= 1 + rs) by lra.
      assert (H2 : / (1 + rs) <= 1) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
      assert (H3 : 0 < / (1 + rs)) by (apply Rinv_0_lt_compat; lra). nra. }
    assert (Hq2 : 137 / 10 * (- hk) <= q).
    { assert (bs >= 4 * (- hk)) by lra. nra. }
    assert (Hn : - r2 <= q / (137 / 10)) by lra.
    rewrite Habs.
    assert (Hphi : 927 / 1000 * q <= q + r2) by nra.
    repeat split.
    + nra.
    + nra.
    + assert (Hy : (927 / 1000 * q) * exp (- (927 / 1000 * q)) <= 3679 / 10000) by (apply xe_bound; nra).
      assert (He : exp (- (q + r2)) <= exp (- (927 / 1000 * q))).
      { destruct (Rle_lt_or_eq_dec _ _ Hphi) as [Hl|Heq].
        - left. apply exp_increasing. lra.
        - rewrite Heq. lra. }
      assert (Hp : 0 <= exp (- (927 / 1000 * q))) by (left; apply exp_pos).
      assert (Hpa : q + - r2 <= 1073 / 1000 * q) by nra.
      assert (He0 : 0 < exp (- (q + r2))) by apply exp_pos.
      assert (H5 : exp (- (q + r2)) * (q + - r2) <= exp (- (927 / 1000 * q)) * (1073 / 1000 * q)).
      { apply Rmult_le_compat; [left; exact He0 | nra | exact He | exact Hpa]. }
      nra.
Qed.

Lemma exp_pert phi phiT D :
  Rabs (phiT - phi) <= D -> 0 <= D -> D <= 1 / 2 -> rel (exp (- phi)) (exp (- phiT)) (D + 2 * (D * D)).
Proof.
  intros H HD0 HD1. unfold rel.
  assert (Hp : 0 < exp (- phi)) by apply exp_pos.
  rewrite (Rabs_right (exp (- phi))) by lra.
  set (y := phi - phiT).
  assert (Hy : Rabs y <= D) by (unfold y; rewrite Rabs_minus_sym; exact H).
  apply Rabs_le_inv in Hy.
  assert (E : exp (- phiT) = exp (- phi) * exp y) by (rewrite <- exp_plus; f_equal; unfold y; ring).
  rewrite E.
  replace (exp (- phi) * exp y - exp (- phi)) with (exp (- phi) * (exp y - 1)) by ring.
  rewrite Rabs_mult, (Rabs_right (exp (- phi))) by lra.
  replace ((D + 2 * (D * D)) * exp (- phi)) with (exp (- phi) * (D + 2 * (D * D))) by ring.
  apply Rmult_le_compat_l; [left; exact Hp|].
  apply Rabs_le. split.
  - pose proof (exp_ineq1_le y). nra.
  - pose proof (exp_ineq1_le (- y)) as Hb. rewrite exp_Ropp in Hb.
    assert (Hpy : 0 < exp y) by apply exp_pos.
    assert (Hb2 : 1 - y <= / exp y) by lra.
    assert (Hb3 : (1 - y) * exp y <= 1).
    { apply Rmult_le_reg_r with (/ exp y); [apply Rinv_0_lt_compat; lra|]. rewrite Rmult_assoc, Rinv_r by lra. nra. }
    assert (Hone : 0 < 1 - y) by lra.
    assert (Hex : exp y <= 1 + y + 2 * (y * y)) by nra.
    nra.
Qed.


Lemma ch_rnd th L : 0 <= th -> th <= L -> L <= 1 / 10 ^ 12 -> th + u + u * th <= L + 1001 / 1000 * u.
Proof.
  intros H0 H1 H2. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hu3 : u * th <= u * (1 / 10 ^ 12)) by (apply Rmult_le_compat_l; [lra | lra]).
  assert (u * (1 / 10 ^ 12) <= 1 / 1000 * u) by (assert (1 / 10 ^ 12 <= 1 / 1000) by interval; nra).
  lra.
Qed.

Lemma ch_div th a L : 0 <= th -> th <= L -> L <= 1 / 10 ^ 12 -> 0 <= a <= 2 * u -> (th + a) / (1 - a) <= L + 2 * u + 1 / 1000 * u.
Proof.
  intros H0 H1 H2 [Ha0 Ha1]. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hd : (th + a) / (1 - a) = (th + a) + (th + a) * (a / (1 - a))).
  { field. lra. }
  assert (Hq : a / (1 - a) <= 3 * u).
  { apply Rmult_le_reg_r with (1 - a); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  assert (Hq0 : 0 <= a / (1 - a)) by (unfold Rdiv; apply Rmult_le_pos; [exact Ha0 | left; apply Rinv_0_lt_compat; lra]).
  assert (Hs : (th + a) * (a / (1 - a)) <= (1 / 10 ^ 12 + 1) * (3 * u)).
  { apply Rmult_le_compat; [lra | exact Hq0 | lra | exact Hq]. }
  assert (Hv : (1 / 10 ^ 12 + 1) * (3 * u) <= 4 * u) by (assert (1 / 10 ^ 12 <= 1 / 3) by interval; nra).
  nra.
Qed.

Lemma ch_step th L : 0 <= th -> th <= L -> L <= 1 / 10 ^ 12 ->
  (u + th + u * th) + u + u * (u + th + u * th) <= L + 2003 / 1000 * u.
Proof.
  intros H0 H1 H2. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hc : u * (u + th + u * th) <= 1 / 1000 * u).
  { assert (u + th + u * th <= 1 / 1000) by (assert (1 / 10 ^ 12 <= 1 / 2000) by interval; nra). nra. }
  assert (Hd : u * th <= 1 / 2000 * u) by (assert (th <= 1 / 2000) by (assert (1 / 10 ^ 12 <= 1 / 2000) by interval; lra); nra).
  lra.
Qed.

Lemma inv_ge a b : 0 < a -> a <= b -> / b <= / a.
Proof. intros Ha Hab. apply Rinv_le_contravar; assumption. Qed.

Lemma theta1_bound u X E :
  0 < u -> u < 12 / 10 ^ 17 -> 0 <= X -> X <= 2 / 10 ^ 13 -> 0 < E -> E <= 1 / 10 ^ 30 ->
  let D := 85 / 10 * X + E in
  (D + 2 * (D * D)) + u * (1 + (D + 2 * (D * D))) <= u + 851 / 100 * X + 2 * E.
Proof.
  intros Hu Hu2 HX HX2 HE HE2 D.
  assert (HD0 : 0 <= D) by (unfold D; lra).
  assert (HDd : D <= 3 / 10 ^ 12).
  { unfold D. assert (85 / 10 * (2 / 10 ^ 13) <= 2 / 10 ^ 12) by interval. assert (1 / 10 ^ 30 <= 1 / 10 ^ 12) by interval. nra. }
  assert (HDD : D * D <= D * (3 / 10 ^ 12)) by (apply Rmult_le_compat_l; lra).
  assert (Hc : u * (1 + (D + 2 * (D * D))) <= u * 2) by (apply Rmult_le_compat_l; [lra | assert (D + 2 * (D * D) <= 1) by nra; lra]).
  assert (Hk : (D + 2 * (D * D)) <= D * (1 + 6 / 10 ^ 12)) by nra.
  assert (Hk2 : D * (1 + 6 / 10 ^ 12) = 85 / 10 * X + E + (85 / 10 * X + E) * (6 / 10 ^ 12)) by (unfold D; ring).
  assert (Hk3 : (85 / 10 * X + E) * (6 / 10 ^ 12) <= 1 / 100 * X + E) by (assert (85 / 10 * (6 / 10 ^ 12) <= 1 / 100) by interval; assert (6 / 10 ^ 12 <= 1) by interval; nra).
  (* u * (D + 2 D^2) <= u * D * (1 + ..) <= small *)
  assert (Hu1 : u * (D + 2 * (D * D)) <= 1 / 10 ^ 12 * D).
  { assert (D + 2 * (D * D) <= 2 * D) by nra. assert (u * (2 * D) <= 1 / 10 ^ 12 * D) by (assert (2 * u <= 1 / 10 ^ 12) by (assert (2 * (12 / 10 ^ 17) <= 1 / 10 ^ 12) by interval; lra); nra). nra. }
  assert (Hu3 : 1 / 10 ^ 12 * D <= 1 / 100 * X + E).
  { unfold D. assert (1 / 10 ^ 12 * (85 / 10) <= 1 / 100) by interval. assert (1 / 10 ^ 12 <= 1) by interval. nra. }
  nra.
Qed.


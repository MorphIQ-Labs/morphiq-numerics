(** The low-correlation kernel (formal/bivariate/BvnKernel.v) against the
    real-valued transcription its error proof is written over (BvnLow.v, BvnArg.v,
    BvnNode.v, BvnSum.v, BvnFinal.v, BvnRule.v): each binary64 function of the
    kernel returns the value of the matching function of the proof, under the
    magnitude bounds the proof's own hypotheses give, so no operation overflows. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Sqrt IEEE64Div.
Require Import BvnKernel BvnLift.
Require Import BvnRound BvnQ BvnArg BvnNode BvnTrig BvnLow BvnSum BvnTail BvnFinal BvnRule BvnTop.
Open Scope R_scope.

(* The unifier would otherwise unfold the binary64 operations of a failed match. *)
Local Opaque fadd fsub fmul fdiv fsqrt fneg fabs.

(** The node's angle. *)
Lemma node_angle_ok asr sign x ra sgn xh :
  exb asr ra 1 -> exb sign sgn 0 -> exb x xh 0 -> (sgn = 1 \/ sgn = -1) ->
  exb (node_angle asr sign x) (angle ra sgn xh) 2.
Proof.
  intros Ha Hs Hx Hsg. unfold node_angle, angle.
  assert (Hsx : exb (sign *f x) (sgn * xh) 0) by (apply exb_mul_sign; [exact Hs | exact Hx | exact Hsg | lia]).
  lift_to.
Qed.

Lemma sq_diff_ok xf yf x y : exb xf x 6 -> exb yf y 6 ->
  exb (sq_diff xf yf) (rndF (rndF (x - y) * rndF (x - y))) 14.
Proof. intros Hx Hy. unfold sq_diff. lift_to. Qed.

Lemma sq_sum_ok xf yf x y : exb xf x 6 -> exb yf y 6 ->
  exb (sq_sum xf yf) (rndF (rndF (x + y) * rndF (x + y))) 14.
Proof. intros Hx Hy. unfold sq_sum. lift_to. Qed.

Section Node.
Variables (L : lib) (expI sinI : R -> R).
Hypotheses (Hexp : lib_exp_rel L expI 0 1) (Hsin : lib_sin_rel L sinI).

(** One node's term: the kernel's [low_term] at the table's [p] and [q] for the
    sine of the node's angle is [node_term], the proof's [rndF (wh * expI (- argnc ..))]. *)
Lemma low_node_ok xf yf asrf sgnf xhf kwf x y asr sgn xh wh Ew :
  exb xf x 6 -> exb yf y 6 -> exb asrf asr 1 -> exb sgnf sgn 0 -> (sgn = 1 \/ sgn = -1) ->
  exb xhf xh 0 -> exb kwf wh Ew -> (0 <= Ew <= 100)%Z ->
  Rabs (angle asr sgn xh) <= 3 / 2 -> Rabs (sinI (angle asr sgn xh)) <= 99 / 100 ->
  exb (low_term L (sq_diff xf yf) (sq_sum xf yf) kwf
         (kquarter /f (k1 -f lib_sin L (node_angle asrf sgnf xhf)))
         (kquarter /f (k1 +f lib_sin L (node_angle asrf sgnf xhf))))
      (node_term expI sinI x y asr sgn xh wh) (Ew + 1).
Proof.
  intros Hx Hy Ha Hs Hsg Hxh Hw HEw Hth Hsh.
  unfold node_term, termf, argnc, low_term.
  pose proof (node_angle_ok asrf sgnf xhf asr sgn xh Ha Hs Hxh Hsg) as Hang.
  assert (Hsn : exb (lib_sin L (node_angle asrf sgnf xhf)) (sinI (angle asr sgn xh)) 1).
  { eapply exb_lib_sin; [exact Hsin | exact Hang | lra]. }
  set (sh := sinI (angle asr sgn xh)) in *.
  assert (D1 : divlow (rndF (1 - sh)) 7).
  { apply divlow_rnd; [ | lia | lia]. apply Rabs_le_inv in Hsh. simpl. lra. }
  assert (D2 : divlow (rndF (1 + sh)) 7).
  { apply divlow_rnd; [ | lia | lia]. apply Rabs_le_inv in Hsh. simpl. lra. }
  pose proof (sq_diff_ok xf yf x y Hx Hy) as Hd.
  pose proof (sq_sum_ok xf yf x y Hx Hy) as Hm.
  assert (N1 : 0 <= rndF (1 - sh)).
  { apply rnd_nonneg0. apply Rabs_le_inv in Hsh. lra. }
  assert (N2 : 0 <= rndF (1 + sh)).
  { apply rnd_nonneg0. apply Rabs_le_inv in Hsh. lra. }
  assert (N1' : 0 < rndF (1 - sh)).
  { unfold divlow in D1. rewrite Rabs_pos_eq in D1 by exact N1. eapply Rlt_le_trans; [apply bpow_gt_0 | exact D1]. }
  assert (N2' : 0 < rndF (1 + sh)).
  { unfold divlow in D2. rewrite Rabs_pos_eq in D2 by exact N2. eapply Rlt_le_trans; [apply bpow_gt_0 | exact D2]. }
  assert (Harg : 0 <= rndF (rndF (rndF (rndF (x - y) * rndF (x - y)) * rndF (/ 4 / rndF (1 - sh)))
                          + rndF (rndF (rndF (x + y) * rndF (x + y)) * rndF (/ 4 / rndF (1 + sh))))).
  { apply rnd_nonneg0. apply Rplus_le_le_0_compat; apply rnd_nonneg0; apply Rmult_le_pos; apply rnd_nonneg0.
    - apply Rle_0_sqr.
    - unfold Rdiv. apply Rmult_le_pos; [lra | apply Rlt_le; apply Rinv_0_lt_compat; exact N1'].
    - apply Rle_0_sqr.
    - unfold Rdiv. apply Rmult_le_pos; [lra | apply Rlt_le; apply Rinv_0_lt_compat; exact N2']. }
  lift_to.
Qed.
End Node.

(** The double-word accumulation: the kernel's [low_sum] over the table's nodes is
    the proof's [acc] over the nodes' terms. A bound on each running word is
    carried through the induction only to exclude overflow: it grows by [2^5] per
    term, from [2^E] to [2^(E + 5 n)] for [n] terms. *)
Section Accumulate.
Variables (L : lib) (d m : f64).

Variable Et : Z.

Definition term_rel (nd : f64 * f64 * f64) (t : R) : Prop :=
  exb (low_term L d m (fst (fst nd)) (snd (fst nd)) (snd nd)) t Et.

Lemma low_sum_ok nds ts : Forall2 term_rel nds ts -> forall hi lo rh rl E,
  exb hi rh E -> exb lo rl E -> (Et <= E)%Z -> (1 <= E)%Z -> (E + 5 * Z.of_nat (length nds) <= 900)%Z ->
  exb (fst (low_sum L d m nds hi lo)) (fst (acc ts (rh, rl))) (E + 5 * Z.of_nat (length nds))
  /\ exb (snd (low_sum L d m nds hi lo)) (snd (acc ts (rh, rl))) (E + 5 * Z.of_nat (length nds)).
Proof.
  intros HF. induction HF as [| nd t nds ts Hn Hrest IH]; intros hi lo rh rl E Hh Hl HEt HE1 HE.
  - simpl. split; (eapply exb_weak; [eassumption | simpl; lia]).
  - destruct nd as [[kw p] q]. cbn [low_sum acc length fst snd step] in *.
    unfold term_rel in Hn. cbn [fst snd] in Hn.
    set (term := low_term L d m kw p q) in *.
    destruct (two_sum64 hi term) as [s e] eqn:Hts.
    destruct (two_sum rh t) as [rs re] eqn:Hts'.
    assert (Hh' : exb hi rh E) by exact Hh.
    destruct (exb_two_sum hi term rh t E Hh' (exb_weak _ _ _ E Hn HEt) ltac:(lia)) as [Hs He].
    rewrite Hts, Hts' in Hs, He. cbn [fst snd] in Hs, He.
    assert (Hs5 : exb s rs (E + 5)) by (eapply exb_weak; [exact Hs | lia]).
    assert (Hlow : exb (lo +f e) (rndF (rl + re)) (E + 5)).
    { eapply exb_weak; [apply (exb_add lo e rl re E (E + 4) Hl He ltac:(unfold cl; lia)) | unfold cl; lia]. }
    pose proof (IH s (lo +f e) rs (rndF (rl + re)) (E + 5)%Z Hs5 Hlow ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
    replace (E + 5 * Z.of_nat (S (length nds)))%Z with (E + 5 + 5 * Z.of_nat (length nds))%Z by (rewrite Nat2Z.inj_succ; ring).
    split; assumption.
Qed.
End Accumulate.

(** The kernel's [PRODUCT_EXACT_FLOOR] is the binary64 nearest [1e-270], the
    least binary64 at or above it, so on binary64 values the proof's test
    [PFLOOR <= hi] and the kernel's [hi >= 1e-270] are one test. *)
Definition Bfloor : R := IZR 4758454107128906 * bpow radix2 (-949).

Lemma floor_exb : exb kproduct_floor Bfloor (-896).
Proof.
  unfold kproduct_floor. refine (exb_of_bits _ false 4758454107128906%positive (-949)%Z _ _ _ _ _).
  - vm_compute. reflexivity.
  - reflexivity.
  - rewrite Rabs_pos_eq.
    + unfold Bfloor. replace (-896)%Z with (53 + -949)%Z by reflexivity. rewrite bpow_plus.
      apply Rmult_le_compat_r; [apply bpow_ge_0 |]. change (IZR 4758454107128906 <= bpow radix2 53).
      simpl. lra.
    + unfold Bfloor. apply Rmult_le_pos; [lra | apply bpow_ge_0].
Qed.

Lemma frac_lt a P Q : 0 < P -> 0 < Q -> a * P < Q -> a * / Q < / P.
Proof.
  intros HP HQ H.
  assert (HP0 : P <> 0) by (intro Hz; lra).
  assert (HQ0 : Q <> 0) by (intro Hz; lra).
  apply Rmult_lt_reg_r with (P * Q); [nra |].
  replace (a * / Q * (P * Q)) with (a * P) by (field; assumption).
  replace (/ P * (P * Q)) with Q by (field; assumption). exact H.
Qed.

Lemma frac_gt a P Q : 0 < P -> 0 < Q -> Q < a * P -> / P < a * / Q.
Proof.
  intros HP HQ H.
  assert (HP0 : P <> 0) by (intro Hz; lra).
  assert (HQ0 : Q <> 0) by (intro Hz; lra).
  apply Rmult_lt_reg_r with (P * Q); [nra |].
  replace (a * / Q * (P * Q)) with (a * P) by (field; assumption).
  replace (/ P * (P * Q)) with Q by (field; assumption). exact H.
Qed.

Lemma floor_bounds : IZR 4758454107128905 * bpow radix2 (-949) < PFLOOR /\ PFLOOR < Bfloor.
Proof.
  unfold PFLOOR, Bfloor.
  replace (-949)%Z with (- (949))%Z by reflexivity. rewrite bpow_opp.
  change (bpow radix2 949) with (IZR (Zpower_pos 2 949)).
  assert (HP : 0 < IZR (10 ^ 270)) by (apply IZR_lt; reflexivity).
  assert (HQ : 0 < IZR (Zpower_pos 2 949)) by (apply IZR_lt; reflexivity).
  assert (A : (4758454107128905 * 10 ^ 270 < Zpower_pos 2 949)%Z) by (vm_compute; reflexivity).
  assert (B1 : (Zpower_pos 2 949 < 4758454107128906 * 10 ^ 270)%Z) by (vm_compute; reflexivity).
  apply IZR_lt in A. apply IZR_lt in B1. rewrite mult_IZR in A, B1.
  replace (/ 10 ^ 270) with (/ IZR (10 ^ 270)) by (rewrite pow_IZR; reflexivity).
  split.
  - apply frac_lt; assumption.
  - apply frac_gt; assumption.
Qed.

Lemma grid_949 h : fmtF h -> bpow radix2 (-897) <= h -> exists n : Z, h = IZR n * bpow radix2 (-949).
Proof.
  intros F Hh. destruct (FLT_format_generic radix2 (-1074) 53 h F) as [[m e] H1 H2 H3].
  simpl in H2, H3.
  assert (He : (-949 <= e)%Z).
  { destruct (Z_le_gt_dec (-949) e) as [A | A]; [exact A |].
    exfalso.
    assert (Hm : Rabs (IZR m) < bpow radix2 53).
    { rewrite <- abs_IZR. rewrite <- (IZR_Zpower radix2 53) by lia. apply IZR_lt. exact H2. }
    assert (Hh2 : Rabs h = Rabs (IZR m) * bpow radix2 e).
    { rewrite H1. unfold F2R. simpl. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)); [reflexivity | apply bpow_ge_0]. }
    assert (He2 : bpow radix2 e <= bpow radix2 (-950)) by (apply bpow_le; lia).
    pose proof (Rabs_pos (IZR m)) as Pm.
    assert (Hlt : Rabs (IZR m) * bpow radix2 e < bpow radix2 53 * bpow radix2 (-950)).
    { apply Rle_lt_trans with (Rabs (IZR m) * bpow radix2 (-950)).
      - apply Rmult_le_compat_l; [exact Pm | exact He2].
      - apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hm]. }
    rewrite <- bpow_plus in Hlt.
    assert (Hb : bpow radix2 (53 + -950) <= bpow radix2 (-897)) by (apply bpow_le; lia).
    rewrite <- Hh2 in Hlt. rewrite Rabs_pos_eq in Hlt; [lra |].
    eapply Rle_trans; [apply bpow_ge_0 | exact Hh]. }
  exists (m * Zpower radix2 (e + 949))%Z.
  rewrite H1. unfold F2R. cbn [Fnum Fexp]. rewrite mult_IZR.
  rewrite (IZR_Zpower radix2 (e + 949)) by lia.
  rewrite Rmult_assoc, <- bpow_plus. replace (e + 949 + -949)%Z with e by ring. reflexivity.
Qed.

Lemma floor_iff h : fmtF h -> (PFLOOR <= h <-> Bfloor <= h).
Proof.
  intros F. destruct floor_bounds as [Hl Hu]. split.
  - intros H.
    assert (Hb : bpow radix2 (-897) <= PFLOOR).
    { unfold PFLOOR. replace (-897)%Z with (- (897))%Z by reflexivity. rewrite bpow_opp.
      change (bpow radix2 897) with (IZR (Zpower_pos 2 897)).
      replace (/ 10 ^ 270) with (/ IZR (10 ^ 270)) by (rewrite pow_IZR; reflexivity).
      assert (A : (10 ^ 270 <= Zpower_pos 2 897)%Z) by (vm_compute; discriminate).
      apply IZR_le in A.
      apply Rinv_le_contravar; [apply IZR_lt; reflexivity | exact A]. }
    destruct (grid_949 h F ltac:(lra)) as [n Hn].
    assert (Hlt : IZR 4758454107128905 * bpow radix2 (-949) < IZR n * bpow radix2 (-949)) by (rewrite <- Hn; lra).
    apply Rmult_lt_reg_r in Hlt; [| apply bpow_gt_0].
    apply lt_IZR in Hlt.
    assert (Hge : (4758454107128906 <= n)%Z) by lia.
    apply IZR_le in Hge. rewrite Hn. unfold Bfloor. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hge].
  - intros H. lra.
Qed.

(** The product's error word, dropped below the floor. *)
Lemma floor_cond hi lo px py :
  exb hi (TwoProdBinary64.two_prod_p px py) 0 -> exb lo (TwoProdBinary64.two_prod_e px py) 4 ->
  exb (if fge hi kproduct_floor then lo else k0) (prod_lo px py) 4.
Proof.
  intros Hhi Hlo. unfold prod_lo.
  pose proof (floor_iff (TwoProdBinary64.two_prod_p px py) (fmtF_rnd (px * py))) as Hiff.
  pose proof (fge_iff hi kproduct_floor (exb_fin _ _ _ Hhi) (proj1 floor_exb)) as Hge.
  rewrite (exb_val _ _ _ floor_exb), (exb_val _ _ _ Hhi) in Hge.
  destruct (fge hi kproduct_floor) eqn:Ef; destruct (Rle_dec PFLOOR (TwoProdBinary64.two_prod_p px py)) as [Hf | Hf].
  - eapply exb_weak; [exact Hlo | lia].
  - exfalso. apply Hf. apply Hiff. apply Hge. reflexivity.
  - exfalso. pose proof (proj1 Hiff Hf) as Hb. pose proof (proj2 Hge Hb). discriminate.
  - eapply exb_weak; [exact exb_k0 | lia].
Qed.

(** The last stage: the kernel's [low_finish] is the proof's [finish]. *)
Lemma low_finish_ok pxf pyf highf lowf px py H Lw E :
  exb pxf px 0 -> exb pyf py 0 -> exb highf H E -> exb lowf Lw E -> (3 <= E <= 500)%Z ->
  exb (low_finish pxf pyf highf lowf) (finish px py H Lw) 0.
Proof.
  intros Hx Hy Hh Hl HE.
  pose proof (exb_two_prod pxf pyf px py 0 0 Hx Hy ltac:(lia) ltac:(lia) ltac:(lia)) as [Hhi Hlo].
  unfold low_finish, finish.
  revert Hhi Hlo. generalize (two_prod64 pxf pyf) as tp. intros [hi lo] Hhi Hlo. cbn [fst snd] in Hhi, Hlo |- *.
  assert (Hhi' : exb hi (TwoProdBinary64.two_prod_p px py) 0) by exact Hhi.
  assert (Hlo' : exb lo (TwoProdBinary64.two_prod_e px py) 4) by exact Hlo.
  pose proof (floor_cond hi lo px py Hhi' Hlo') as Hlo2.
  pose proof (exb_two_sum hi highf (TwoProdBinary64.two_prod_p px py) H E
    (exb_weak hi _ 0%Z E Hhi' ltac:(lia)) Hh ltac:(lia)) as [Hss Hse].
  revert Hss Hse. generalize (two_sum64 hi highf) as ts. intros [s e] Hss Hse. cbn [fst snd] in Hss, Hse |- *.
  unfold clampf. eapply exb_clamp. cbv zeta.
  lift.
Qed.

(** The nodes of a table against the proof's [NodeS] records: the stored
    abscissa and weight of each table row give the positive node, then its
    mirror, as the table lists them. [Kh] is the folded constant [rndF (asr / (2 TAU))],
    and a node's [nkw] is [rndF (nwh * Kh)] as in [node_enc] (BvnRule.v). *)
Definition stored_node (Kh : R) (xz wz : Z) (sgn : R) (n : NodeS) : Prop :=
  nsgn n = sgn /\ nxh n = B (aw xz) /\ nwh n = B (aw wz) /\ nkw n = rndF (nwh n * Kh).

Fixpoint nodes_match (Kh : R) (xw : list (Z * Z)) (nodes : list NodeS) : Prop :=
  match xw, nodes with
  | [], [] => True
  | (xz, wz) :: r, np :: nn :: rest =>
      stored_node Kh xz wz 1 np /\ stored_node Kh xz wz (-1) nn /\ nodes_match Kh r rest
  | _, _ => False
  end.

(** The magnitudes the proof's node lemmas establish ([node_full], BvnLow.v) and
    the kernel's operations need: abscissa and weight at most 1, the angle at most
    [3/2], its sine at most [99/100]. *)
Definition node_ranges (sinI : R -> R) (asr : R) (n : NodeS) : Prop :=
  Rabs (nxh n) <= 1 /\ Rabs (nwh n) <= 1 /\
  Rabs (angle asr (nsgn n) (nxh n)) <= 3 / 2 /\ Rabs (sinI (angle asr (nsgn n) (nxh n))) <= 99 / 100.

Section Table.
Variables (L : lib) (expI sinI : R -> R).
Hypotheses (Hexp : lib_exp_rel L expI 0 1) (Hsin : lib_sin_rel L sinI).
Variables (xf yf asrf k : f64) (x y asr Kh : R).
Hypotheses (Hx : exb xf x 6) (Hy : exb yf y 6) (Ha : exb asrf asr 1) (Hk : exb k Kh 1).

Lemma term_of_node sgnf sgn xz wz n :
  exb sgnf sgn 0 -> (sgn = 1 \/ sgn = -1) -> stored_node Kh xz wz sgn n ->
  finite (aw xz) -> finite (aw wz) -> node_ranges sinI asr n ->
  term_rel L (sq_diff xf yf) (sq_sum xf yf) 2 (node_entry L asrf k (aw wz) (aw xz) sgnf)
    (tn expI sinI x y asr n).
Proof.
  intros Hs Hsg [Hns [Hxh [Hwh Hkw]]] Fx Fw (Hr1 & Hr2 & Hr3 & Hr4).
  assert (Hxe : exb (aw xz) (nxh n) 0).
  { repeat split; [exact Fx | symmetry; exact Hxh | ]. change (bpow radix2 0) with 1. exact Hr1. }
  assert (Hwe : exb (aw wz) (nwh n) 0).
  { repeat split; [exact Fw | symmetry; exact Hwh | ]. change (bpow radix2 0) with 1. exact Hr2. }
  assert (Hke : exb (aw wz *f k) (nkw n) 1).
  { rewrite Hkw. eapply exb_weak; [eapply exb_mul; [exact Hwe | exact Hk | unfold cl; lia] | unfold cl; lia]. }
  assert (Hsn : exb sgnf (nsgn n) 0) by (rewrite Hns; exact Hs).
  unfold term_rel, node_entry. cbn [fst snd]. unfold tn.
  exact (low_node_ok L expI sinI Hexp Hsin xf yf asrf sgnf (aw xz) (aw wz *f k) x y asr (nsgn n) (nxh n) (nkw n) 1%Z
           Hx Hy Ha Hsn (eq_ind_r (fun v => v = 1 \/ v = -1) Hsg Hns) Hxe Hke ltac:(lia) Hr3 Hr4).
Qed.

Lemma terms_ok xw : forall nodes, nodes_match Kh xw nodes ->
  (forall xz wz, In (xz, wz) xw -> finite (aw xz) /\ finite (aw wz)) ->
  Forall (node_ranges sinI asr) nodes ->
  Forall2 (term_rel L (sq_diff xf yf) (sq_sum xf yf) 2)
    (low_pairs L asrf k xw) (map (tn expI sinI x y asr) nodes).
Proof.
  induction xw as [| [xz wz] r IH]; intros nodes Hm Hfin Hr.
  - destruct nodes; [| destruct Hm]. constructor.
  - destruct nodes as [| np [| nn rest]]; try (destruct Hm; fail).
    destruct Hm as [Hp [Hn Hrest]].
    inversion Hr as [| ? ? Hrp Hr1]; subst. inversion Hr1 as [| ? ? Hrn Hr2]; subst.
    destruct (Hfin xz wz (or_introl eq_refl)) as [Fx Fw].
    pose proof (IH rest Hrest ltac:(intros a b Hin; apply Hfin; right; exact Hin) Hr2) as IHr.
    unfold low_pairs in IH |- *. cbn [flat_map fst snd map].
    apply Forall2_cons; [| apply Forall2_cons; [| exact IHr]].
    + exact (term_of_node k1 1 xz wz np exb_k1 (or_introl eq_refl) Hp Fx Fw Hrp).
    + exact (term_of_node kneg1 (-1) xz wz nn exb_kneg1 (or_intror eq_refl) Hn Fx Fw Hrn).
Qed.
End Table.

Lemma Forall2_len {A B : Type} (P : A -> B -> Prop) l1 l2 : Forall2 P l1 l2 -> length l1 = length l2.
Proof. intros H. induction H; simpl; auto. Qed.

(** [2 * TAU] is exact. *)
Lemma two_tau_exb : exb (k2 *f ktau) (2 * TAU) 4.
Proof.
  pose proof (exb_mul k2 ktau 2 (884279719003555 / 140737488355328) 1 3 exb_k2 exb_ktau ltac:(unfold cl; lia)) as H.
  assert (Ft : fmtF (884279719003555 / 140737488355328)).
  { pose proof (B_fmt ktau) as F. rewrite (proj1 (proj2 exb_ktau)) in F. exact F. }
  pose proof (fmtF_double _ Ft) as F2.
  assert (E : rndF (2 * (884279719003555 / 140737488355328)) = 2 * TAU).
  { unfold TAU. apply round_generic; [exact _ | exact F2]. }
  eapply exb_cong; [eapply exb_weak; [exact H | unfold cl; lia] | exact E].
Qed.

(** The whole low branch: the kernel's [kernel_low], on a table whose nodes are
    those [nodes_match] relates to the proof's [NodeS] records, is the proof's
    [Rhat], with the distribution functions' results as [pxI] and [pyI]. *)
Theorem kernel_low_ok (L : lib) (expI sinI ncI : R -> R)
  (Hexp : lib_exp_rel L expI 0 1) (Hsin : lib_sin_rel L sinI) (Hnc : lib_ncdf_rel L ncI)
  (t : table) (xf yf : f64) (x y asr Kh : R) (xs ws : list Z) (nodes : list NodeS) :
  t_nodes t = low_nodes L (t_asr t) (t_asr t /f (k2 *f ktau)) xs ws ->
  exb (t_asr t) asr 1 -> Kh = rndF (asr / (2 * TAU)) ->
  nodes_match Kh (combine xs ws) nodes ->
  (forall xz wz, In (xz, wz) (combine xs ws) -> finite (aw xz) /\ finite (aw wz)) ->
  Forall (node_ranges sinI asr) nodes -> (length nodes <= 24)%nat ->
  exb xf x 6 -> exb yf y 6 ->
  exb (kernel_low L t xf yf) (Rhat expI sinI x y asr nodes (ncI x) (ncI y)) 0.
Proof.
  intros Ht Ha HKh Hm Hfin Hr Hlen Hx Hy.
  set (k := t_asr t /f (k2 *f ktau)).
  assert (Hk : exb k Kh 1).
  { rewrite HKh. unfold k. eapply exb_weak.
    - eapply exb_div_one; [exact Ha | exact two_tau_exb | unfold cl; lia | | unfold cl; lia].
      rewrite Rabs_pos_eq by (unfold TAU; lra). unfold TAU. lra.
    - unfold cl; lia. }
  pose proof (terms_ok L expI sinI Hexp Hsin xf yf (t_asr t) k x y asr Kh Hx Hy Ha Hk (combine xs ws) nodes Hm Hfin Hr) as Hterms.
  assert (Hlens : length (low_pairs L (t_asr t) k (combine xs ws)) = length nodes).
  { apply Forall2_len in Hterms. rewrite map_length in Hterms. exact Hterms. }
  pose proof (low_sum_ok L (sq_diff xf yf) (sq_sum xf yf) 2 (low_pairs L (t_asr t) k (combine xs ws))
    (map (tn expI sinI x y asr) nodes) Hterms k0 k0 0 0 2 ltac:(eapply exb_weak; [exact exb_k0' | lia]) ltac:(eapply exb_weak; [exact exb_k0' | lia]) ltac:(lia) ltac:(lia)
    ltac:(rewrite Hlens; assert (Z.of_nat (length nodes) <= 24)%Z by lia; lia)) as [Hhigh Hlow].
  rewrite Hlens in Hhigh, Hlow.
  unfold kernel_low. rewrite Ht. fold k. change (low_nodes L (t_asr t) k xs ws) with (low_pairs L (t_asr t) k (combine xs ws)).
  revert Hhigh Hlow. generalize (low_sum L (sq_diff xf yf) (sq_sum xf yf) (low_pairs L (t_asr t) k (combine xs ws)) k0 k0) as ls.
  intros [h l] Hhigh Hlow. cbn [fst snd] in Hhigh, Hlow |- *.
  unfold Rhat.
  eapply (low_finish_ok _ _ h l (ncI x) (ncI y) _ _ 122%Z).
  - eapply exb_lib_ncdf; [exact Hnc | exact Hx].
  - eapply exb_lib_ncdf; [exact Hnc | exact Hy].
  - eapply exb_weak; [exact Hhigh | assert (Z.of_nat (length nodes) <= 24)%Z by lia; lia].
  - eapply exb_weak; [exact Hlow | assert (Z.of_nat (length nodes) <= 24)%Z by lia; lia].
  - lia.
Qed.

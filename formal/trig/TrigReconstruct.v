(** Q256 reconstruction of the centered Payne-Hanek fraction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Q Require Import Limbs QSpec Q256 Q256Real.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import TrigConstants TrigWindow TrigWindowError TrigClosest TrigFraction TrigCentered.
Import ListNotations.
Open Scope R_scope.

Lemma trig_from_limbs_error n ms e0 : limbs_ok ms ->
  valid (Q256.from_limbs n ms e0) /\
  Rabs (qval (Q256.from_limbs n ms e0)-val n (v ms) e0) <=
    bpow radix2 (-255)*Rabs (val n (v ms) e0).
Proof.
  intro O. destruct (Q256.from_limbs_ok n ms e0 O) as [Ok [Zero Nonzero]].
  destruct (Z.eq_dec (v ms) 0) as [Z|Z].
  - assert (Out : (v (Q256.m (Q256.from_limbs n ms e0))=0)%Z) by (apply Zero; exact Z).
    split; [split; [exact Ok|left; exact Out]|].
    rewrite (qval_zero _ Out),Z,val_zero. rewrite Rminus_diag_eq,Rabs_R0 by reflexivity.
    nra.
  - destruct (Nonzero Z) as [N [Sign [Under Error]]].
    split; [split; [exact Ok|right; exact N]|].
    rewrite val_abs by (apply v_nonneg; exact O).
    unfold qval. rewrite Sign. unfold val.
    destruct n.
    + rewrite !F2R_Zopp.
      replace (-F2R (Float radix2 (v (Q256.m (Q256.from_limbs true ms e0)))
          (Q256.e (Q256.from_limbs true ms e0))) - -F2R (Float radix2 (v ms) e0))
        with (F2R (Float radix2 (v ms) e0)-
          F2R (Float radix2 (v (Q256.m (Q256.from_limbs true ms e0)))
            (Q256.e (Q256.from_limbs true ms e0)))) by ring.
      rewrite Rabs_pos_eq by lra. exact Error.
    + rewrite Rabs_left1 by lra. lra.
Qed.

Definition trig_half_pi_q := Q256.new false trig_half_pi_words trig_half_pi_exponent.
Lemma trig_half_pi_ok : ok4 trig_half_pi_words.
Proof.
  split; [|reflexivity]. unfold trig_half_pi_words.
  repeat (apply Forall_cons; [unfold Limbs.B; lia|]); apply Forall_nil.
Qed.
Lemma trig_half_pi_q_valid : valid trig_half_pi_q.
Proof. apply new_valid,trig_half_pi_ok. Qed.
Lemma trig_half_pi_q_value : qval trig_half_pi_q=IZR trig_half_pi_mantissa/2^255.
Proof.
  unfold trig_half_pi_q. rewrite Q256.new_val by exact trig_half_pi_ok.
  unfold val,F2R; cbn [Fnum Fexp].
  change (v trig_half_pi_words) with trig_half_pi_mantissa.
  assert (P : bpow radix2 trig_half_pi_exponent=/(2:R)^255).
  { rewrite pow_IZR; reflexivity. }
  rewrite P; reflexivity.
Qed.
Theorem trig_half_pi_q_error :
  Rabs (qval trig_half_pi_q-PI/2)< /2^255*(PI/2).
Proof. rewrite trig_half_pi_q_value. exact trig_half_pi_relative. Qed.

Lemma trig_relative_trans a b c e1 e2 : 0<=e1 -> 0<=e2 ->
  Rabs(a-b)<=e1*Rabs b -> Rabs(b-c)<=e2*Rabs c ->
  Rabs(a-c)<=(e1+e2+e1*e2)*Rabs c.
Proof.
  intros E1 E2 A B.
  assert (Bsize : Rabs b<=(1+e2)*Rabs c).
  { replace b with ((b-c)+c) at 1 by ring. eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (Asize : e1*Rabs b<=e1*((1+e2)*Rabs c)).
  { apply Rmult_le_compat_l; assumption. }
  replace (a-c) with ((a-b)+(b-c)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. nra.
Qed.

Lemma trig_relative_mul a b x y ea eb : 0<=ea -> 0<=eb ->
  Rabs(a-x)<=ea*Rabs x -> Rabs(b-y)<=eb*Rabs y ->
  Rabs(a*b-x*y)<=(ea+eb+ea*eb)*Rabs(x*y).
Proof.
  intros Ea Eb A B.
  assert (Bsize : Rabs b<=(1+eb)*Rabs y).
  { replace b with ((b-y)+y) at 1 by ring. eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (P : Rabs(a-x)*Rabs b<=(ea*Rabs x)*((1+eb)*Rabs y)).
  { apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Q : Rabs x*Rabs(b-y)<=Rabs x*(eb*Rabs y)).
  { apply Rmult_le_compat_l; [apply Rabs_pos|exact B]. }
  replace (a*b-x*y) with ((a-x)*b+x*(b-y)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite !Rabs_mult in *; nra.
Qed.

Definition trig_q_fraction (e m : Z) :=
  let p:=trig_product e m in
  Q256.from_limbs (trig_negative (trig_fraction p)) (snd (trig_select p)) (-trig_fraction_bits).
Definition trig_q_remainder e m := Q256.mul (trig_q_fraction e m) trig_half_pi_q.

Theorem trig_q_fraction_error e m : (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  valid (trig_q_fraction e m) /\
  Rabs(qval (trig_q_fraction e m)-(trig_prefix_value e m-IZR (trig_full_integer e m))) <=
    /2^255*Rabs(trig_prefix_value e m-IZR (trig_full_integer e m)).
Proof.
  intros E M. destruct (trig_product_exact e m E ltac:(lia)) as [O [L _]].
  destruct (trig_select_exact _ O L) as [_ [Ok _]].
  pose proof (trig_from_limbs_error (trig_negative (trig_fraction (trig_product e m)))
    (snd (trig_select (trig_product e m))) (-315) Ok) as F.
  rewrite trig_centered_input in F by assumption.
  assert (Pow : bpow radix2 (-255)=/(2:R)^255) by (rewrite pow_IZR; reflexivity).
  rewrite Pow in F. exact F.
Qed.

Theorem trig_reconstruction_error e m : (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  valid (trig_q_remainder e m) /\
  Rabs(qval (trig_q_remainder e m)-
    (trig_prefix_value e m-IZR (trig_full_integer e m))*(PI/2)) <=
    /2^252*Rabs((trig_prefix_value e m-IZR (trig_full_integer e m))*(PI/2)).
Proof.
  intros E M. destruct (trig_q_fraction_error e m E M) as [F Error].
  destruct (mul_any _ _ F trig_half_pi_q_valid) as [V Multiply].
  split; [exact V|].
  assert (Pow : bpow radix2 (-255)=/(2:R)^255) by (rewrite pow_IZR; reflexivity).
  rewrite Pow in Multiply.
  assert (U : 0<=/(2:R)^255<=/4) by (split; interval).
  assert (H : Rabs(qval trig_half_pi_q-PI/2)<=/2^255*Rabs(PI/2)).
  { rewrite (Rabs_pos_eq (PI/2)) by interval. left; exact trig_half_pi_q_error. }
  pose proof (trig_relative_mul _ _ _ _ _ _ (proj1 U) (proj1 U) Error H) as Product.
  assert (Ppos : 0<=/2^255+/2^255+(/2^255)*(/2^255)) by interval.
  pose proof (trig_relative_trans _ _ _ _ _ (proj1 U) Ppos Multiply Product) as Total.
  apply Rle_trans with (1:=Total). apply Rmult_le_compat_r; [apply Rabs_pos|].
  interval.
Qed.

Theorem trig_remainder_error x e m :
  finite x -> PI/4<=B x -> (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  B x=IZR m*bpow radix2 e ->
  Rabs(qval (trig_q_remainder e m)-(B x-IZR (trig_full_integer e m)*(PI/2))) <=
    /2^199*Rabs(B x-IZR (trig_full_integer e m)*(PI/2)).
Proof.
  intros F X E M V.
  pose proof (trig_prefix_relative x e m (trig_full_integer e m) F X E M V) as Prefix.
  destruct (trig_reconstruction_error e m E M) as [_ Reconstruct].
  assert (Pi : 0<PI) by interval.
  assert (Exact : B x-IZR (trig_full_integer e m)*(PI/2)=
    (B x*(2/PI)-IZR (trig_full_integer e m))*(PI/2)) by (field; lra).
  assert (Trunc : Rabs((trig_prefix_value e m-IZR (trig_full_integer e m))*(PI/2)-
      (B x-IZR (trig_full_integer e m)*(PI/2))) <=
      /2^200*Rabs(B x-IZR (trig_full_integer e m)*(PI/2))).
  { rewrite Exact.
    replace ((trig_prefix_value e m-IZR (trig_full_integer e m))*(PI/2)-
      (B x*(2/PI)-IZR (trig_full_integer e m))*(PI/2))
      with ((trig_prefix_value e m-B x*(2/PI))*(PI/2)) by ring.
    rewrite !Rabs_mult. rewrite Rabs_minus_sym in Prefix.
    replace (/2^200*(Rabs(B x*(2/PI)-IZR (trig_full_integer e m))*Rabs(PI/2)))
      with ((/2^200*Rabs(B x*(2/PI)-IZR (trig_full_integer e m)))*Rabs(PI/2)) by ring.
    apply Rmult_le_compat_r; [apply Rabs_pos|left; exact Prefix]. }
  assert (U : 0<=/(2:R)^252) by interval.
  assert (T : 0<=/(2:R)^200) by interval.
  pose proof (trig_relative_trans _ _ _ _ _ U T Reconstruct Trunc) as Total.
  apply Rle_trans with (1:=Total). apply Rmult_le_compat_r; [apply Rabs_pos|]. interval.
Qed.

Theorem trig_remainder_range x e m :
  finite x -> PI/4<=B x -> (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  B x=IZR m*bpow radix2 e -> Rabs(qval (trig_q_remainder e m))<=PI/4.
Proof.
  intros F X E M V.
  pose proof (trig_centered_nearest x e m F X E M V) as Nearest.
  pose proof (trig_remainder_error x e m F X E M V) as Error.
  pose proof (trig_binary64_half_separation x (trig_full_integer e m) F X) as Above.
  pose proof (trig_binary64_half_separation x (trig_full_integer e m-1)%Z F X) as Below.
  rewrite minus_IZR in Below.
  rewrite Rabs_left1 in Above by lra. rewrite Rabs_pos_eq in Below by lra.
  assert (Centered : Rabs(B x*(2/PI)-IZR (trig_full_integer e m))<=/2-/2^63).
  { apply Rabs_le; split; lra. }
  assert (Pi : 0<PI) by interval.
  assert (Exact : B x-IZR (trig_full_integer e m)*(PI/2)=
    (B x*(2/PI)-IZR (trig_full_integer e m))*(PI/2)) by (field; lra).
  assert (Rbound : Rabs(B x-IZR (trig_full_integer e m)*(PI/2))<=(/2-/2^63)*(PI/2)).
  { rewrite Exact,Rabs_mult,(Rabs_pos_eq (PI/2)) by lra.
    apply Rmult_le_compat_r; lra. }
  assert (U : 0<=1+/(2:R)^199) by interval.
  apply Rle_trans with ((1+/2^199)*Rabs(B x-IZR (trig_full_integer e m)*(PI/2))).
  - replace (qval (trig_q_remainder e m)) with
      ((qval (trig_q_remainder e m)-(B x-IZR (trig_full_integer e m)*(PI/2)))+
       (B x-IZR (trig_full_integer e m)*(PI/2))) at 1 by ring.
    eapply Rle_trans; [apply Rabs_triang|]. nra.
  - apply Rle_trans with ((1+/2^199)*((/2-/2^63)*(PI/2))).
    + apply Rmult_le_compat_l; assumption.
    + replace ((1+/2^199)*((/2-/2^63)*(PI/2))) with
        (((1+/2^199)*(/2-/2^63))*(PI/2)) by ring.
      replace (PI/4) with ((/2)*(PI/2)) by field.
      apply Rmult_le_compat_r; [lra|]. interval with (i_prec 100).
Qed.

Theorem trig_remainder_nonzero x e m :
  finite x -> PI/4<=B x -> (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  B x=IZR m*bpow radix2 e -> qval (trig_q_remainder e m)<>0.
Proof.
  intros F X E M V Zero.
  pose proof (trig_binary64_separation x (trig_full_integer e m) F X) as Gap.
  pose proof (trig_remainder_error x e m F X E M V) as Error.
  assert (Pi : 0<PI) by interval.
  assert (Exact : B x-IZR (trig_full_integer e m)*(PI/2)=
    (B x*(2/PI)-IZR (trig_full_integer e m))*(PI/2)) by (field; lra).
  assert (Positive : 0<Rabs(B x-IZR (trig_full_integer e m)*(PI/2))).
  { rewrite Exact,Rabs_mult. apply Rmult_lt_0_compat.
    - assert (G : 0</(2:R)^62) by interval. lra.
    - rewrite Rabs_pos_eq by lra; lra. }
  rewrite Zero,Rminus_0_l,Rabs_Ropp in Error.
  assert (Small : /(2:R)^199<1) by interval. nra.
Qed.

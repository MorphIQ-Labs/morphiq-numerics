(** Binary64 decoding and the complete large-argument reduction contract. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require Import Limbs Q128Mul Q256 Q256Real.
From Binary64 Require Import IEEE64 Encodings.
From Interval Require Import Tactic.
Require Import TrigConstants TrigWindow TrigWindowError TrigClosest TrigFraction TrigCentered TrigReconstruct.
Open Scope R_scope.

Theorem trig_decode x : finite x -> PI/4<=B x ->
  exists m e, (0<m<2^53)%Z /\ (-53<=e<=971)%Z /\
    B x=IZR m*bpow radix2 e /\
    Z.lor (Z.land (bits_of_b64 x) (2^52-1)) (Z.shiftl 1 52)=m /\
    (Z.shiftr (bits_of_b64 x) 52-1075)%Z=e.
Proof.
  intros F X. assert (Half : /2<PI/4) by interval.
  assert (Normal : bpow radix2 (-1022)<=B x).
  { apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia|]. change (/2<=B x); lra. }
  destruct (pos_normal x F Normal) as [m [e [Hx [_ [M [E [V [_ [_ Bits]]]]]]]]].
  assert (Low : (-53<=e)%Z).
  { destruct (Z_le_gt_dec (-53) e); [assumption|].
    assert (Small : B x<bpow radix2 (e+53)).
    { rewrite V,bpow_plus,Rmult_comm. apply Rmult_lt_compat_l; [apply bpow_gt_0|].
      change (IZR (Zpos m)<IZR (2^53)). apply IZR_lt; lia. }
    assert (Upper : bpow radix2 (e+53)<=/2).
    { change (bpow radix2 (e+53)<=bpow radix2 (-1)). apply bpow_le; lia. }
    exfalso; lra. }
  exists (Zpos m),e. split; [lia|]. split; [lia|]. split; [exact V|].
  rewrite Bits,join_eq. split.
  - change (2^52-1)%Z with (Z.ones 52). rewrite Z.land_ones by lia.
    rewrite Z.add_comm,Z.mod_add by lia. rewrite Z.mod_small by lia.
    rewrite lor_disjoint_low by lia. lia.
  - rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia; lia.
Qed.

Theorem trig_reduce_large_correct x : finite x -> PI/4<=B x ->
  exists n q, trig_reduce_large (bits_of_b64 x)=((n mod 4)%Z,q) /\
    valid q /\ Rabs(qval q)<=PI/4 /\ -/2<B x*(2/PI)-IZR n</2 /\
    Rabs(qval q-(B x-IZR n*(PI/2))) <= /2^199*Rabs(B x-IZR n*(PI/2)).
Proof.
  intros F X. destruct (trig_decode x F X) as [m [e [M [E [V [Sig Exp]]]]]].
  exists (trig_full_integer e m),(trig_q_remainder e m).
  rewrite trig_reduce_large_parts,Sig,Exp.
  pose proof (trig_centered_exact e m E M) as [_ [K _]].
  destruct (trig_select (trig_product e m)) as [k mag] eqn:Select.
  cbn [fst] in K. split.
  - unfold trig_q_remainder,trig_q_fraction,trig_half_pi_q. rewrite Select. cbn [snd].
    rewrite K; reflexivity.
  - split; [exact (proj1 (trig_reconstruction_error e m E M))|].
    split; [exact (trig_remainder_range x e m F X E M V)|].
    split.
    + exact (trig_centered_nearest x e m F X E M V).
    + exact (trig_remainder_error x e m F X E M V).
Qed.

Definition trig_quarter := b64_of_bits 4605249457297304856.
Definition trig_quarter_next := b64_of_bits 4605249457297304857.
Lemma trig_quarter_finite : finite trig_quarter.
Proof. vm_compute; reflexivity. Qed.
Lemma trig_quarter_value : B trig_quarter=7074237752028440/2^53.
Proof. rewrite pow_IZR; reflexivity. Qed.
Lemma trig_quarter_next_value : B trig_quarter_next=7074237752028441/2^53.
Proof. rewrite pow_IZR; reflexivity. Qed.
Theorem trig_quarter_bounds : B trig_quarter<PI/4<B trig_quarter_next.
Proof. rewrite trig_quarter_value,trig_quarter_next_value. split; interval with (i_prec 100). Qed.

Lemma trig_above_quarter x : B trig_quarter<B x -> PI/4<=B x.
Proof.
  intro X. assert (Range : bpow radix2 (-1022)<=B trig_quarter<bpow radix2 1023).
  { rewrite trig_quarter_value. split.
    - apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia|]. change (/2<=7074237752028440/2^53); interval.
    - apply Rlt_le_trans with (bpow radix2 0); [change (7074237752028440/2^53<1); interval|]. apply bpow_le; lia. }
  destruct (bits_up trig_quarter trig_quarter_finite Range) as [_ Up].
  assert (Bits : bits_of_b64 trig_quarter=4605249457297304856%Z) by (vm_compute; reflexivity).
  rewrite Bits in Up. change (B trig_quarter_next=succ radix2 (FLT_exp (-1074) 53) (B trig_quarter)) in Up.
  pose proof (proj2 trig_quarter_bounds) as Pi.
  apply Rle_trans with (B trig_quarter_next); [lra|]. rewrite Up.
  apply succ_le_lt; try apply B_fmt; try exact X.
  exact (@FLT_exp_valid (-1074) 53 ltac:(unfold Prec_gt_0; lia)).
Qed.

Lemma trig_finite_exponent (x : f64) : finite x ->
  ((bits_of_b64 x/2^52) mod 2^11<>2047)%Z.
Proof.
  intro F. pose proof (split_bits_of_binary_float_correct 52 11 eq_refl eq_refl x) as S.
  unfold split_bits in S. change (bits_of_binary_float 52 11 x) with (bits_of_b64 x) in S.
  destruct x as [s|s|s pl Hpl|s mx ex Hb]; try discriminate F.
  - clear S. destruct s; vm_compute; discriminate.
  - pose proof Hb as Hb'. unfold bounded in Hb'. apply andb_prop in Hb'. destruct Hb' as [_ Hb'].
    apply Zle_bool_imp_le in Hb'. apply (f_equal snd) in S.
    unfold split_bits_of_binary_float in S; cbv beta zeta in S.
    destruct (0<=?Z.pos mx-2^52)%Z; cbv beta iota delta [snd] in S; rewrite S.
    all: cbn in Hb' |- *; lia.
Qed.
Lemma trig_from_binary64 x : finite x ->
  qval (Q256.from_f64 (bits_of_b64 x))=B x.
Proof.
  intro F. rewrite Q256.from_f64_ok.
  - unfold b64_of_bits,bits_of_b64. f_equal. apply binary_float_of_bits_of_binary_float.
  - exact (bits_of_binary_float_range 52 11 eq_refl eq_refl x).
  - exact (trig_finite_exponent x F).
Qed.

Lemma trig_small_correct x : finite x -> 0<=B x<=B trig_quarter ->
  valid (Q256.from_f64 (bits_of_b64 x)) /\
  Rabs(qval (Q256.from_f64 (bits_of_b64 x)))<=PI/4 /\
  -/2<B x*(2/PI)</2 /\
  Rabs(qval (Q256.from_f64 (bits_of_b64 x))-B x)<=/2^199*Rabs(B x).
Proof.
  intros F X. split; [apply from_f64_valid|].
  pose proof (proj1 trig_quarter_bounds) as Q.
  split.
  { rewrite trig_from_binary64 by exact F. rewrite Rabs_pos_eq by lra; lra. }
  assert (Pi : 0<PI) by interval.
  assert (Inv : 0<2/PI) by (unfold Rdiv; apply Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; exact Pi]).
  assert (Half : (PI/4)*(2/PI)=/2) by (field; lra).
  split.
  - split; [nra|]. rewrite <-Half. apply Rmult_lt_compat_r; lra.
  - rewrite trig_from_binary64 by exact F. rewrite Rminus_diag_eq,Rabs_R0 by reflexivity.
    apply Rmult_le_pos; [left; interval|apply Rabs_pos].
Qed.

Theorem trig_reduce_correct x : finite x -> 0<=B x ->
  exists n q, trig_reduce64 (bits_of_b64 x)=((n mod 4)%Z,q) /\
    valid q /\ Rabs(qval q)<=PI/4 /\ -/2<B x*(2/PI)-IZR n</2 /\
    Rabs(qval q-(B x-IZR n*(PI/2))) <= /2^199*Rabs(B x-IZR n*(PI/2)).
Proof.
  intros F X. unfold trig_reduce64.
  assert (Round : b64_of_bits (bits_of_b64 x)=x).
  { apply (binary_float_of_bits_of_binary_float 52 11). }
  rewrite Round. change (b64_of_bits 4605249457297304856) with trig_quarter.
  rewrite Bcompare_correct by (exact F || exact trig_quarter_finite).
  destruct (Rcompare_spec (B x) (B trig_quarter)) as [Eq|Lt|Gt].
  - exists 0%Z,(Q256.from_f64 (bits_of_b64 x)). split; [reflexivity|].
    replace (B x-IZR 0*(PI/2)) with (B x) by ring.
    replace (B x*(2/PI)-IZR 0) with (B x*(2/PI)) by ring.
    apply trig_small_correct; [exact F|lra].
  - exists 0%Z,(Q256.from_f64 (bits_of_b64 x)). split; [reflexivity|].
    replace (B x-IZR 0*(PI/2)) with (B x) by ring.
    replace (B x*(2/PI)-IZR 0) with (B x*(2/PI)) by ring.
    apply trig_small_correct; [exact F|lra].
  - apply trig_reduce_large_correct; [exact F|apply trig_above_quarter; exact Gt].
Qed.

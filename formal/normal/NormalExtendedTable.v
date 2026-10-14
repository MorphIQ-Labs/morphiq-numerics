(** The complete extended-input table branch, including the rounded lookup,
    predecessor repair and the cap below 16. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Encodings.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxAccurateInputs ErfcxAccurateTerms
  ErfcxTableReduction ErfcxAccurateTaylorReduction NormalResidualGrid
  NormalErfcxTaylor NormalTableLookup NormalTablePredecessor NormalTableCap.
Open Scope R_scope.

Definition normal_q_eighth := mul_pow2 q_one (-3).
Lemma normal_q_eighth_ok : valid normal_q_eighth /\ qval normal_q_eighth=/8.
Proof.
  destruct q_one_ok as[Q Value];destruct(mul_pow2_any _ (-3) Q)as[Eighth E].
  split;[exact Eighth|unfold normal_q_eighth;rewrite E,Value;change(bpow radix2 (-3))with(/8);field].
Qed.
Lemma normal_q_eighth_encoding : normal_q_eighth=q_float(b64_of_bits 4593671619917905920).
Proof. vm_compute;reflexivity. Qed.

Definition normal_q_table_lookup x high :=
  let '(i,c,r,e):=table_reduce64 high in
  let h:=normal_q_erfcx_residual x c in
  match cmp_abs h normal_q_eighth with
  | Gt => let '(ip,cp,rp,ep):=table_reduce64(normal_previous64 high) in
      normal_q_erfcx_taylor_at x cp (Z.to_nat ip)
  | _ => normal_q_erfcx_taylor_at x c (Z.to_nat i)
  end.

Lemma normal_table_reduce_binade h : finite h -> 8<=B h -> table_reduce64 h=table_binade64 h.
Proof.
  intros F H;destruct ErfcxReciprocal.one_ok as[Fo Bo];unfold table_reduce64.
  rewrite(Bcompare_correct 53 1024 h ErfcxReciprocal.one F Fo),Bo.
  destruct(Rcompare_spec(B h)1);try lra;reflexivity.
Qed.

Theorem normal_q_table_lookup_ordinary_error x : valid x -> /4<=qval x<16 ->
  B(Q256.to_f64 x)<16 ->
  valid(normal_q_table_lookup x (Q256.to_f64 x)) /\
  Rabs(qval(normal_q_table_lookup x (Q256.to_f64 x))-gaussian_erfcx(qval x))<=bpow radix2 (-123).
Proof.
  intros X Range High.
  destruct(normal_table_input_round x X ltac:(split;lra))as[Fh [H [Rounded Difference]]].
  pose proof(accurate_table_reduce_ieee _ Fh ltac:(split;lra))as Reduction.
  unfold normal_q_table_lookup.
  destruct(table_reduce64(Q256.to_f64 x))as[[[i c]r]e]eqn:Reduce;cbv zeta in Reduction|-*.
  destruct Reduction as[I [Fc [_ [Center _]]]].
  destruct(q_float_ok c Fc)as[C _];destruct(neg_any _ C)as[NC _].
  destruct(add_any _ _ X NC)as[Residual _].
  destruct normal_q_eighth_ok as[Eighth EighthValue].
  pose proof(normal_q_compare_abs (normal_q_erfcx_residual x c) normal_q_eighth Residual Eighth)as Compare.
  rewrite EighthValue,(Rabs_pos_eq(/8))in Compare by lra.
  assert (Ordinary : Rabs(qval(normal_q_erfcx_residual x c))<=/8 ->
    valid(normal_q_erfcx_taylor_at x c (Z.to_nat i)) /\
    Rabs(qval(normal_q_erfcx_taylor_at x c (Z.to_nat i))-gaussian_erfcx(qval x))<=bpow radix2 (-123)).
  { intros Radius;apply normal_q_erfcx_taylor_at_error;try assumption;[split;lra|lia]. }
  destruct(cmp_abs (normal_q_erfcx_residual x c) normal_q_eighth).
  - apply Ordinary;lra.
  - apply Ordinary;lra.
  - assert (Large : 8<=B(Q256.to_f64 x)).
    { destruct(Rle_dec 8 (B(Q256.to_f64 x)));[assumption|exfalso].
      assert (Near : Rabs(qval x-B(Q256.to_f64 x))<=bpow radix2 (-48)).
      { rewrite Rabs_minus_sym;eapply Rle_trans;[exact Difference|apply bpow_le;lia]. }
      pose proof(normal_extended_small_cell_radius x _ X ltac:(split;lra) Fh ltac:(split;lra) Near)as Small.
      rewrite Reduce in Small;cbv zeta in Small;destruct Small as[_ [_ [_ Radius]]];lra. }
    pose proof(normal_q_erfcx_previous_table_error x X Range ltac:(split;lra))as Previous.
    rewrite <-normal_table_reduce_binade in Previous by assumption;rewrite Reduce in Previous.
    exact(Previous Compare).
Qed.

Local Opaque normal_q_erfcx_taylor_at normal_q_erfcx_residual.

Theorem normal_q_table_lookup_cap_error x : valid x -> /4<=qval x<16 ->
  B(Q256.to_f64 x)=16 ->
  valid(normal_q_table_lookup x normal_table_cap) /\
  Rabs(qval(normal_q_table_lookup x normal_table_cap)-gaussian_erfcx(qval x))<=bpow radix2 (-123).
Proof.
  intros X Range Rounded.
  pose proof(normal_extended_cap_radius x X Range Rounded)as Radius.
  destruct normal_table_last_center_ok as[Fc _];destruct(q_float_ok _ Fc)as[C _].
  destruct(neg_any _ C)as[NC _];destruct(add_any _ _ X NC)as[Residual _].
  destruct normal_q_eighth_ok as[Eighth EighthValue].
  pose proof(normal_q_compare_abs (normal_q_erfcx_residual x normal_table_last_center)
    normal_q_eighth Residual Eighth)as Compare.
  rewrite EighthValue,(Rabs_pos_eq(/8))in Compare by lra.
  pose proof(normal_q_erfcx_capped_table_error x X Range Rounded)as Result.
  unfold normal_q_erfcx_capped_table in Result.
  unfold normal_q_table_lookup;rewrite normal_table_cap_reduction;cbv beta iota zeta.
  change(Z.to_nat 176)with 176%nat.
  destruct(cmp_abs (normal_q_erfcx_residual x normal_table_last_center) normal_q_eighth).
  - exact Result.
  - exact Result.
  - exfalso;lra.
Qed.

Definition normal_table_high x :=
  match Bcompare 53 1024 (Q256.to_f64 x) normal_table_cap with
  | Some Gt => normal_table_cap
  | _ => Q256.to_f64 x
  end.
Definition normal_q_erfcx_extended_table x := normal_q_table_lookup x (normal_table_high x).

Theorem normal_q_erfcx_extended_table_error x : valid x -> /4<=qval x<16 ->
  valid(normal_q_erfcx_extended_table x) /\
  Rabs(qval(normal_q_erfcx_extended_table x)-gaussian_erfcx(qval x))<=bpow radix2 (-123).
Proof.
  intros X Range;destruct(normal_table_input_round x X ltac:(split;lra))as[Fh [H _]].
  destruct normal_table_cap_ok as[Fc Cap].
  unfold normal_q_erfcx_extended_table,normal_table_high.
  rewrite(Bcompare_correct 53 1024 (Q256.to_f64 x) normal_table_cap Fh Fc).
  destruct(Rcompare_spec(B(Q256.to_f64 x))(B normal_table_cap))as[Low|Equal|Above].
  - apply normal_q_table_lookup_ordinary_error;try assumption.
    pose proof(bpow_gt_0 radix2 (-49));lra.
  - apply normal_q_table_lookup_ordinary_error;try assumption.
    pose proof(bpow_gt_0 radix2 (-49));lra.
  - apply normal_q_table_lookup_cap_error;try assumption.
    destruct(Rlt_dec(B(Q256.to_f64 x))16)as[Below|AtSixteen];[|lra].
    pose proof(normal_table_cap_max _ Fh Below);lra.
Qed.

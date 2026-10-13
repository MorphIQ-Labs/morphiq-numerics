(** Adjacent encodings on the constant binary64 underflow grid, including
    the first normal binade. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
Require Import StageGappa.
Open Scope R_scope.

Lemma small_bits_value n : (0 < n < 2^53)%Z ->
  finite (b64_of_bits n) /\ B (b64_of_bits n)=IZR n*bpow radix2 (-1074).
Proof.
  intros N. destruct (Z_lt_ge_dec n (2^52)) as [Sub | Normal].
  - replace n with (join_bits 52 11 false n 0) at 1 2
      by (rewrite join_eq; ring).
    unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, is_finite_FF2B.
    unfold binary_float_of_bits_aux.
    rewrite split_join_bits by (change (Zpower 2 52) with (2^52)%Z;
      change (Zpower 2 11) with 2048%Z; lia).
    destruct n as [ | p | p]; try lia. split; reflexivity.
  - replace n with (join_bits 52 11 false (n-2^52) 1) at 1 2
      by (rewrite join_eq; ring).
    destruct (join_val (n-2^52) 1 ltac:(lia) ltac:(lia)) as [F V].
    split; [exact F | rewrite V; f_equal; f_equal; lia].
Qed.

Lemma small_positive_encoding h : finite h -> 0<B h<bpow radix2 (-1021) ->
  (0<bits_of_b64 h<2^53)%Z /\ B h=IZR (bits_of_b64 h)*bpow radix2 (-1074).
Proof.
  intros F H. destruct h as [s | s | s pl Hpl | s m e He]; try discriminate.
  { cbn in H. lra. }
  destruct s.
  { exfalso. pose proof (F2R_lt_0 radix2 (Float radix2 (Zneg m) e) ltac:(simpl; lia)).
    change (0<F2R (Float radix2 (Zneg m) e)<bpow radix2 (-1021)) in H. lra. }
  pose proof He as Bound. unfold bounded in Bound. apply andb_prop in Bound as [Canonical _].
  pose proof (canonical_canonical_mantissa 53 1024 false m e Canonical) as C.
  assert (Mag : (mag radix2 (B (B754_finite 53 1024 false m e He)) <= -1021)%Z).
  { apply mag_le_bpow; [lra | rewrite Rabs_pos_eq; lra]. }
  assert (E : (e=(-1074))%Z).
  { unfold canonical in C. cbn [Fexp] in C.
    unfold cexp, FLT_exp in C. change (e=Z.max
      (mag radix2 (B (B754_finite 53 1024 false m e He))-53) (-1074))%Z in C. lia. }
  assert (M : (0<Zpos m<2^53)%Z).
  { split; [lia | apply lt_IZR].
    apply Rmult_lt_reg_r with (bpow radix2 (-1074)); [apply bpow_gt_0 | ].
    pose proof (proj2 H) as Upper.
    change (IZR (Zpos m)*bpow radix2 e < bpow radix2 (-1021)) in Upper.
    replace (IZR (2^53)*bpow radix2 (-1074)) with (bpow radix2 (-1021))
      by (change (IZR (2^53)) with (bpow radix2 53); rewrite <- bpow_plus; reflexivity).
    rewrite <- E. exact Upper. }
  assert (Bits : bits_of_b64 (B754_finite 53 1024 false m e He)=Zpos m).
  { unfold bits_of_b64, bits_of_binary_float.
    change (Zpower 2 52) with (2^52)%Z.
    destruct (Zle_bool 0 (Zpos m-2^52)) eqn:Branch.
    - rewrite join_eq. change (3-2^(11-1)-(52+1))%Z with (-1074)%Z. lia.
    - rewrite join_eq. ring. }
  rewrite Bits. split; [exact M | ]. change (IZR (Zpos m)*bpow radix2 e=IZR (Zpos m)*bpow radix2 (-1074)).
  rewrite E. reflexivity.
Qed.

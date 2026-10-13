(** Final binary64 conversion of the Taylor fallback. This is a proved
    error bound, not a whole-domain correct-rounding claim. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxRounding ErfcxAccurateInputs ErfcxAccurateTaylorEntry.
Open Scope R_scope.
Theorem q_taylor_rounded x : finite x -> -/2<=B x<16 ->
  finite(Q256.to_f64(q_taylor x)) /\ exists d a,
    Rabs d<=bpow radix2 (-53) /\ Rabs a<=bpow radix2 (-123)+bpow radix2 (-1075) /\
    B(Q256.to_f64(q_taylor x))=gaussian_erfcx(B x)*(1+d)+a.
Proof.
  intros Fx X. destruct(q_taylor_error x Fx X) as [Q Error].
  pose proof(table_target_bound x Fx X) as Target.
  destruct(rounding_decomposition(qval(q_taylor x))) as [d [a [D [A Round]]]].
  assert (Value : Rabs(qval(q_taylor x))<=1024).
  { replace (qval(q_taylor x)) with ((qval(q_taylor x)-gaussian_erfcx(B x))+gaussian_erfcx(B x)) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. bpow_num_all;lra. }
  assert (Factor : Rabs(1+d)<=2) by (bpow_num_all;apply Rabs_le;lra).
  assert (AbsA : Rabs a<=bpow radix2 (-1075)) by (apply Rabs_le;exact A).
  assert (RoundedRange : Rabs(rndF(qval(q_taylor x)))<=4096).
  { rewrite Round. eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult.
    pose proof(Rabs_pos(qval(q_taylor x)));pose proof(Rabs_pos(1+d)). bpow_num_all;nra. }
  assert (FiniteBound : Rabs(rndF(qval(q_taylor x)))<bpow radix2 1024).
  { eapply Rle_lt_trans;[exact RoundedRange|]. change 4096 with (bpow radix2 12). apply bpow_lt;lia. }
  destruct(q_to_float_round _ Q FiniteBound) as [Result Rounded].
  split;[exact Result|]. exists d,((qval(q_taylor x)-gaussian_erfcx(B x))*(1+d)+a).
  split;[apply Rabs_le;exact D|]. split.
  - eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult.
    assert (Product : Rabs(qval(q_taylor x)-gaussian_erfcx(B x))*Rabs(1+d)<=bpow radix2 (-123)).
    { eapply Rle_trans with (bpow radix2 (-124)*2).
      - apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Error|exact Factor].
      - bpow_num;lra. }
    lra.
  - rewrite Rounded,Round. ring.
Qed.

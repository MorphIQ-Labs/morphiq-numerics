(** Binary64/Q256 conversions and exact integer factors of the accurate tail.
    Reuse the existing finite-encoding and exact-integer conversion lemmas. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import QSpec QRound Q256 Q256Real LimbScan.
From Q Require Limbs.
Require ExpAccurate LnAccurate.
Open Scope R_scope.

Definition q_float x := Q256.from_f64 (bits_of_b64 x).

Theorem q_float_ok x : finite x -> valid (q_float x) /\ qval (q_float x)=B x.
Proof.
  intros F. split; [apply from_f64_valid | ]. unfold q_float.
  rewrite Q256.from_f64_ok.
  - unfold b64_of_bits,bits_of_b64. f_equal. apply binary_float_of_bits_of_binary_float.
  - exact (bits_of_binary_float_range 52 11 eq_refl eq_refl x).
  - exact (ExpAccurate.bits_exp_ok x F).
Qed.

Theorem q_to_float_round q : valid q -> Rabs (rndF (qval q))<bpow radix2 1024 ->
  finite (Q256.to_f64 q) /\ B (Q256.to_f64 q)=rndF (qval q).
Proof.
  intros [O N] Bound. destruct N as [Zero | Normal].
  - unfold Q256.to_f64. rewrite is_zero_ok by apply O. rewrite Zero. cbn [Z.eqb].
    rewrite (qval_zero q Zero),round_0 by exact _. split; reflexivity.
  - rewrite Q256.to_f64_ok by assumption. unfold QRound.bn.
    pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE
      (QRound.signed (Q256.neg q) (Limbs.v (m q))) (Q256.e q) (Q256.neg q)) as C.
    rewrite Rlt_bool_true in C by exact Bound.
    destruct C as [Value [Finite Sign]]. split; assumption.
Qed.

Theorem q_float_roundtrip x : finite x ->
  finite (Q256.to_f64 (q_float x)) /\ B (Q256.to_f64 (q_float x))=B x.
Proof.
  intros F. destruct (q_float_ok x F) as [Q Value].
  assert (Round : rndF (qval (q_float x))=B x).
  { rewrite Value. apply round_generic; [exact _ | apply B_fmt]. }
  pose proof (q_to_float_round _ Q ltac:(rewrite Round; apply abs_B2R_lt_emax)) as Result.
  rewrite Round in Result. exact Result.
Qed.

Definition q_odd k := q_float (LnAccurate.fe (Z.of_nat (2*k+1))).

Theorem q_odd_ok k : (k<400)%nat -> valid (q_odd k) /\ qval (q_odd k)=2*INR k+1.
Proof.
  intros K.
  destruct (LnAccurate.fe_ok (Z.of_nat (2*k+1)) ltac:(rewrite Z.abs_eq; lia)) as [F Value].
  unfold q_odd. destruct (q_float_ok _ F) as [Q V]. split; [exact Q | ].
  rewrite V,Value, <- INR_IZR_INZ, plus_INR,mult_INR.
  change (INR 2) with 2. change (INR 1) with 1. reflexivity.
Qed.

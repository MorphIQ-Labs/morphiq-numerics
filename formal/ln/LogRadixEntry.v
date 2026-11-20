(** Public radix logarithms: shared special-value screening, the proved
    rounding decision, and the accurate fallback. The log2 hard-case premise
    remains explicit; log10 has its stated final-result ULP bound. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest RoundingGaps.
From Interval Require Import Tactic.
Require Import Exp2 ExpAccurate ExpFast LnEntry LnFastTables LogRadixFast LogRadixDecision
  LogRadixRounding LogRadixUlp.
Open Scope R_scope.

Definition radix_special x : option f64 :=
  if is_nan 53 1024 x then Some x else
  if flt x c_zero then Some lf_nan else
  if lf_eq x c_zero then Some lf_neg_inf else
  if lf_infinite x then Some x else
  if lf_eq x c_one then Some c_zero else None.
Definition radix_entry (fast : f64 -> option f64) (accurate : f64 -> f64) x :=
  match radix_special x with Some y => y | None =>
    match fast x with Some y => y | None => accurate x end end.
Definition log2_entry := radix_entry log2_fast log2_accurate_result.
Definition log10_entry := radix_entry log10_fast log10_accurate_result.

Lemma radix_regular_screen x : finite x -> 0<B x -> B x<>1 -> radix_special x=None.
Proof.
  intros Fx Px Nx. destruct (lf_finite_screens x Fx) as [Nan Inf].
  assert (Neg : flt x c_zero=false) by
    (apply (proj2 (flt_false _ _ Fx c_zero_finite)); rewrite c_zero_val; lra).
  assert (Zero : lf_eq x c_zero=false) by
    (apply lf_not_eq; try assumption; [exact c_zero_finite | rewrite c_zero_val; lra]).
  assert (One : lf_eq x c_one=false) by
    (apply lf_not_eq; try assumption; [exact c_one_finite | rewrite c_one_val; intro Z; apply Nx; rewrite Z; field]).
  unfold radix_special; rewrite Nan,Neg,Zero,Inf,One; reflexivity.
Qed.

Theorem log2_entry_regular x : finite x -> 0<B x -> B x<>1 ->
  midpoint_far (Rabs(ln(B x)/ln 2)) (/2^109) ->
  finite (log2_entry x) /\ B (log2_entry x)=rndF(ln(B x)/ln 2).
Proof.
  intros Fx Px Nx Far. unfold log2_entry,radix_entry; rewrite radix_regular_screen by assumption.
  destruct (log2_fast x) as [r | ] eqn:D.
  - exact (log2_fast_correct x r Fx Px Nx D).
  - exact (log2_accurate_correct x Fx Px Nx Far).
Qed.

Theorem log10_entry_regular x : finite x -> 0<B x -> B x<>1 ->
  finite (log10_entry x) /\
  Rabs(B (log10_entry x)-ln(B x)/ln 10)<=
    (/2+/2^69)*ulp radix2 (FLT_exp emin prec) (ln(B x)/ln 10).
Proof.
  intros Fx Px Nx. unfold log10_entry,radix_entry; rewrite radix_regular_screen by assumption.
  destruct (log10_fast x) as [r | ] eqn:D.
  - destruct (log10_fast_correct x r Fx Px Nx D) as [Fr V]. split; [exact Fr | rewrite V].
    apply radix_round_error.
    + exact (proj1 (radix_log_range x 10 Fx Px Nx ltac:(split; interval))).
    + rewrite Rminus_diag_eq,Rabs_R0 by reflexivity.
      apply Rmult_le_pos; [interval | apply Rabs_pos].
  - exact (log10_accurate_ulp x Fx Px Nx).
Qed.

(** Exact representable logarithms, including integral powers of the radix,
    do not need a midpoint-distance premise. *)
Theorem log2_entry_representable x : finite x -> 0<B x -> B x<>1 ->
  fmtF(ln(B x)/ln 2) -> finite (log2_entry x) /\ B (log2_entry x)=ln(B x)/ln 2.
Proof.
  intros Fx Px Nx F. unfold log2_entry,radix_entry; rewrite radix_regular_screen by assumption.
  destruct (log2_fast x) as [r | ] eqn:D.
  - destruct (log2_fast_correct x r Fx Px Nx D) as [Fr V].
    split; [exact Fr | rewrite V; apply round_generic; [exact _ | exact F]].
  - exact (log2_accurate_representable x Fx Px Nx F).
Qed.

Theorem log10_entry_representable x : finite x -> 0<B x -> B x<>1 ->
  fmtF(ln(B x)/ln 10) -> finite (log10_entry x) /\ B (log10_entry x)=ln(B x)/ln 10.
Proof.
  intros Fx Px Nx F. unfold log10_entry,radix_entry; rewrite radix_regular_screen by assumption.
  destruct (log10_fast x) as [r | ] eqn:D.
  - destruct (log10_fast_correct x r Fx Px Nx D) as [Fr V].
    split; [exact Fr | rewrite V; apply round_generic; [exact _ | exact F]].
  - exact (log10_accurate_representable x Fx Px Nx F).
Qed.

Theorem radix_entry_specials fast accurate :
  radix_entry fast accurate (b64_of_bits 0)=lf_neg_inf /\
  radix_entry fast accurate (b64_of_bits 9223372036854775808)=lf_neg_inf /\
  radix_entry fast accurate (b64_of_bits 4607182418800017408)=c_zero /\
  radix_entry fast accurate (b64_of_bits 9218868437227405312)=b64_of_bits 9218868437227405312 /\
  radix_entry fast accurate (b64_of_bits 18442240474082181120)=lf_nan.
Proof. unfold radix_entry,radix_special; vm_compute; repeat split; reflexivity. Qed.

Theorem radix_entry_nan fast accurate x : is_nan 53 1024 x=true -> radix_entry fast accurate x=x.
Proof. intros N; unfold radix_entry,radix_special; rewrite N; reflexivity. Qed.

Theorem radix_entry_negative fast accurate x : finite x -> B x<0 -> radix_entry fast accurate x=lf_nan.
Proof.
  intros Fx X. destruct (lf_finite_screens x Fx) as [Nan _].
  assert (N : flt x c_zero=true) by
    (apply (proj2 (flt_true _ _ Fx c_zero_finite)); rewrite c_zero_val; exact X).
  unfold radix_entry,radix_special; rewrite Nan,N; reflexivity.
Qed.

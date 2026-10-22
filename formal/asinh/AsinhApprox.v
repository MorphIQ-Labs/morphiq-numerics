(** The series branch of asinh approximates [arcsinh]: with the table POLY0's
    coefficients, [arcsinh z] is [z + z^3 P(z^2)] to [3/16 2^-54 z^3] on
    [[2^-28, 0.0078126]] (the relative accuracy of Sollya's fit and the series'
    truncation, which [series_compose.g] budgets as [2^-54 (1 + 2^-23)] of
    [z - arcsinh z >= 0.99 z^3/6]). Proved by [sinh] monotonicity
    ([asinh_within]), the bounds on [sinh] at the polynomial's two ends by
    [interval]; Sollya's report is not an input. *)
From Coq Require Import Reals ZArith Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinhWithin.
Open Scope R_scope.

(** The polynomial's coefficients, as the kernel's table holds them. *)
Definition c0r : R := - (IZR 6004799503160661 * bpow radix2 (-55)).
Definition c1r : R := IZR 1351079888189287 * bpow radix2 (-54).
Definition c2r : R := - (IZR 3216854006803669 * bpow radix2 (-56)).
Definition c3r : R := IZR 8649021371757797 * bpow radix2 (-58).

Lemma approx_series z : / 268435456 <= z <= 0.0078126 ->
  Rabs (arcsinh z - (z + z * z * z * (c0r + z * z * (c1r + z * z * (c2r + z * z * c3r)))))
    <= 3 / 16 / 18014398509481984 * (z * z * z).
Proof.
  intros Hz. unfold c0r, c1r, c2r, c3r. bpow_num.
  apply asinh_within.
  all: interval with (i_bisect z, i_taylor z, i_prec 240, i_degree 14, i_depth 60).
Qed.

(** End-to-end regular scalar dispatch: an accepted first-stage or fast
    interval or the Q256 fallback, with a common bound on the exact
    normal-family target. *)
From Coq Require Import Reals.
From Coq Require Import ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add RoundingTest.
Require Import NormalComparisons NormalFastDispatch NormalDensityFirst NormalPublicModel NormalPublicBounds
  NormalPublicAccurate NormalPublicDomain NormalAccurateDensity.
Open Scope R_scope.
Local Opaque normal_fast_dispatch64 normal_accurate64 normal_special64 normal_density_first64.

Theorem normal_regular_bounded op x : finite x -> normal_special64 op x=None ->
  normal_bounded(normal_target op (B x))(normal_regular64 op x).
Proof.
  intros Fx Screen;destruct(normal_regular_domain op x Fx Screen)as[Domain Pdf].
  unfold normal_regular64;destruct(normal_first64 op x)as[y|]eqn:First.
  { unfold normal_first64 in First;destruct op;try discriminate.
    assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
    destruct normal_thirty_seven_ok as [F37 B37].
    destruct(normal_lt normal_thirty_seven (b64_abs x))eqn:Above;[discriminate|].
    apply normal_lt_false in Above;[|exact F37|exact Fa].
    rewrite B_abs,B37 in Above.
    destruct(normal_density_first_ok x y Fx ltac:(split;[exact(Pdf eq_refl)|exact Above])First)as[F Rounded].
    apply normal_exact_bounded;assumption. }
  destruct(normal_fast_dispatch64 op x)as[y|]eqn:Fast.
  - destruct(normal_fast_dispatch_decided op x y Fx Pdf Fast)as[F Rounded].
    apply normal_exact_bounded;assumption.
  - apply normal_accurate_bounded;assumption.
Qed.

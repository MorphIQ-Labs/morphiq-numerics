(** End-to-end regular scalar dispatch: an accepted fast interval or the
    Q256 fallback, with a common bound on the exact normal-family target. *)
From Coq Require Import Reals.
From Binary64 Require Import IEEE64.
Require Import NormalFastDispatch NormalPublicModel NormalPublicBounds
  NormalPublicAccurate NormalPublicDomain.
Open Scope R_scope.
Local Opaque normal_fast_dispatch64 normal_accurate64 normal_special64.

Theorem normal_regular_bounded op x : finite x -> normal_special64 op x=None ->
  normal_bounded(normal_target op (B x))(normal_regular64 op x).
Proof.
  intros Fx Screen;destruct(normal_regular_domain op x Fx Screen)as[Domain Pdf].
  unfold normal_regular64;destruct(normal_fast_dispatch64 op x)as[y|]eqn:Fast.
  - destruct(normal_fast_dispatch_decided op x y Fx Pdf Fast)as[F Rounded].
    apply normal_exact_bounded;assumption.
  - apply normal_accurate_bounded;assumption.
Qed.

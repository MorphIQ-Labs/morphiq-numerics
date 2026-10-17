(** End-to-end regular scalar dispatch: an accepted first-stage or fast
    interval or the Q256 fallback, with a common bound on the exact
    normal-family target. *)
From Coq Require Import Reals.
From Coq Require Import ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add RoundingTest Encodings.
Require Import StageGappa NormalComparisons NormalFastDispatch NormalDensityFirst NormalTailFirst NormalCenterFirst ErfcxDecision NormalPublicModel NormalPublicBounds
  NormalPublicAccurate NormalPublicDomain NormalAccurateDensity.
Open Scope R_scope.
Local Opaque normal_fast_dispatch64 normal_accurate64 normal_special64 normal_density_first64 normal_tail_first64 normal_center_first64.

Theorem normal_regular_bounded op x : finite x -> normal_special64 op x=None ->
  normal_bounded(normal_target op (B x))(normal_regular64 op x).
Proof.
  intros Fx Screen;destruct(normal_regular_domain op x Fx Screen)as[Domain Pdf].
  unfold normal_regular64;destruct(normal_first64 op x)as[y|]eqn:First.
  { unfold normal_first64 in First.
    assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
    assert(Tail : forall op', (op'=NormalCdf \/ op'=NormalCentered) ->
      (if normal_lt normal_thirty_six (b64_abs x) then None else
       if normal_le (b64_abs x) (erfcx_pow2(-1)) then
         if normal_lt (b64_abs x) (erfcx_pow2(-33)) then None else normal_center_first64 op' x
       else normal_tail_first64 op' x)=Some y -> normal_bounded(normal_target op' (B x)) y).
    { intros op' _ T.
      destruct(erfcx_pow2_ok (-1) ltac:(lia))as[Fh Bh].
      destruct(erfcx_pow2_ok (-33) ltac:(lia))as[Fs Bs].
      assert(F36 : finite normal_thirty_six)by(exact(bits_finite 4630263366890291200 false 5066549580791808 (-47) eq_refl)).
      assert(B36 : B normal_thirty_six=36)by(change(5066549580791808*bpow radix2(-47)=36);bpow_num;field).
      destruct(normal_lt normal_thirty_six (b64_abs x))eqn:High;[discriminate|].
      apply(normal_lt_false _ _ F36 Fa)in High. rewrite B_abs,B36 in High.
      destruct(normal_le (b64_abs x) (erfcx_pow2(-1)))eqn:Low.
      - destruct(normal_lt (b64_abs x) (erfcx_pow2(-33)))eqn:Small;[discriminate|].
        apply(normal_le_true _ _ Fa Fh)in Low;apply(normal_lt_false _ _ Fa Fs)in Small.
        rewrite B_abs,Bh in Low;rewrite B_abs,Bs in Small;change(bpow radix2 (-1))with(/2)in Low.
        destruct(normal_center_first_ok op' x y Fx ltac:(split;lra)T)as[F Rounded].
        apply normal_exact_bounded;assumption.
      - apply(normal_le_false _ _ Fa Fh)in Low.
        rewrite B_abs,Bh in Low;change(bpow radix2 (-1))with(/2)in Low.
        destruct(normal_tail_first_ok op' x y Fx ltac:(split;lra)T)as[F Rounded].
        apply normal_exact_bounded;assumption. }
    destruct op;[ | exact(Tail NormalCdf (or_introl eq_refl) First) | exact(Tail NormalCentered (or_intror eq_refl) First) | discriminate].
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

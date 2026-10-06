(** The square root in IEEE 754 binary64 arithmetic: Flocq's [b64_sqrt] at
    [mode_NE]. For every [x] it is the binary64-model rounding of [sqrt x]
    (Coq's [sqrt] is 0 below 0, where the result is a NaN whose value [B2R]
    reads as 0), and it is finite exactly for the finite [x >= 0], [-0]
    included. The Rust [sqrt] (crates/morphiq-numerics/src/sqrt.rs) is checked
    against this definition bit for bit on the cross-check corpus
    (formal/extraction). *)

From Coq Require Import Reals ZArith Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.

Open Scope R_scope.

Definition fsqrt (x : f64) : f64 := b64_sqrt mode_NE x.

Theorem sqrt_ieee x : B (fsqrt x) = rndF (sqrt (B x)) /\
  (finite (fsqrt x) <-> finite x /\ 0 <= B x).
Proof.
  destruct (Bsqrt_correct 53 1024 eq_refl eq_refl unop_nan_pl64 mode_NE x) as [C1 [C2 _]].
  split; [exact C1 | ].
  unfold fsqrt, b64_sqrt. rewrite C2.
  destruct x as [s | s | s pl Hpl | s m e Hx]; simpl.
  - split; [intros _; split; [reflexivity | lra] | now intros].
  - split; [discriminate | intros [F _]; discriminate F].
  - split; [discriminate | intros [F _]; discriminate F].
  - destruct s.
    + split; [discriminate | ].
      intros [_ H]. exfalso. unfold F2R in H; simpl in H.
      pose proof (bpow_gt_0 radix2 e). assert (0 < IZR (Zpos m)) by (apply IZR_lt; reflexivity).
      rewrite <- (Ropp_involutive (IZR (Zneg m) * bpow radix2 e)) in H.
      replace (- (IZR (Zneg m) * bpow radix2 e)) with (IZR (Zpos m) * bpow radix2 e) in H
        by (rewrite <- Pos2Z.opp_pos, opp_IZR; ring).
      pose proof (Rmult_lt_0_compat _ _ H1 H0). lra.
    + split; [intros _; split; [reflexivity | ] | now intros].
      apply F2R_ge_0. simpl. apply Pos2Z.is_nonneg.
Qed.

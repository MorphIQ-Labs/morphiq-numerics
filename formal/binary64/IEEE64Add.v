(** The additive algorithms in IEEE 754 binary64 arithmetic: on operands at
    most [m 2^e] in magnitude, with the stated multiple of [m] below both
    [2^53] and [2^(1024 - e)], no operation overflows, and each returns its
    binary64-model value ([Binary64Add.v]). *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.

Open Scope R_scope.

(** One step: [step lemma bound] specializes [lemma] into [S], discharging its
    numeric side conditions (the bound is a valid significand and below the
    overflow threshold) by [lia], with the operands' bound [bound]. *)
Ltac step lem bound :=
  pose proof lem as S;
  repeat match type of S with
    | (?P -> _) => let h := fresh in assert (h : P) by lia; specialize (S h); clear h
  end;
  specialize (S bound).

(** [w k b] weakens bound [b] to [k]. *)
Notation w k b := (bnd_weaken _ k _ _ b ltac:(lia)).

Definition two_sum64 (a b : f64) : f64 * f64 :=
  let s := fadd a b in
  let a' := fsub s b in
  let b' := fsub s a' in
  let da := fsub a a' in
  let db := fsub b b' in
  (s, fadd da db).

Definition fast_two_sum64 (a b : f64) : f64 * f64 :=
  let s := fadd a b in
  let z := fsub s a in
  (s, fsub b z).

Lemma two_sum64_ok m e a b : finite a -> finite b -> bnd m e (B a) -> bnd m e (B b) ->
  (0 <= m)%Z -> (10 * m < 2 ^ 53)%Z -> (10 * m < 2 ^ (1024 - e))%Z -> (-1074 <= e <= 1024)%Z ->
  finite (fst (two_sum64 a b)) /\ finite (snd (two_sum64 a b))
  /\ (B (fst (two_sum64 a b)), B (snd (two_sum64 a b))) = two_sum (B a) (B b)
  /\ bnd (2 * m) e (B (fst (two_sum64 a b))) /\ bnd (10 * m) e (B (snd (two_sum64 a b))).
Proof.
  intros Fa Fb Ba Bb Hm H53 Ho He.
  unfold two_sum64; cbn [fst snd].
  step (fadd_bnd (2 * m) e a b Fa Fb) (w (2 * m)%Z (bnd_plus _ _ _ _ _ Ba Bb)).
  destruct S as [Fs [Es Bs]]. set (s := fadd a b) in *.
  step (fsub_bnd (3 * m) e s b Fs Fb) (w (3 * m)%Z (bnd_minus _ _ _ _ _ Bs Bb)).
  destruct S as [Fa' [Ea' Ba']]. set (a' := fsub s b) in *.
  step (fsub_bnd (5 * m) e s a' Fs Fa') (w (5 * m)%Z (bnd_minus _ _ _ _ _ Bs Ba')).
  destruct S as [Fb' [Eb' Bb']]. set (b' := fsub s a') in *.
  step (fsub_bnd (4 * m) e a a' Fa Fa') (w (4 * m)%Z (bnd_minus _ _ _ _ _ Ba Ba')).
  destruct S as [Fda [Eda Bda]].
  step (fsub_bnd (6 * m) e b b' Fb Fb') (w (6 * m)%Z (bnd_minus _ _ _ _ _ Bb Bb')).
  destruct S as [Fdb [Edb Bdb]].
  step (fadd_bnd (10 * m) e (fsub a a') (fsub b b') Fda Fdb) (w (10 * m)%Z (bnd_plus _ _ _ _ _ Bda Bdb)).
  destruct S as [Fr [Er Br]].
  repeat split; try assumption.
  unfold two_sum. rewrite Er, Edb, Eda, Eb', Ea', Es. reflexivity.
Qed.

Lemma fast_two_sum64_ok m e a b : finite a -> finite b -> bnd m e (B a) -> bnd m e (B b) ->
  (0 <= m)%Z -> (4 * m < 2 ^ 53)%Z -> (4 * m < 2 ^ (1024 - e))%Z -> (-1074 <= e <= 1024)%Z ->
  finite (fst (fast_two_sum64 a b)) /\ finite (snd (fast_two_sum64 a b))
  /\ (B (fst (fast_two_sum64 a b)), B (snd (fast_two_sum64 a b))) = fast_two_sum (B a) (B b)
  /\ bnd (2 * m) e (B (fst (fast_two_sum64 a b))) /\ bnd (4 * m) e (B (snd (fast_two_sum64 a b))).
Proof.
  intros Fa Fb Ba Bb Hm H53 Ho He.
  unfold fast_two_sum64; cbn [fst snd].
  step (fadd_bnd (2 * m) e a b Fa Fb) (w (2 * m)%Z (bnd_plus _ _ _ _ _ Ba Bb)).
  destruct S as [Fs [Es Bs]]. set (s := fadd a b) in *.
  step (fsub_bnd (3 * m) e s a Fs Fa) (w (3 * m)%Z (bnd_minus _ _ _ _ _ Bs Ba)).
  destruct S as [Fz [Ez Bz]].
  step (fsub_bnd (4 * m) e b (fsub s a) Fb Fz) (w (4 * m)%Z (bnd_minus _ _ _ _ _ Bb Bz)).
  destruct S as [Fr [Er Br]].
  repeat split; try assumption.
  unfold fast_two_sum. rewrite Er, Ez, Es. reflexivity.
Qed.

Definition add_f64_64 (xh xl y : f64) : f64 * f64 :=
  let '(sh, sl) := two_sum64 xh y in
  let v := fadd xl sl in
  fast_two_sum64 sh v.

Definition add64 (xh xl yh yl : f64) : f64 * f64 :=
  let '(sh, sl) := two_sum64 xh yh in
  let '(th, tl) := two_sum64 xl yl in
  let c := fadd sl th in
  let '(vh, vl) := fast_two_sum64 sh c in
  let w := fadd tl vl in
  fast_two_sum64 vh w.

Definition fneg (x : f64) : f64 := b64_opp x.

Definition sub64 (xh xl yh yl : f64) : f64 * f64 := add64 xh xl (fneg yh) (fneg yl).

Lemma add_f64_64_ok m e xh xl y :
  finite xh -> finite xl -> finite y -> bnd m e (B xh) -> bnd m e (B xl) -> bnd m e (B y) ->
  (0 <= m)%Z -> (44 * m < 2 ^ 53)%Z -> (44 * m < 2 ^ (1024 - e))%Z -> (-1074 <= e <= 1024)%Z ->
  finite (fst (add_f64_64 xh xl y)) /\ finite (snd (add_f64_64 xh xl y))
  /\ (B (fst (add_f64_64 xh xl y)), B (snd (add_f64_64 xh xl y))) = add_f64 (B xh) (B xl) (B y).
Proof.
  intros Fh Fl Fy Bh Bl By Hm H53 Ho He.
  destruct (two_sum64_ok m e xh y Fh Fy Bh By ltac:(lia) ltac:(lia) ltac:(lia) He)
    as [Fsh [Fsl [Es [Bsh Bsl]]]].
  unfold add_f64_64, add_f64. rewrite <- Es.
  destruct (two_sum64 xh y) as [sh sl]. cbn [fst snd] in *.
  step (fadd_bnd (11 * m) e xl sl Fl Fsl) (w (11 * m)%Z (bnd_plus _ _ _ _ _ Bl Bsl)).
  destruct S as [Fv [Ev Bv]].
  destruct (fast_two_sum64_ok (11 * m) e sh (fadd xl sl) Fsh Fv (w (11 * m)%Z Bsh) Bv
              ltac:(lia) ltac:(lia) ltac:(lia) He) as [Fzh [Fzl [Ez _]]].
  rewrite <- Ev. repeat split; assumption.
Qed.

Lemma add64_ok m e xh xl yh yl :
  finite xh -> finite xl -> finite yh -> finite yl ->
  bnd m e (B xh) -> bnd m e (B xl) -> bnd m e (B yh) -> bnd m e (B yl) ->
  (0 <= m)%Z -> (232 * m < 2 ^ 53)%Z -> (232 * m < 2 ^ (1024 - e))%Z -> (-1074 <= e <= 1024)%Z ->
  finite (fst (add64 xh xl yh yl)) /\ finite (snd (add64 xh xl yh yl))
  /\ (B (fst (add64 xh xl yh yl)), B (snd (add64 xh xl yh yl))) = add (B xh) (B xl) (B yh) (B yl).
Proof.
  intros Fxh Fxl Fyh Fyl Bxh Bxl Byh Byl Hm H53 Ho He.
  destruct (two_sum64_ok m e xh yh Fxh Fyh Bxh Byh ltac:(lia) ltac:(lia) ltac:(lia) He)
    as [Fsh [Fsl [Es [Bsh Bsl]]]].
  destruct (two_sum64_ok m e xl yl Fxl Fyl Bxl Byl ltac:(lia) ltac:(lia) ltac:(lia) He)
    as [Fth [Ftl [Et [Bth Btl]]]].
  unfold add64, add. rewrite <- Es, <- Et.
  destruct (two_sum64 xh yh) as [sh sl]. destruct (two_sum64 xl yl) as [th tl].
  cbn [fst snd] in *.
  step (fadd_bnd (12 * m) e sl th Fsl Fth) (w (12 * m)%Z (bnd_plus _ _ _ _ _ Bsl Bth)).
  destruct S as [Fc [Ec Bc]].
  destruct (fast_two_sum64_ok (12 * m) e sh (fadd sl th) Fsh Fc (w (12 * m)%Z Bsh) Bc
              ltac:(lia) ltac:(lia) ltac:(lia) He) as [Fvh [Fvl [Ev [Bvh Bvl]]]].
  rewrite <- Ec, <- Ev.
  destruct (fast_two_sum64 sh (fadd sl th)) as [vh vl]. cbn [fst snd] in *.
  step (fadd_bnd (58 * m) e tl vl Ftl Fvl)
    (w (58 * m)%Z (bnd_plus _ _ _ _ _ Btl (w (48 * m)%Z Bvl))).
  destruct S as [Fw [Ew Bw]].
  destruct (fast_two_sum64_ok (58 * m) e vh (fadd tl vl) Fvh Fw (w (58 * m)%Z Bvh) Bw
              ltac:(lia) ltac:(lia) ltac:(lia) He) as [Fzh [Fzl [Ez _]]].
  rewrite <- Ew. repeat split; assumption.
Qed.

(** The bounds, for IEEE inputs: every word at most [2^1018] ([add_f64]) or
    [2^1016] ([add], [sub]) in magnitude keeps every operation finite. *)
Theorem add_f64_ieee xh xl y :
  finite xh -> finite xl -> finite y -> B xh = rndF (B xh + B xl) ->
  Rabs (B xh) <= bpow radix2 1018 -> Rabs (B xl) <= bpow radix2 1018 -> Rabs (B y) <= bpow radix2 1018 ->
  let '(zh, zl) := add_f64_64 xh xl y in
  finite zh /\ finite zl /\
  Rabs ((B zh + B zl - (B xh + B xl + B y)) / (B xh + B xl + B y)) <= 2 * bpow radix2 (- prec) ^ 2.
Proof.
  intros Fh Fl Fy E Bh Bl By.
  assert (U : forall v, Rabs v <= bpow radix2 1018 -> bnd 1 1018 v) by (intros v Hv; unfold bnd; lra).
  destruct (add_f64_64_ok 1 1018 xh xl y Fh Fl Fy (U _ Bh) (U _ Bl) (U _ By)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl Ez]].
  pose proof (add_f64_bound (B xh) (B xl) (B y) (B_fmt xh) (B_fmt xl) (B_fmt y) E) as Bd.
  rewrite <- Ez in Bd.
  destruct (add_f64_64 xh xl y) as [zh zl]. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

Theorem add_ieee xh xl yh yl :
  finite xh -> finite xl -> B xh = rndF (B xh + B xl) ->
  finite yh -> finite yl -> B yh = rndF (B yh + B yl) ->
  Rabs (B xh) <= bpow radix2 1016 -> Rabs (B xl) <= bpow radix2 1016 ->
  Rabs (B yh) <= bpow radix2 1016 -> Rabs (B yl) <= bpow radix2 1016 ->
  B xh + B xl + (B yh + B yl) <> 0 ->
  let '(zh, zl) := add64 xh xl yh yl in
  finite zh /\ finite zl /\
  Rabs ((B zh + B zl - (B xh + B xl + (B yh + B yl))) / (B xh + B xl + (B yh + B yl)))
    <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Bxh Bxl Byh Byl Hn.
  assert (U : forall v, Rabs v <= bpow radix2 1016 -> bnd 1 1016 v) by (intros v Hv; unfold bnd; lra).
  destruct (add64_ok 1 1016 xh xl yh yl Fxh Fxl Fyh Fyl (U _ Bxh) (U _ Bxl) (U _ Byh) (U _ Byl)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl Ez]].
  pose proof (add_bound (B xh) (B xl) (B yh) (B yl) (B_fmt xh) (B_fmt xl) Ex
                (B_fmt yh) (B_fmt yl) Ey Hn) as Bd.
  rewrite <- Ez in Bd.
  destruct (add64 xh xl yh yl) as [zh zl]. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

Theorem sub_ieee xh xl yh yl :
  finite xh -> finite xl -> B xh = rndF (B xh + B xl) ->
  finite yh -> finite yl -> B yh = rndF (B yh + B yl) ->
  Rabs (B xh) <= bpow radix2 1016 -> Rabs (B xl) <= bpow radix2 1016 ->
  Rabs (B yh) <= bpow radix2 1016 -> Rabs (B yl) <= bpow radix2 1016 ->
  B xh + B xl - (B yh + B yl) <> 0 ->
  let '(zh, zl) := sub64 xh xl yh yl in
  finite zh /\ finite zl /\
  Rabs ((B zh + B zl - (B xh + B xl - (B yh + B yl))) / (B xh + B xl - (B yh + B yl)))
    <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Bxh Bxl Byh Byl Hn.
  assert (Nb : forall x, B (fneg x) = - B x) by (intros x; apply B2R_Bopp).
  assert (Nf : forall x, finite x -> finite (fneg x))
    by (intros x Fx; unfold fneg, b64_opp; now rewrite is_finite_Bopp).
  unfold sub64.
  pose proof (add_ieee xh xl (fneg yh) (fneg yl) Fxh Fxl Ex (Nf _ Fyh) (Nf _ Fyl)) as A.
  rewrite !Nb in A.
  replace (B xh + B xl - (B yh + B yl)) with (B xh + B xl + (- B yh + - B yl)) in * by ring.
  apply A; try assumption; rewrite ?Rabs_Ropp; try assumption.
  now apply dw_opp.
Qed.

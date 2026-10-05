(** The double-word divisions in IEEE 754 binary64 arithmetic, on the domain
    of [Binary64Div.v]: for [L, H >= 0] with [2L + 2H <= 917], every nonzero
    word [w] has [2^-L <= |w| < 2^H]. A quotient by a divisor at least [2^-L]
    is at most [2^L] times its dividend's bound, so every operation's bound
    stays below [2^(2H + 2L + 9) <= 2^926]: no operation overflows, and each
    algorithm returns its binary64-model value. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul Binary64Div IEEE64 IEEE64Add IEEE64Mul.
Require TwoProdBinary64.

Open Scope R_scope.

Lemma bnd_div k e L x y : (0 <= k)%Z -> bnd k e x -> bpow radix2 (- L) <= Rabs y ->
  bnd k (e + L) (x / y).
Proof.
  unfold bnd. intros Hk Hx Hy.
  assert (Py : 0 < Rabs y) by (pose proof (bpow_gt_0 radix2 (- L)); lra).
  assert (y0 : y <> 0) by (intros ->; rewrite Rabs_R0 in Py; lra).
  unfold Rdiv. rewrite Rabs_mult, (Rabs_Rinv y y0), bpow_plus.
  apply Rmult_le_reg_r with (Rabs y); [exact Py | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  apply Rle_trans with (1 := Hx).
  replace (IZR k * (bpow radix2 e * bpow radix2 L) * Rabs y)
    with (IZR k * bpow radix2 e * (bpow radix2 L * Rabs y)) by ring.
  rewrite <- (Rmult_1_r (IZR k * bpow radix2 e)) at 1.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos; [now apply IZR_le | apply bpow_ge_0].
  - replace 1 with (bpow radix2 L * bpow radix2 (- L)) by (rewrite <- bpow_plus; now replace (L + - L)%Z with 0%Z by ring).
    apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Hy].
Qed.

Lemma bnd_div_to k e L e' x y : (e' = e + L)%Z -> (0 <= k)%Z -> bnd k e x ->
  bpow radix2 (- L) <= Rabs y -> bnd k e' (x / y).
Proof. intros ->. apply bnd_div. Qed.

Lemma range_bnd L H w : in_range L H w -> bnd 1 H w.
Proof. unfold bnd. intros [-> | [_ Hw]]; rewrite ?Rabs_R0; pose proof (bpow_gt_0 radix2 H); lra. Qed.

Definition div_f64_64 (xh xl y : f64) : f64 * f64 :=
  let th := fdiv xh y in
  let '(pih, pil) := two_prod64 th y in
  let dh := fsub xh pih in
  let dt := fsub dh pil in
  let d := fadd dt xl in
  let tl := fdiv d y in
  fast_two_sum64 th tl.

Definition div64 (xh xl yh yl : f64) : f64 * f64 :=
  let th := fdiv xh yh in
  let '(rh, rl) := mul_f64_64 yh yl th in
  let pih := fsub xh rh in
  let dl := fsub xl rl in
  let d := fadd pih dl in
  let tl := fdiv d yh in
  fast_two_sum64 th tl.

Lemma div_f64_64_ok L H xh xl y :
  (0 <= L)%Z -> (0 <= H)%Z -> (2 * L + 2 * H <= 917)%Z ->
  finite xh -> finite xl -> finite y -> bnd 1 H (B xh) -> bnd 1 H (B xl) -> bnd 1 H (B y) ->
  bpow radix2 (- L) <= Rabs (B y) ->
  finite (fst (div_f64_64 xh xl y)) /\ finite (snd (div_f64_64 xh xl y))
  /\ (B (fst (div_f64_64 xh xl y)), B (snd (div_f64_64 xh xl y))) = div_f64 (B xh) (B xl) (B y).
Proof.
  intros HL HH HLH Fxh Fxl Fy Bxh Bxl By Ly.
  assert (Y0 : B y <> 0) by (intros E; rewrite E, Rabs_R0 in Ly; pose proof (bpow_gt_0 radix2 (- L)); lra).
  pose proof (pow_ge 7 (1024 - (H + L)) ltac:(lia)) as P1.
  pose proof (pow_ge 7 (1024 - (2 * H + L)) ltac:(lia)) as P2.
  pose proof (pow_ge 7 (1024 - (2 * H + 2 * L)) ltac:(lia)) as P3.
  change (2 ^ 7)%Z with 128%Z in P1, P2, P3.
  step (fdiv_bnd 1 (H + L) xh y Fxh Y0) (bnd_div 1 H L _ _ ltac:(lia) Bxh Ly).
  destruct S as [Fth [Eth Bth]].
  unfold div_f64_64, div_f64. rewrite <- Eth.
  set (th := fdiv xh y) in *.
  destruct (two_prod64_ok (H + L) H th y Fth Fy Bth By ltac:(lia) ltac:(lia) ltac:(lia))
    as [Fpih [Fpil [Ep [Bpih Bpil]]]].
  rewrite <- Ep.
  destruct (two_prod64 th y) as [pih pil]. cbn [fst snd] in *.
  replace (H + L + H)%Z with (2 * H + L)%Z in Bpih, Bpil by ring.
  assert (Bxh' : bnd 1 (2 * H + L) (B xh)) by (apply (bnd_up 1 H); [lia | lia | exact Bxh]).
  assert (Bxl' : bnd 1 (2 * H + L) (B xl)) by (apply (bnd_up 1 H); [lia | lia | exact Bxl]).
  step (fsub_bnd 2 (2 * H + L) xh pih Fxh Fpih) (bnd_minus _ _ _ _ _ Bxh' Bpih).
  destruct S as [Fdh [Edh Bdh]].
  step (fsub_bnd 12 (2 * H + L) _ pil Fdh Fpil) (bnd_minus _ _ _ _ _ Bdh Bpil).
  destruct S as [Fdt [Edt Bdt]].
  step (fadd_bnd 13 (2 * H + L) _ xl Fdt Fxl) (bnd_plus _ _ _ _ _ Bdt Bxl').
  destruct S as [Fd [Ed Bd]].
  step (fdiv_bnd 13 (2 * H + 2 * L) _ y Fd Y0)
    (bnd_div_to 13 (2 * H + L) L (2 * H + 2 * L) _ _ ltac:(lia) ltac:(lia) Bd Ly).
  destruct S as [Ftl [Etl Btl]].
  assert (Bth' : bnd 13 (2 * H + 2 * L) (B th)) by (apply (bnd_up 13 (H + L)); [lia | lia | exact (w 13%Z Bth)]).
  destruct (fast_two_sum64_ok 13 (2 * H + 2 * L) th _ Fth Ftl Bth' Btl
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl [Ez _]]].
  rewrite Etl, Ed, Edt, Edh in Ez. repeat split; assumption.
Qed.

Lemma div64_ok L H xh xl yh yl :
  (0 <= L)%Z -> (0 <= H)%Z -> (2 * L + 2 * H <= 917)%Z ->
  finite xh -> finite xl -> finite yh -> finite yl ->
  bnd 1 H (B xh) -> bnd 1 H (B xl) -> bnd 1 H (B yh) -> bnd 1 H (B yl) ->
  bpow radix2 (- L) <= Rabs (B yh) ->
  finite (fst (div64 xh xl yh yl)) /\ finite (snd (div64 xh xl yh yl))
  /\ (B (fst (div64 xh xl yh yl)), B (snd (div64 xh xl yh yl))) = div (B xh) (B xl) (B yh) (B yl).
Proof.
  intros HL HH HLH Fxh Fxl Fyh Fyl Bxh Bxl Byh Byl Ly.
  assert (Y0 : B yh <> 0) by (intros E; rewrite E, Rabs_R0 in Ly; pose proof (bpow_gt_0 radix2 (- L)); lra).
  pose proof (pow_ge 7 (1024 - (H + L)) ltac:(lia)) as P1.
  pose proof (pow_ge 7 (1024 - (2 * H + L)) ltac:(lia)) as P2.
  pose proof (pow_ge 9 (1024 - (2 * H + 2 * L)) ltac:(lia)) as P3.
  change (2 ^ 7)%Z with 128%Z in P1, P2. change (2 ^ 9)%Z with 512%Z in P3.
  step (fdiv_bnd 1 (H + L) xh yh Fxh Y0) (bnd_div 1 H L _ _ ltac:(lia) Bxh Ly).
  destruct S as [Fth [Eth Bth]].
  unfold div64, div. rewrite <- Eth.
  set (th := fdiv xh yh) in *.
  destruct (mul_f64_64_ok H (H + L) yh yl th Fyh Fyl Fth Byh Byl Bth ltac:(lia) ltac:(lia) ltac:(lia))
    as [Frh [Frl [Er [Brh Brl]]]].
  rewrite <- Er.
  destruct (mul_f64_64 yh yl th) as [rh rl]. cbn [fst snd] in *.
  replace (H + (H + L))%Z with (2 * H + L)%Z in Brh, Brl by ring.
  assert (Bxh' : bnd 1 (2 * H + L) (B xh)) by (apply (bnd_up 1 H); [lia | lia | exact Bxh]).
  assert (Bxl' : bnd 1 (2 * H + L) (B xl)) by (apply (bnd_up 1 H); [lia | lia | exact Bxl]).
  step (fsub_bnd 29 (2 * H + L) xh rh Fxh Frh) (bnd_minus _ _ _ _ _ Bxh' Brh).
  destruct S as [Fpih [Epih Bpih]].
  step (fsub_bnd 57 (2 * H + L) xl rl Fxl Frl) (bnd_minus _ _ _ _ _ Bxl' Brl).
  destruct S as [Fdl [Edl Bdl]].
  step (fadd_bnd 86 (2 * H + L) _ _ Fpih Fdl) (bnd_plus _ _ _ _ _ Bpih Bdl).
  destruct S as [Fd [Ed Bd]].
  step (fdiv_bnd 86 (2 * H + 2 * L) _ yh Fd Y0)
    (bnd_div_to 86 (2 * H + L) L (2 * H + 2 * L) _ _ ltac:(lia) ltac:(lia) Bd Ly).
  destruct S as [Ftl [Etl Btl]].
  assert (Bth' : bnd 86 (2 * H + 2 * L) (B th)) by (apply (bnd_up 86 (H + L)); [lia | lia | exact (w 86%Z Bth)]).
  destruct (fast_two_sum64_ok 86 (2 * H + 2 * L) th _ Fth Ftl Bth' Btl
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl [Ez _]]].
  rewrite Etl, Ed, Edl, Epih in Ez. repeat split; assumption.
Qed.

(** The bounds, for IEEE inputs on the division domain: no operation
    overflows, so the results are finite and within the proved bounds. *)
Theorem div_f64_ieee L H xh xl y :
  (0 <= L)%Z -> (0 <= H)%Z -> (2 * L + 2 * H <= 917)%Z ->
  finite xh -> finite xl -> finite y -> B xh = rndF (B xh + B xl) -> B y <> 0 ->
  in_range L H (B xh) -> in_range L H (B xl) -> in_range L H (B y) ->
  let '(zh, zl) := div_f64_64 xh xl y in
  finite zh /\ finite zl /\
  Rabs ((B zh + B zl - (B xh + B xl) / B y) / ((B xh + B xl) / B y))
    <= 3 * (bpow radix2 (- prec) * bpow radix2 (- prec)).
Proof.
  intros HL HH HLH Fxh Fxl Fy E Y0 Rxh Rxl Ry.
  assert (Ly : bpow radix2 (- L) <= Rabs (B y)) by (destruct Ry as [Y | [Y _]]; [now elim Y0 | exact Y]).
  destruct (div_f64_64_ok L H xh xl y HL HH HLH Fxh Fxl Fy (range_bnd _ _ _ Rxh) (range_bnd _ _ _ Rxl)
              (range_bnd _ _ _ Ry) Ly) as [Fzh [Fzl Ez]].
  pose proof (div_f64_bound L H (B xh) (B xl) (B y) HL HH HLH (B_fmt xh) (B_fmt xl) (B_fmt y) E Y0
                Rxh Rxl Ry) as Bd.
  rewrite <- Ez in Bd.
  destruct (div_f64_64 xh xl y) as [zh zl]. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

Theorem div_ieee L H xh xl yh yl :
  (0 <= L)%Z -> (0 <= H)%Z -> (2 * L + 2 * H <= 917)%Z ->
  finite xh -> finite xl -> B xh = rndF (B xh + B xl) ->
  finite yh -> finite yl -> B yh = rndF (B yh + B yl) -> B yh <> 0 ->
  in_range L H (B xh) -> in_range L H (B xl) -> in_range L H (B yh) -> in_range L H (B yl) ->
  let '(zh, zl) := div64 xh xl yh yl in
  finite zh /\ finite zl /\
  Rabs ((B zh + B zl - (B xh + B xl) / (B yh + B yl)) / ((B xh + B xl) / (B yh + B yl)))
    <= 15 * bpow radix2 (- prec) ^ 2 + 56 * bpow radix2 (- prec) ^ 3.
Proof.
  intros HL HH HLH Fxh Fxl Ex Fyh Fyl Ey Y0 Rxh Rxl Ryh Ryl.
  assert (Ly : bpow radix2 (- L) <= Rabs (B yh)) by (destruct Ryh as [Y | [Y _]]; [now elim Y0 | exact Y]).
  destruct (div64_ok L H xh xl yh yl HL HH HLH Fxh Fxl Fyh Fyl (range_bnd _ _ _ Rxh) (range_bnd _ _ _ Rxl)
              (range_bnd _ _ _ Ryh) (range_bnd _ _ _ Ryl) Ly) as [Fzh [Fzl Ez]].
  pose proof (div_bound L H (B xh) (B xl) (B yh) (B yl) HL HH HLH (B_fmt xh) (B_fmt xl) Ex
                (B_fmt yh) (B_fmt yl) Ey Y0 Rxh Rxl Ryh Ryl) as Bd.
  rewrite <- Ez in Bd.
  destruct (div64 xh xl yh yl) as [zh zl]. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

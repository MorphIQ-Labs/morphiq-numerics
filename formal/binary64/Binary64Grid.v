(** Fixed binary grids track the least possible nonzero low word through
    double-word compositions. Rounding preserves a grid, so an integer
    multiple argument can discharge underflow hypotheses without assuming
    that every intermediate has a large relative magnitude. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64.
Open Scope R_scope.

Definition binary_grid e x := generic_format radix2 (FIX_exp e) x.

Lemma binary_grid_integer e x : binary_grid e x <-> exists m:Z,x=IZR m*bpow radix2 e.
Proof.
  split.
  - intros G;destruct(FIX_format_generic radix2 e x G)as[[m k]Value Exponent].
    simpl in Exponent;subst k;exists m;exact Value.
  - intros[m Value];apply generic_format_FIX.
    apply(FIX_spec radix2 e x (Float radix2 m e));[exact Value|reflexivity].
Qed.

Lemma binary_grid_round e x : binary_grid e x -> binary_grid e (rndF x).
Proof.
  intros G;unfold binary_grid,rndF;apply generic_round_generic;auto with typeclass_instances.
Qed.

Lemma binary_grid_zero e : binary_grid e 0.
Proof. apply generic_format_0. Qed.

Lemma binary_grid_add e x y : binary_grid e x -> binary_grid e y -> binary_grid e (x+y).
Proof.
  rewrite !binary_grid_integer;intros[m X][n Y];exists(m+n)%Z;rewrite X,Y,plus_IZR;ring.
Qed.

Lemma binary_grid_opp e x : binary_grid e x -> binary_grid e (-x).
Proof. intros X;apply generic_format_opp;exact X. Qed.

Lemma binary_grid_sub e x y : binary_grid e x -> binary_grid e y -> binary_grid e (x-y).
Proof.
  rewrite !binary_grid_integer;intros[m X][n Y];exists(m-n)%Z;rewrite X,Y,minus_IZR;ring.
Qed.

Lemma binary_grid_mul ex ey x y : binary_grid ex x -> binary_grid ey y -> binary_grid(ex+ey)(x*y).
Proof.
  rewrite !binary_grid_integer;intros[m X][n Y];exists(m*n)%Z;rewrite X,Y,mult_IZR,bpow_plus;ring.
Qed.

Lemma binary_grid_finer e f x : (e<=f)%Z -> binary_grid f x -> binary_grid e x.
Proof.
  intros E G;apply(generic_inclusion_mag radix2 (FIX_exp f)(FIX_exp e)x);[intros _;exact E|exact G].
Qed.

Lemma binary_grid_nonzero e x : binary_grid e x -> x=0 \/ bpow radix2 e<=Rabs x.
Proof.
  rewrite binary_grid_integer;intros[m Value];destruct(Z.eq_dec m 0)as[Zero|Nonzero].
  - left;rewrite Value,Zero;ring.
  - right;rewrite Value,Rabs_mult,(Rabs_pos_eq(bpow radix2 e))by apply bpow_ge_0.
    rewrite <-abs_IZR;assert(1<=IZR(Z.abs m))by(apply IZR_le;lia).
    pose proof(bpow_ge_0 radix2 e);nra.
Qed.

Lemma binary_grid_normal e x : (-1022<=e)%Z -> binary_grid e x -> normal_or_zero x.
Proof.
  intros E G;destruct(binary_grid_nonzero e x G)as[Zero|Bound];[left;exact Zero|right].
  eapply Rle_trans;[|exact Bound];apply bpow_le;exact E.
Qed.

Lemma binary_grid_two_prod_domain ex ey x y : (-969<=ex+ey)%Z ->
  binary_grid ex x -> binary_grid ey y -> in_two_prod_domain x y.
Proof.
  intros E X Y;destruct(binary_grid_nonzero (ex+ey)(x*y)(binary_grid_mul ex ey x y X Y))as[Zero|Bound];
    [left;exact Zero|right].
  eapply Rle_trans;[|exact Bound];apply bpow_le;exact E.
Qed.

Lemma binary_grid_binary64 x lower : bpow radix2 lower<=Rabs(B x) ->
  binary_grid (lower-52)(B x).
Proof.
  intros Lower;apply(generic_inclusion_ge radix2 (FLT_exp emin prec) (FIX_exp(lower-52)) lower).
  - intros e E;unfold FIX_exp,FLT_exp,prec;lia.
  - exact Lower.
  - apply B_fmt.
Qed.

Lemma binary_grid_two_sum e x y : binary_grid e x -> binary_grid e y ->
  let '(h,l):=two_sum x y in binary_grid e h /\ binary_grid e l.
Proof.
  intros X Y;unfold two_sum;split;
    repeat first[apply binary_grid_round|apply binary_grid_sub|apply binary_grid_add|apply binary_grid_opp|assumption].
Qed.

Lemma binary_grid_fast_two_sum e x y : binary_grid e x -> binary_grid e y ->
  let '(h,l):=fast_two_sum x y in binary_grid e h /\ binary_grid e l.
Proof.
  intros X Y;unfold fast_two_sum;split;
    repeat first[apply binary_grid_round|apply binary_grid_sub|apply binary_grid_add|apply binary_grid_opp|assumption].
Qed.

Lemma binary_grid_add_f64 e xh xl y : binary_grid e xh -> binary_grid e xl -> binary_grid e y ->
  let '(h,l):=add_f64 xh xl y in binary_grid e h /\ binary_grid e l.
Proof.
  intros Xh Xl Y;unfold add_f64,two_sum,fast_two_sum;split;
    repeat first[apply binary_grid_round|apply binary_grid_sub|apply binary_grid_add|apply binary_grid_opp|assumption].
Qed.

Lemma binary_grid_add_dw e xh xl yh yl :
  binary_grid e xh -> binary_grid e xl -> binary_grid e yh -> binary_grid e yl ->
  let '(h,l):=add xh xl yh yl in binary_grid e h /\ binary_grid e l.
Proof.
  intros Xh Xl Yh Yl;unfold add,two_sum,fast_two_sum;split;
    repeat first[apply binary_grid_round|apply binary_grid_sub|apply binary_grid_add|apply binary_grid_opp|assumption].
Qed.

Lemma binary_grid_two_prod e x y : fmtF x -> fmtF y -> in_two_prod_domain x y ->
  binary_grid e (x*y) -> let '(h,l):=two_prod x y in binary_grid e h /\ binary_grid e l.
Proof.
  intros Fx Fy Domain Grid.
  pose proof(TwoProdBinary64.two_prod_exact x y Fx Fy Domain)as Total.
  assert(High : binary_grid e (TwoProdBinary64.two_prod_p x y))by(apply binary_grid_round;exact Grid).
  unfold two_prod;split;[exact High|].
  replace(TwoProdBinary64.two_prod_e x y)with(x*y-TwoProdBinary64.two_prod_p x y)by lra.
  apply binary_grid_sub;assumption.
Qed.

Lemma binary_grid_mul_f64 e xh xl y : fmtF xh -> fmtF y -> in_two_prod_domain xh y ->
  binary_grid e (xh*y) -> binary_grid e (xl*y) ->
  let '(h,l):=mul_f64 xh xl y in binary_grid e h /\ binary_grid e l.
Proof.
  intros Fx Fy Domain Leading Cross;pose proof(binary_grid_two_prod e xh y Fx Fy Domain Leading)as Product.
  unfold mul_f64;destruct(two_prod xh y)as[h l];destruct Product as[H L].
  unfold fast_two_sum;split;
    repeat first[apply binary_grid_round|apply binary_grid_sub|apply binary_grid_add|apply binary_grid_opp|assumption].
Qed.

Lemma binary_grid_mul_dw e xh xl yh yl : fmtF xh -> fmtF yh -> in_two_prod_domain xh yh ->
  binary_grid e (xh*yh) -> binary_grid e (xh*yl) -> binary_grid e (xl*yh) ->
  let '(h,l):=mul xh xl yh yl in binary_grid e h /\ binary_grid e l.
Proof.
  intros Fx Fy Domain Leading Cross1 Cross2;pose proof(binary_grid_two_prod e xh yh Fx Fy Domain Leading)as Product.
  unfold mul;destruct(two_prod xh yh)as[h l];destruct Product as[H L].
  unfold fast_two_sum;split;
    repeat first[apply binary_grid_round|apply binary_grid_sub|apply binary_grid_add|apply binary_grid_opp|assumption].
Qed.

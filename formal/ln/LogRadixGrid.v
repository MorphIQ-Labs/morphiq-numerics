(** The fast logarithm's actual intermediates stay on fixed binary grids.
    These are lower bounds on nonzero products, not accuracy assumptions:
    they discharge the underflow premises of double-word radix scaling. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid Encodings.
From Interval Require Import Tactic.
Require Import ExpFast Ln1pLemmas LnTables LnReduction LnAccurate LnFastTables LnTableCheck LnFastTableCheck
  LnFastPoly LnFastCertificates LnFastCorrection LnFastSquare LnFastSum
  LnFastKernel LnFastReduced LnFastZero LnFastAdd LnFastY LnFastLn2 LnFastValue.
Open Scope R_scope.
Local Ltac radix_grid_round := apply grid_round; [exact _ | exact _ | ].

Lemma radix_normalized_grid e h l : h = rndF (h+l) -> on_grid e (h+l) ->
  on_grid e h /\ on_grid e l.
Proof.
  intros D G. assert (Gh : on_grid e h) by (rewrite D; radix_grid_round; assumption).
  split; [exact Gh | replace l with ((h+l)-h) by ring; now apply grid_minus].
Qed.

Lemma radix_add_grid e xh xl yh yl :
  finite xh -> finite xl -> finite yh -> finite yl ->
  Rabs(B xh)<=4096 -> Rabs(B xl)<=4096 -> Rabs(B yh)<=4096 -> Rabs(B yl)<=4096 ->
  on_grid e (B xh) -> on_grid e (B xl) -> on_grid e (B yh) -> on_grid e (B yl) ->
  let '(h,l):=add64 xh xl yh yl in on_grid e (B h) /\ on_grid e (B l).
Proof.
  intros Fxh Fxl Fyh Fyl Xh Xl Yh Yl Gxh Gxl Gyh Gyl.
  assert (Big : forall v, Rabs v<=4096 -> bnd 1 12 v).
  { intros v H. unfold bnd. change (IZR 1*bpow radix2 12) with (1*4096); lra. }
  destruct (add64_ok 1 12 xh xl yh yl Fxh Fxl Fyh Fyl
    (Big _ Xh) (Big _ Xl) (Big _ Yh) (Big _ Yl)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ V]].
  pose proof (grid_add e _ _ _ _ Gxh Gxl Gyh Gyl) as G.
  rewrite <-V in G. destruct (add64 xh xl yh yl); exact G.
Qed.

Lemma radix_add_f64_grid e xh xl y :
  finite xh -> finite xl -> finite y ->
  Rabs(B xh)<=4096 -> Rabs(B xl)<=4096 -> Rabs(B y)<=4096 ->
  on_grid e (B xh) -> on_grid e (B xl) -> on_grid e (B y) ->
  let '(h,l):=add_f64_64 xh xl y in on_grid e (B h) /\ on_grid e (B l).
Proof.
  intros Fxh Fxl Fy Xh Xl Y Gxh Gxl Gy.
  assert (Big : forall v, Rabs v<=4096 -> bnd 1 12 v).
  { intros v H. unfold bnd. change (IZR 1*bpow radix2 12) with (1*4096); lra. }
  destruct (add_f64_64_ok 1 12 xh xl y Fxh Fxl Fy
    (Big _ Xh) (Big _ Xl) (Big _ Y)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ V]].
  pose proof (grid_add_f64 e _ _ _ Gxh Gxl Gy) as G.
  rewrite <-V in G. destruct (add_f64_64 xh xl y); exact G.
Qed.

Lemma radix_horner_grid x : on_grid (-63) x -> on_grid (-434) (lf_wr x).
Proof.
  intros Gx.
  assert (Step : forall e c v, (e<= -56)%Z -> on_grid (-56) c -> on_grid e v ->
    on_grid (e-63) (rndF(c+rndF(x*v)))).
  { intros e c v E Gc Gv. radix_grid_round; apply grid_plus.
    - apply (grid_le (-56)); [lia | exact Gc].
    - radix_grid_round. replace (e-63)%Z with (-63+e)%Z by lia. now apply grid_mult. }
  assert (G3 : on_grid (-56) (B lf_c3)) by
    (rewrite lf_c3_val; apply (val_grid 6004799503160661 54 56); lia).
  assert (G4 : on_grid (-56) (B lf_c4)) by
    (rewrite lf_c4_val; apply (val_grid (-4503599627370541) 54 56); lia).
  assert (G5 : on_grid (-56) (B lf_c5)) by
    (rewrite lf_c5_val; apply (val_grid 7205759403880275 55 56); lia).
  assert (G6 : on_grid (-56) (B lf_c6)) by
    (rewrite lf_c6_val; apply (val_grid (-6004799491394840) 55 56); lia).
  assert (G7 : on_grid (-56) (B lf_c7)) by
    (rewrite lf_c7_val; apply (val_grid 5146968127772584 55 56); lia).
  assert (G8 : on_grid (-56) (B lf_c8)) by
    (rewrite lf_c8_val; apply (val_grid (-4503984727172023) 55 56); lia).
  assert (G9 : on_grid (-56) (B lf_c9)) by
    (rewrite lf_c9_val; apply (val_grid 8060734871950603 56 56); lia).
  pose proof (Step (-56)%Z _ _ ltac:(lia) G8 G9) as H1.
  pose proof (Step (-119)%Z _ _ ltac:(lia) G7 H1) as H2.
  pose proof (Step (-182)%Z _ _ ltac:(lia) G6 H2) as H3.
  pose proof (Step (-245)%Z _ _ ltac:(lia) G5 H3) as H4.
  pose proof (Step (-308)%Z _ _ ltac:(lia) G4 H4) as H5.
  pose proof (Step (-371)%Z _ _ ltac:(lia) G3 H5) as H6.
  rewrite lf_c3_real, lf_c4_real, lf_c5_real, lf_c6_real, lf_c7_real, lf_c8_real, lf_c9_real in H6.
  exact H6.
Qed.

Lemma radix_tail_grid x : finite x -> Rabs(B x)<=/32 -> on_grid (-63) (B x) ->
  on_grid (-623) (B (lf_tail x)).
Proof.
  intros Fx X Gx. destruct (lf_tail_ok x Fx X) as [_ [V _]]. rewrite V.
  unfold lf_tr. radix_grid_round. change (-623)%Z with (-189 + -434)%Z.
  apply grid_mult; [ | now apply radix_horner_grid].
  radix_grid_round. change (-189)%Z with (-63 + -126)%Z. apply grid_mult; [exact Gx | ].
  radix_grid_round. change (-126)%Z with (-63 + -63)%Z. now apply grid_mult.
Qed.

Lemma radix_correction_grid x l : finite x -> finite l ->
  Rabs(B x)<=/32 -> Rabs(B l)<=1 -> on_grid (-63) (B x) -> on_grid (-63) (B l) ->
  on_grid (-623) (B (lf_correction x l)).
Proof.
  intros Fx Fl X L Gx Gl.
  destruct (fmul_p (-5) x l Fx Fl ltac:(lia)) as [Fc [Vc Ac]].
  - change (bpow radix2 (-5)) with (/32). rewrite Rabs_mult.
    pose proof (Rabs_pos (B x)); pose proof (Rabs_pos (B l)); nra.
  - destruct (lf_tail_ok x Fx X) as [Ft [Vt At]].
    destruct (fsub_bnd 1 0 (lf_tail x) (fmul x l) Ft Fc
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fu [Vu Au]].
    + unfold bnd. change (IZR 1*bpow radix2 0) with (1*1).
      change (bpow radix2 (-5)) with (/32) in Ac.
      apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra.
    + unfold lf_correction. rewrite Vu. radix_grid_round; apply grid_minus.
      * now apply radix_tail_grid.
      * rewrite Vc. radix_grid_round. apply (grid_le (-126)); [lia | ].
        change (-126)%Z with (-63 + -63)%Z. now apply grid_mult.
Qed.

Lemma radix_half_square_grid x : finite x -> /2^64<=Rabs(B x)<=/32 ->
  on_grid (-63) (B x) ->
  let '(h,l):=lf_half_square x in on_grid (-127) (B h) /\ on_grid (-127) (B l).
Proof.
  intros Fx X Gx. pose proof (lf_half_square_ok x Fx X) as S.
  destruct (lf_half_square x) as [h l]. destruct S as [_ [_ [D [V _]]]].
  apply radix_normalized_grid; [exact D | rewrite V].
  replace (-(B x*B x)/2) with (-(B x*B x) * bpow radix2 (-1)) by
    (change (bpow radix2 (-1)) with (/2); field).
  change (-127)%Z with (-126 + -1)%Z. apply grid_mult.
  - apply grid_opp. change (-126)%Z with (-63 + -63)%Z. now apply grid_mult.
  - exists 1%Z; ring.
Qed.

Lemma radix_polynomial_grid x l : finite x -> finite l ->
  /2^64<=Rabs(B x)<=/32 -> B x=rndF(B x+B l) -> Rabs(B l)<=lf_u*Rabs(B x) ->
  on_grid (-63) (B x) -> on_grid (-63) (B l) ->
  let '(h,t):=lf_polynomial x l in on_grid (-623) (B h) /\ on_grid (-623) (B t).
Proof.
  intros Fx Fl X D L Gx Gl.
  assert (Al : Rabs(B l)<=1) by (unfold lf_u in L; lra).
  assert (First : let '(h,t):=lf_first_sum x l in
    on_grid (-127) (B h) /\ on_grid (-127) (B t)).
  { pose proof (lf_half_square_ok x Fx X) as S.
    pose proof (radix_half_square_grid x Fx X Gx) as G.
    unfold lf_first_sum. destruct (lf_half_square x) as [h t].
    destruct S as [Fh [Ft [Dh [V [Ah At]]]]]. destruct G as [Gh Gt].
    apply radix_add_grid; try assumption; try lra.
    all: apply (grid_le (-63)); [lia | assumption]. }
  pose proof (lf_first_sum_ok x l Fx Fl X D L) as S.
  pose proof (lf_correction_ok x l Fx Fl ltac:(lra) Al
    (grid_le (-63) (-116) _ ltac:(lia) Gx)
    (grid_le (-63) (-232) _ ltac:(lia) Gl)) as C.
  unfold lf_polynomial. destruct (lf_first_sum x l) as [h t].
  destruct S as [Fh [Ft [Dh [Ah [At _]]]]]. destruct First as [Gh Gt].
  destruct C as [Fc [Ac _]].
  apply radix_add_f64_grid; try assumption; try lra.
  - apply (grid_le (-127)); [lia | exact Gh].
  - apply (grid_le (-127)); [lia | exact Gt].
  - now apply radix_correction_grid.
Qed.

Theorem radix_reduced_grid y i : (i<128)%nat -> finite y ->
  ln_lo i<=B y<ln_hi i -> on_grid (-53) (B y) ->
  let '(h,l):=lf_reduced_poly y i in on_grid (-623) (B h) /\ on_grid (-623) (B l).
Proof.
  intros I Fy Y Gy. pose proof (z_ok y i I Fy Y Gy) as Z.
  destruct (z_range y i I Y Gy) as [Pr [Az Gz]].
  unfold lf_reduced_poly. destruct (reduce_z y (ln_r i)) as [zh zl].
  destruct Z as [Fh [Fl [Vz [Dz [A [L Z]]]]]].
  assert (Gh : on_grid (-63) (B zh)) by (rewrite Dz,Vz; radix_grid_round; assumption).
  assert (Gl : on_grid (-63) (B zl)).
  { replace (B zl) with ((B y*B (ln_r i)-1)-B zh) by lra. now apply grid_minus. }
  destruct Z as [[Z0 L0] | Z].
  - pose proof (lf_polynomial_zero zh zl Fh Fl Z0 L0) as P.
    destruct (lf_polynomial zh zl) as [h l]. destruct P as [_ [_ [H T]]].
    rewrite H,T; split; apply grid_0.
  - assert (Zh : Rabs(B zh)<=/128) by
      (rewrite Dz; apply rnd_bound; [apply (fmt_pow (-7)); lia | exact A]).
    apply radix_polynomial_grid; try assumption.
    + split; [apply Rle_trans with (2:=Z); interval with (i_prec 100) | lra].
Qed.

Lemma radix_table_words_grid i : (i<128)%nat ->
  let '(h,l):=lf_neg_ln_r i in on_grid (-128) (B h) /\ on_grid (-128) (B l).
Proof.
  intros I. do 128 (destruct i as [|i];
    [unfold lf_neg_ln_r,lf_table; cbn [nth]; split;
      match goal with |- on_grid _ (B (b64_of_bits ?n)) =>
        let d := eval vm_compute in (dec n) in
        match d with Some (?m,?e) =>
          destruct (dec_ok n m e eq_refl) as [_ V]; rewrite V;
          apply (grid_le e); [lia | exists m; reflexivity]
        end
      end | ]). lia.
Qed.

Lemma radix_table_grid i : (i<128)%nat ->
  let '(h,l):=lf_table_pair i in on_grid (-128) (B h) /\ on_grid (-128) (B l).
Proof.
  intros I. pose proof (radix_table_words_grid i I) as G.
  pose proof (lf_table_all i I) as T. unfold lf_table_ok in T.
  unfold lf_table_pair. destruct (lf_neg_ln_r i) as [a b].
  destruct G as [Ga Gb]. destruct T as [Fa [Fb [Aa [Ab _]]]].
  pose proof (two_sum_ieee a b Fa Fb
    ltac:(apply Rle_trans with 1; [exact Aa | interval])
    ltac:(apply Rle_trans with (/2^53); [exact Ab | interval])) as S.
  destruct (two_sum64 a b) as [h l]. destruct S as [_ [_ [H V]]].
  apply radix_normalized_grid; [rewrite V; exact H | rewrite V; now apply grid_plus].
Qed.

Theorem radix_ln_y_grid y i : (i<128)%nat -> finite y ->
  ln_lo i<=B y<ln_hi i -> on_grid (-53) (B y) ->
  let '(h,l):=lf_ln_y y i in on_grid (-623) (B h) /\ on_grid (-623) (B l).
Proof.
  intros I Fy Y Gy.
  pose proof (radix_table_grid i I) as TG. pose proof (radix_reduced_grid y i I Fy Y Gy) as PG.
  pose proof (lf_table_pair_ok i I) as T. pose proof (lf_reduced_poly_ok y i I Fy Y Gy) as P.
  unfold lf_ln_y. destruct (lf_table_pair i) as [a b]; destruct (lf_reduced_poly y i) as [c d].
  destruct TG as [Ga Gb]; destruct PG as [Gc Gd].
  destruct T as [Fa [Fb [Da [Aa [Ab _]]]]]; destruct P as [Fc [Fd [Dc [Ac [Ad _]]]]].
  apply radix_add_grid; try assumption; try lra.
  all: apply (grid_le (-128)); [lia | assumption].
Qed.

Lemma radix_e_ln2_grid e : (Z.abs e<=1074)%Z ->
  let '(h,l):=lf_e_ln2 e in on_grid (-97) (B h) /\ on_grid (-97) (B l).
Proof.
  intros E. destruct (fe_ok e ltac:(lia)) as [Fe Ve].
  assert (Ae : Rabs(IZR e)<=1074) by (rewrite <-abs_IZR; apply IZR_le; exact E).
  assert (Ge : on_grid 0 (B (fe e))) by (rewrite Ve; exists e; change (bpow radix2 0) with 1; ring).
  assert (Gh : on_grid (-97) (B lf_lh)) by
    (rewrite lf_lh_val; apply (val_grid 6243314768164864 53 97); lia).
  assert (Gl : on_grid (-97) (B lf_ll)) by
    (rewrite lf_ll_val; apply (val_grid 8711806768342832 97 97); lia).
  assert (Ah : Rabs(B lf_lh)<=1) by (rewrite lf_lh_val; interval).
  assert (Al : Rabs(B lf_ll)<=1) by (rewrite lf_ll_val; interval).
  assert (Product : forall a, finite a -> Rabs(B a)<=1 -> on_grid (-97) (B a) ->
    finite (fmul (fe e) a) /\ Rabs(B (fmul (fe e) a))<=2048 /\ on_grid (-97) (B (fmul (fe e) a))).
  { intros a Fa A G. destruct (fmul_p 11 (fe e) a Fe Fa ltac:(lia)) as [F [V Bound]].
    - rewrite Ve,Rabs_mult. change (bpow radix2 11) with 2048.
      pose proof (Rabs_pos (IZR e)); pose proof (Rabs_pos (B a)); nra.
    - split; [exact F | split; [exact Bound | rewrite V; radix_grid_round]].
      change (-97)%Z with (0 + -97)%Z. now apply grid_mult. }
  destruct (Product lf_lh lf_lh_finite Ah Gh) as [Fh [Ph Qh]].
  destruct (Product lf_ll lf_ll_finite Al Gl) as [Fl [Pl Ql]].
  pose proof (two_sum_ieee (fmul (fe e) lf_lh) (fmul (fe e) lf_ll) Fh Fl
    ltac:(apply Rle_trans with 2048; [exact Ph | interval])
    ltac:(apply Rle_trans with 2048; [exact Pl | interval])) as S.
  unfold lf_e_ln2. destruct (two_sum64 (fmul (fe e) lf_lh) (fmul (fe e) lf_ll)) as [h l].
  destruct S as [_ [_ [H V]]].
  apply radix_normalized_grid; [rewrite V; exact H | rewrite V; now apply grid_plus].
Qed.

Theorem radix_value_grid e y i : (Z.abs e<=1074)%Z -> (i<128)%nat -> finite y ->
  ln_lo i<=B y<ln_hi i -> on_grid (-53) (B y) ->
  let '(h,l):=lf_value e y i in on_grid (-623) (B h) /\ on_grid (-623) (B l).
Proof.
  intros E I Fy Y Gy.
  pose proof (radix_e_ln2_grid e E) as EG. pose proof (radix_ln_y_grid y i I Fy Y Gy) as YG.
  pose proof (lf_e_ln2_ok e E) as EP. pose proof (lf_ln_y_ok y i I Fy Y Gy) as YP.
  unfold lf_value. destruct (lf_e_ln2 e) as [a b]; destruct (lf_ln_y y i) as [c d].
  destruct EG as [Ga Gb]; destruct YG as [Gc Gd].
  destruct EP as [Fa [Fb [Da [Aa [Ab _]]]]]; destruct YP as [Fc [Fd [Dc [Ac [Ad _]]]]].
  apply radix_add_grid; try assumption; try lra.
  all: apply (grid_le (-97)); [lia | assumption].
Qed.

Theorem radix_ln_fast_grid x : finite x -> 0<B x ->
  let '(h,l):=lf_ln_fast_value x in on_grid (-623) (B h) /\ on_grid (-623) (B l).
Proof.
  intros Fx Px. pose proof (reduce_ok x Fx Px) as R. unfold lf_ln_fast_value.
  destruct (reduce x) as [[[e i] y] r]. destruct R as [I [R [Fy [Y [Gy [V E]]]]]].
  apply radix_value_grid; try assumption; lia.
Qed.

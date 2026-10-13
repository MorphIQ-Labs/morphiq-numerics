(** Exact -x^2/2, including the residual word, on the small-path domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingTest.
From Interval Require Import Tactic.
Require Import ExpFast Ln1pLemmas LnFastTables.
Open Scope R_scope.
Definition lf_half_square x :=
 let '(p,l) := two_prod64 x x in
 two_sum64 (fmul lf_mhalf p) (fmul lf_mhalf l).
Lemma lf_half_word p : finite p -> on_grid (-232) (B p) -> Rabs (B p) <= 1 ->
 finite (fmul lf_mhalf p) /\ B (fmul lf_mhalf p) = -B p/2 /\ Rabs (B (fmul lf_mhalf p)) <= /2.
Proof.
 intros F G A. assert (H : B lf_mhalf = -/2) by (rewrite lf_mhalf_val; field).
 destruct (fmul_exact lf_mhalf p lf_mhalf_finite F) as [Fp V].
 - rewrite H. replace (-/2*B p) with ((-B p)*bpow radix2 (-1)) by (change (bpow radix2 (-1)) with (/2); ring).
   apply (scaled_fmt_grid _ (-232)); [apply generic_format_opp; apply B_fmt | apply grid_opp; exact G | lia].
 - rewrite H, Rabs_mult. replace (Rabs (-/2)) with (/2) by (rewrite Rabs_left; lra).
   apply Rle_lt_trans with (/2); [lra | interval with (i_prec 64)].
 - rewrite H in V. split; [exact Fp | split; [rewrite V; field | ]].
   rewrite V, Rabs_mult. replace (Rabs (-/2)) with (/2) by (rewrite Rabs_left; lra). lra.
Qed.
Theorem lf_half_square_ok x : finite x -> /2^64 <= Rabs (B x) <= /32 ->
 let '(h,l) := lf_half_square x in
 finite h /\ finite l /\ B h = rndF (B h+B l) /\ B h+B l = -(B x*B x)/2 /\
 Rabs (B h) <= /2048 /\ Rabs (B l) <= /1024.
Proof.
 intros F X. assert (A : Rabs (B x*B x) <= /1024).
 { rewrite Rabs_mult. nra. }
 assert (Dom : in_two_prod_domain (B x) (B x)).
 { right. rewrite Rabs_mult. apply Rle_trans with ((/2^64)*(/2^64)); [interval with (i_prec 64) | nra]. }
 pose proof (two_prod_ieee 0 0 x x F F ltac:(change (bpow radix2 0) with 1; lra)
  ltac:(change (bpow radix2 0) with 1; lra) ltac:(lia) ltac:(lia) ltac:(lia) Dom) as P.
 unfold lf_half_square. destruct (two_prod64 x x) as [p l]. destruct P as [Fp [Fl [Vp Vl]]].
 assert (Ap : Rabs (B p) <= /1024).
 { rewrite Vp. apply rnd_bound; [apply (fmt_pow (-10)); lia | exact A]. }
 assert (Al : Rabs (B l) <= /512).
 { replace (B l) with (B x*B x-B p) by lra. apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
 assert (Gx : on_grid (-116) (B x)).
 { replace (-116)%Z with (-64-52)%Z by reflexivity.
   apply (grid_fmt_bound (FLT_exp emin prec) (-64)); [unfold FLT_exp,prec; lia | apply B_fmt | right; apply Rle_trans with (/2^64); [interval with (i_prec 100) | exact (proj1 X)]]. }
 assert (Gxx : on_grid (-232) (B x*B x)) by (change (-232)%Z with (-116 + -116)%Z; apply grid_mult; exact Gx).
 assert (Gp : on_grid (-232) (B p)) by (rewrite Vp; apply grid_round; [exact _ | exact _ | exact Gxx]).
 assert (Gl : on_grid (-232) (B l)) by (replace (B l) with (B x*B x-B p) by lra; apply grid_minus; assumption).
 destruct (lf_half_word p Fp Gp ltac:(lra)) as [Fhp [Vhp Ahp]].
 destruct (lf_half_word l Fl Gl ltac:(lra)) as [Fhl [Vhl Ahl]].
 pose proof (two_sum_ieee (fmul lf_mhalf p) (fmul lf_mhalf l) Fhp Fhl
   ltac:(apply Rle_trans with (/2); [exact Ahp | interval with (i_prec 64)])
   ltac:(apply Rle_trans with (/2); [exact Ahl | interval with (i_prec 64)])) as S.
 destruct (two_sum64 (fmul lf_mhalf p) (fmul lf_mhalf l)) as [h t]. destruct S as [Fh [Ft [Vh Vt]]].
 rewrite Vhp, Vhl in Vh, Vt.
 assert (V : B h+B t = -(B x*B x)/2) by lra.
 assert (H : B h = rndF (B h+B t)) by (rewrite Vt; exact Vh).
 assert (Bh : Rabs (B h) <= /2048).
 { rewrite H, V. apply rnd_bound; [apply (fmt_pow (-11)); lia | ]. unfold Rdiv; rewrite Rabs_mult, Rabs_Ropp, (Rabs_pos_eq (/2)); lra. }
 assert (Bl : Rabs (B t) <= /1024).
 { replace (B t) with (-(B x*B x)/2-B h) by lra. apply Rle_trans with (1:=Rabs_triang _ _).
   rewrite Rabs_Ropp. unfold Rdiv; rewrite Rabs_mult, Rabs_Ropp, (Rabs_pos_eq (/2)); lra. }
 repeat split; assumption.
Qed.

(** Exact x^2/2, including the residual word, on the small-path domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingTest.
From Interval Require Import Tactic.
Require Import ExpFast Ln1pLemmas Expm1GeneralScale.
Open Scope R_scope.
Definition em_half_square x :=
 let '(p,l) := two_prod64 x x in
 two_sum64 (fmul c_half p) (fmul c_half l).
Lemma em_half_word p : finite p -> on_grid (-212) (B p) -> Rabs (B p) <= 1 ->
 finite (fmul c_half p) /\ B (fmul c_half p) = B p/2 /\ Rabs (B (fmul c_half p)) <= /2.
Proof.
 intros F G A. assert (H : B c_half = /2) by (rewrite c_half_val; field).
 destruct (fmul_exact c_half p c_half_finite F) as [Fp V].
 - rewrite H. replace (/2*B p) with (B p*bpow radix2 (-1)) by (change (bpow radix2 (-1)) with (/2); ring).
   apply (scaled_fmt_grid _ (-212)); [apply B_fmt | exact G | lia].
 - rewrite H, Rabs_mult, (Rabs_pos_eq (/2)) by lra.
   apply Rle_lt_trans with (/2); [lra | interval].
 - rewrite H in V. split; [exact Fp | split; [rewrite V; field | ]].
   rewrite V, Rabs_mult, (Rabs_pos_eq (/2)); lra.
Qed.
Theorem em_half_square_ok x : finite x -> /2^54 <= Rabs (B x) <= /32 ->
 let '(h,l) := em_half_square x in
 finite h /\ finite l /\ B h = rndF (B h+B l) /\ B h+B l = B x*B x/2 /\
 Rabs (B h) <= /2048 /\ Rabs (B l) <= /1024.
Proof.
 intros F X. assert (A : Rabs (B x*B x) <= /1024).
 { rewrite Rabs_mult. nra. }
 assert (Dom : in_two_prod_domain (B x) (B x)).
 { right. rewrite Rabs_mult. apply Rle_trans with ((/2^54)*(/2^54)); [interval | nra]. }
 pose proof (two_prod_ieee 0 0 x x F F ltac:(change (bpow radix2 0) with 1; lra)
  ltac:(change (bpow radix2 0) with 1; lra) ltac:(lia) ltac:(lia) ltac:(lia) Dom) as P.
 unfold em_half_square. destruct (two_prod64 x x) as [p l]. destruct P as [Fp [Fl [Vp Vl]]].
 assert (Ap : Rabs (B p) <= /1024).
 { rewrite Vp. apply rnd_bound; [apply (fmt_pow (-10)); lia | exact A]. }
 assert (Al : Rabs (B l) <= /512).
 { replace (B l) with (B x*B x-B p) by lra. apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
 assert (Gx : on_grid (-106) (B x)).
 { replace (-106)%Z with (-54-52)%Z by reflexivity.
   apply (grid_fmt_bound (FLT_exp emin prec) (-54)); [unfold FLT_exp,prec; lia | apply B_fmt | right; apply Rle_trans with (/2^54); [interval with (i_prec 100) | exact (proj1 X)]]. }
 assert (Gxx : on_grid (-212) (B x*B x)) by (change (-212)%Z with (-106 + -106)%Z; apply grid_mult; exact Gx).
 assert (Gp : on_grid (-212) (B p)) by (rewrite Vp; apply grid_round; [exact _ | exact _ | exact Gxx]).
 assert (Gl : on_grid (-212) (B l)) by (replace (B l) with (B x*B x-B p) by lra; apply grid_minus; assumption).
 destruct (em_half_word p Fp Gp ltac:(lra)) as [Fhp [Vhp Ahp]].
 destruct (em_half_word l Fl Gl ltac:(lra)) as [Fhl [Vhl Ahl]].
 pose proof (two_sum_ieee (fmul c_half p) (fmul c_half l) Fhp Fhl
   ltac:(apply Rle_trans with (/2); [exact Ahp | interval])
   ltac:(apply Rle_trans with (/2); [exact Ahl | interval])) as S.
 destruct (two_sum64 (fmul c_half p) (fmul c_half l)) as [h t]. destruct S as [Fh [Ft [Vh Vt]]].
 rewrite Vhp, Vhl in Vh, Vt.
 assert (V : B h+B t = B x*B x/2) by lra.
 assert (H : B h = rndF (B h+B t)) by (rewrite Vt; exact Vh).
 assert (Bh : Rabs (B h) <= /2048).
 { rewrite H, V. apply rnd_bound; [apply (fmt_pow (-11)); lia | ]. unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/2)); lra. }
 assert (Bl : Rabs (B t) <= /1024).
 { replace (B t) with (B x*B x/2-B h) by lra. apply Rle_trans with (1:=Rabs_triang _ _).
   rewrite Rabs_Ropp. unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/2)); lra. }
 repeat split; assumption.
Qed.

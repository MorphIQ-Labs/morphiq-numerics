(** The folded binary64 normal-pair path and its composed absolute bound.
    Inputs are the shared exact open uniform and rounded folded angle. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Sqrt Encodings
 Grid RoundingGaps RoundingCore RoundingConstant RoundingTest.
From Interval Require Import Tactic.
Require Import StageGappa FastLn FastRandomAngular FastRandomBound.
Open Scope R_scope.

Definition bm_neg_two : f64 := b64_of_bits 13835058055282163712.
Lemma bm_neg_two_ok : finite bm_neg_two /\ B bm_neg_two = -2.
Proof.
 split;[reflexivity|]. unfold bm_neg_two.
 rewrite (bits_val 13835058055282163712 true 4503599627370496 51 eq_refl).
 cbn. field.
Qed.

Definition bm_radius64 u := fsqrt (fmul bm_neg_two (fast_ln_public64 u)).
Definition bm_pair64 u phi :=
 let r:=bm_radius64 u in
 (fmul r (bm_cos64 phi),fmul r (bm_sin64 phi)).
Definition bm_strong_component u angle :=
 rndF (rndF (sqrt(-2*rndF(ln(B u)))) * rndF angle).

Lemma bm_round16 x : Rabs x<=16 -> Rabs(rndF x-x)<=/2^50.
Proof.
 intros X. pose proof (rnd_err_below x 4 ltac:(lia)
   ltac:(change (bpow radix2 4) with 16;exact X)) as E.
 eapply Rle_trans;[exact E|]. change (bpow radix2 (-50)<=/2^50).
 bpow_num;interval with (i_prec 100).
Qed.
Lemma bm_round1 x : Rabs x<=1 -> Rabs(rndF x-x)<=bm_unit.
Proof.
 intros X. pose proof (rnd_err_below x 0 ltac:(lia)
   ltac:(change (bpow radix2 0) with 1;exact X)) as E.
 eapply Rle_trans;[exact E|]. change (bpow radix2 (-54)<=bm_unit).
 bpow_num;unfold bm_unit;interval with (i_prec 100).
Qed.

Lemma bm_uniform_log_range u : bm_unit<=B u<=1-bm_unit ->
 bm_unit<= -ln(B u)<=37.
Proof.
 intros U;unfold bm_unit in *.
 interval with (i_prec 200).
Qed.

Lemma bm_reference_log L : bm_unit<=L<=37 ->
 Rabs(-rndF(-L)-L)<=bm_unit*L.
Proof.
 intros Lr. assert (N : bpow radix2 (-1022)<=Rabs(-L)).
 { rewrite Rabs_Ropp,Rabs_pos_eq by (unfold bm_unit in Lr;lra).
   apply Rle_trans with (bpow radix2 (-53));[apply bpow_le;lia|].
   bpow_num;unfold bm_unit in Lr;lra. }
 pose proof (rnd_rel (-L) N) as E. rewrite RNE_rndF in E.
 replace (-rndF(-L)-L) with (-(rndF(-L)-(-L))) by ring.
 rewrite Rabs_Ropp. rewrite (Rabs_Ropp L),(Rabs_pos_eq L) in E by (unfold bm_unit in Lr;lra).
 bpow_num_all;unfold bm_unit;lra.
Qed.

Lemma bm_twice_exact l : finite l -> Rabs(B l)<=38 ->
 finite (fmul bm_neg_two l) /\ B(fmul bm_neg_two l)= -2*B l.
Proof.
 intros Fl L. destruct bm_neg_two_ok as [F2 V2].
 assert (G : on_grid (-1074) (-B l)).
 { apply grid_opp. apply grid_le with (cexp radix2 fexp64 (B l)).
   - unfold cexp,fexp64,FLT_exp;lia.
   - apply grid_fmt,B_fmt. }
 assert (Fmt : fmtF (-2*B l)).
 { replace (-2*B l) with ((-B l)*bpow radix2 1) by (change (bpow radix2 1) with 2;ring).
   apply (scaled_fmt_grid _ (-1074));[apply generic_format_opp,B_fmt|exact G|lia]. }
 destruct (fmul_ok 1 7 bm_neg_two l F2 Fl ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as [Fp Vp].
 { unfold bnd;rewrite V2,Rabs_mult. bpow_num;cbn [IZR]. rewrite (Rabs_left (-2)) by lra. lra. }
 split;[exact Fp|]. rewrite Vp,V2,round_generic;auto with typeclass_instances.
Qed.

Theorem bm_radius_ok u : finite u -> bm_unit<=B u<=1-bm_unit ->
 let a:= -B(fast_ln_public64 u) in
 finite (bm_radius64 u) /\ Rabs(B(bm_radius64 u)-sqrt(2*a))<=/2^50 /\
 Rabs(B(bm_radius64 u))<=9.
Proof.
 intros Fu U a. pose proof (bm_uniform_log_range u U) as Lr.
 assert (Up : 0<B u) by (unfold bm_unit in U;lra).
 destruct (fast_ln_public_ok u Fu Up) as [Fl Log].
 set (L:= -ln(B u)) in *.
 assert (A : Rabs(a-L)<=bm_unit*L+bm_log_floor).
 { unfold a,L. replace (-B(fast_ln_public64 u)- -ln(B u)) with
     (-(B(fast_ln_public64 u)-ln(B u))) by ring.
   rewrite Rabs_Ropp. rewrite (Rabs_left (ln(B u))) in Log by (unfold L in Lr;unfold bm_unit in Lr;lra).
   bpow_num_all;unfold bm_unit,bm_log_floor;lra. }
 destruct (bm_log_ranges L a L Lr A) as [[Al Au] _].
 { rewrite Rminus_diag_eq,Rabs_R0 by reflexivity. unfold bm_unit in Lr |- *;nra. }
 assert (Ar : 0<=a<=38) by (unfold bm_unit in Lr;nra).
 assert (Abs : Rabs(B(fast_ln_public64 u))<=38).
 { replace (B(fast_ln_public64 u)) with (-a) by (unfold a;ring).
   rewrite Rabs_Ropp,Rabs_pos_eq by lra;lra. }
 destruct (bm_twice_exact _ Fl Abs) as [Fp Vp].
 unfold bm_radius64. destruct (sqrt_ieee (fmul bm_neg_two (fast_ln_public64 u))) as [V Fin].
 assert (P : B(fmul bm_neg_two (fast_ln_public64 u))=2*a) by (rewrite Vp;unfold a;ring).
 rewrite P in V,Fin.
 assert (Fr : finite(fsqrt(fmul bm_neg_two (fast_ln_public64 u)))) by (apply Fin;split;[exact Fp|nra]).
 assert (R : 0<=sqrt(2*a)<=9- /2^50) by (interval with (i_prec 100)).
 assert (Mag : Rabs(sqrt(2*a))<=16) by (rewrite Rabs_pos_eq;lra).
 pose proof (bm_round16 (sqrt(2*a)) Mag) as Round.
 split;[exact Fr|]. rewrite V. split;[exact Round|]. apply Rabs_le_inv in Round. apply Rabs_le;lra.
Qed.

Lemma bm_reference_radius L : bm_unit<=L<=37 ->
 let b:= -rndF(-L) in
 Rabs(rndF(sqrt(2*b))-sqrt(2*b))<=/2^50 /\ Rabs(rndF(sqrt(2*b)))<=9.
Proof.
 intros Lr b. pose proof (bm_reference_log L Lr) as Log;fold b in Log.
 destruct (bm_log_ranges L L b Lr) as [_ [Bl Bu]].
 { rewrite Rminus_diag_eq,Rabs_R0 by reflexivity;unfold bm_unit,bm_log_floor in Lr |- *;nra. }
 { exact Log. }
 assert (Br:0<=b<=38) by (unfold bm_unit in Lr;nra).
 assert (R:0<=sqrt(2*b)<=9-/2^50) by (interval with (i_prec 100)).
 assert (Mag:Rabs(sqrt(2*b))<=16) by (rewrite Rabs_pos_eq;lra).
 pose proof (bm_round16 (sqrt(2*b)) Mag) as Round.
 split;[exact Round|]. apply Rabs_le_inv in Round. apply Rabs_le;lra.
Qed.

Theorem bm_component_ok u phi angle kernel : finite u -> bm_unit<=B u<=1-bm_unit ->
 finite phi -> 0<=B phi<=bm_limit -> Rabs angle<=1 ->
 finite kernel -> Rabs(B kernel-angle)<=/2^44 ->
 finite(fmul (bm_radius64 u) kernel) /\
 Rabs(B(fmul (bm_radius64 u) kernel)-bm_strong_component u angle)<=/2^38.
Proof.
 intros Fu U Fphi Phi Angle Fk K.
 pose proof (bm_uniform_log_range u U) as Lr.
 set (L:= -ln(B u)) in *.
 assert (Up:0<B u) by (unfold bm_unit in U;lra).
 destruct (fast_ln_public_ok u Fu Up) as [Fl Log].
 set (a:= -B(fast_ln_public64 u)).
 assert (A:Rabs(a-L)<=bm_unit*L+bm_log_floor).
 { unfold a,L. replace (-B(fast_ln_public64 u)- -ln(B u)) with
    (-(B(fast_ln_public64 u)-ln(B u))) by ring. rewrite Rabs_Ropp.
   rewrite (Rabs_left (ln(B u))) in Log by (unfold L in Lr;unfold bm_unit in Lr;lra). bpow_num_all;unfold bm_unit,bm_log_floor;lra. }
 pose proof (bm_reference_log L Lr) as RefLog.
 destruct (bm_radius_ok u Fu U) as [Fr [Rerror Rrange]]. fold a in Rerror.
 destruct (bm_reference_radius L Lr) as [Serror Srange].
 assert (Cerror:Rabs(rndF angle-angle)<=bm_unit).
 { apply bm_round1;exact Angle. }
 assert (Krange:Rabs(B kernel)<=1+/2^44).
 { replace (B kernel) with ((B kernel-angle)+angle) by ring.
   eapply Rle_trans;[apply Rabs_triang|];lra. }
 assert (Pmag:Rabs(B(bm_radius64 u)*B kernel)<=16).
 { rewrite Rabs_mult. eapply Rle_trans with (9*(1+/2^44)).
   - apply Rmult_le_compat;try apply Rabs_pos;assumption.
   - interval with(i_prec 80). }
 destruct (fmul16 _ _ Fr Fk Pmag) as [Fp Vp].
 pose proof (bm_round16 (B(bm_radius64 u)*B kernel) Pmag) as Yf.
 assert (Cs:Rabs(rndF angle)<=1+bm_unit).
 { replace (rndF angle) with ((rndF angle-angle)+angle) by ring.
   eapply Rle_trans;[apply Rabs_triang|];lra. }
 assert (Qmag:Rabs(rndF(sqrt(2*(-rndF(-L))))*rndF angle)<=16).
 { rewrite Rabs_mult. eapply Rle_trans with (9*(1+bm_unit)).
   - apply Rmult_le_compat;try apply Rabs_pos;assumption.
   - unfold bm_unit;interval with(i_prec 80). }
 pose proof (bm_round16 (rndF(sqrt(2*(-rndF(-L))))*rndF angle) Qmag) as Ys.
 split;[exact Fp|]. rewrite Vp. unfold bm_strong_component.
 replace (-2*rndF(ln(B u))) with (2*(-rndF(-L))) by (unfold L;rewrite Ropp_involutive;ring).
 eapply bm_output_bound with (L:=L) (a:=a) (b:= -rndF(-L))
   (rf:=B(bm_radius64 u)) (rs:=rndF(sqrt(2*(-rndF(-L))))) (cf:=B kernel)
   (cs:=rndF angle) (exact_angle:=angle);eassumption.
Qed.

Theorem bm_pair_ok u phi : finite u -> bm_unit<=B u<=1-bm_unit ->
 finite phi -> 0<=B phi<=bm_limit ->
 let '(c,s):=bm_pair64 u phi in
 finite c /\ finite s /\
 Rabs(B c-bm_strong_component u (cos(B phi)))<=/2^38 /\
 Rabs(B s-bm_strong_component u (sin(B phi)))<=/2^38.
Proof.
 intros Fu U Fp P. destruct (bm_sin_ok phi Fp P) as [Fs S].
 destruct (bm_cos_ok phi Fp P) as [Fc C].
 destruct (bm_component_ok u phi (sin(B phi)) (bm_sin64 phi) Fu U Fp P) as [Fsv Sv].
 { apply Rabs_le;apply SIN_bound. } { exact Fs. } { exact S. }
 destruct (bm_component_ok u phi (cos(B phi)) (bm_cos64 phi) Fu U Fp P) as [Fcv Cv].
 { apply Rabs_le;apply COS_bound. } { exact Fc. } { exact C. }
 unfold bm_pair64. repeat split;assumption.
Qed.

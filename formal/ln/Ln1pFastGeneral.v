(** General ln_1p fallback: absolute division error covers gradual underflow. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingTest.
From Interval Require Import Tactic.
Require Import LnAccurate LnFastValue LnFastCompose LnFastAdd Ln1pLemmas Ln1pApprox LnTableCheck.
Open Scope R_scope.
Lemma lf_small_round_error q : Rabs q<=/2^52 -> Rabs(rndF q-q)<=/2^104.
Proof.
 intros Q. destruct (Req_dec q 0) as [-> | N].
 - rewrite round_0 by exact _. rewrite Rminus_0_r,Rabs_R0; interval with (i_prec 140).
 - apply Rle_trans with (/2*ulp radix2 (FLT_exp emin prec) q); [apply error_le_half_ulp; exact _ | ].
   rewrite ulp_neq_0 by exact N. unfold cexp.
   assert (M : (mag radix2 q<= -51)%Z).
   { apply mag_le_bpow; [exact N | apply Rle_lt_trans with (1:=Q); interval with (i_prec 100)]. }
   apply Rle_trans with (/2*bpow radix2 (-104)).
   + apply Rmult_le_compat_l; [lra | apply bpow_le; unfold FLT_exp,emin,prec; lia].
   + interval with (i_prec 140).
Qed.
Lemma lf_log_general_away x : -1<x -> /128<=Rabs x -> /256<=Rabs(ln(1+x)).
Proof.
 intros X A. destruct (Rle_or_lt 0 x) as [P | N].
 - rewrite Rabs_pos_eq in A by lra. pose proof (ln_le_mono (1+/128) (1+x) ltac:(lra) ltac:(lra)).
   assert (/256<=ln(1+/128)) by interval with (i_prec 100). rewrite Rabs_pos_eq; lra.
 - rewrite Rabs_left in A by lra. pose proof (ln_le_mono (1+x) (1-/128) ltac:(lra) ltac:(lra)).
   assert (ln(1-/128)<= -/256) by interval with (i_prec 100). rewrite Rabs_left; lra.
Qed.
Definition lf_ln1p_general_value x := let '(h,l):=split x in let '(a,b):=lf_ln_fast_value h in add_f64_64 a b (fdiv l h).
Theorem lf_ln1p_general_ok x : finite x -> -1<B x -> /128<=Rabs(B x) ->
 let '(h,l):=lf_ln1p_general_value x in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=2048 /\ Rabs(B l)<=4096 /\
 Rabs(B h+B l-ln(1+B x))<=/2^63*Rabs(ln(1+B x)).
Proof.
 intros Fx X Ax. pose proof (split_ok x Fx X) as S. unfold lf_ln1p_general_value.
 destruct (split x) as [h l]. destruct S as [Fh [Fl [Sum [Ph [Lo [Hm Hg]]]]]].
 set (q:=B l/B h). set (v:=ln(1+B x)).
 assert (Aq : Rabs q<=/2^52).
 { unfold q. apply ratio_bound; [rewrite (Rabs_pos_eq (B h)); lra | rewrite (Rabs_pos_eq (B h)) by lra].
   apply Rle_trans with (1:=Lo). apply Rmult_le_compat_r; [lra | interval with (i_prec 100)]. }
 assert (Lq : Rabs(ln(1+q)-q)<=/2^102).
 { pose proof (ln1p_linear q ltac:(assert (/2^52<=/2) by interval with (i_prec 100); lra)) as E.
   apply Rle_trans with (1:=E). assert (A: -(/2^52)<=q<=/2^52) by (apply Rabs_le_inv; exact Aq).
   interval with (i_prec 160). }
 assert (Dq : Rabs(ln(1+q))<=/2^51).
 { pose proof (Rabs_triang_inv (ln(1+q)) q). assert (/2^52+/2^102<=/2^51) by interval with (i_prec 160); lra. }
 assert (Log : ln(B h)+ln(1+q)=v).
 { unfold v. rewrite <-ln_mult; [f_equal; unfold q; field_simplify; lra | exact Ph | ].
   apply Rabs_le_inv in Aq. assert (/2^52<1) by interval with (i_prec 100); lra. }
 assert (Av : /256<=Rabs v) by (apply lf_log_general_away; assumption).
 assert (V0 : v<>0) by (intro Z; rewrite Z,Rabs_R0 in Av; lra).
 assert (Delta : Rabs(ln(1+q))<=/2^43*Rabs v).
 { apply Rle_trans with (1:=Dq). apply Rle_trans with ((/2^43)*(/256)); [interval with (i_prec 140) | apply Rmult_le_compat_l; [interval with (i_prec 100) | exact Av]]. }
 assert (Lh : Rabs(ln(B h))<=(1+/2^43)*Rabs v).
 { replace (ln(B h)) with (v-ln(1+q)) by lra. apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
 destruct (fdiv_bnd 1 (-52) l h Fl ltac:(lra) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fd [Vd Ad]].
 - unfold bnd. change (bpow radix2 (-52)) with (/4503599627370496). apply Rle_trans with (1:=Aq); interval with (i_prec 100).
 - fold q in Vd. unfold bnd in Ad. change (bpow radix2 (-52)) with (/4503599627370496) in Ad.
   assert (Ed : Rabs(B (fdiv l h)-ln(1+q))<=/2^93*Rabs v).
   { replace (B (fdiv l h)-ln(1+q)) with ((B (fdiv l h)-q)+(q-ln(1+q))) by ring.
     apply Rle_trans with (1:=Rabs_triang _ _). rewrite (Rabs_minus_sym q (ln(1+q))). rewrite Vd.
     pose proof (lf_small_round_error q Aq). apply Rle_trans with (/2^104+/2^102); [lra | ].
     apply Rle_trans with ((/2^93)*(/256)); [interval with (i_prec 180) | apply Rmult_le_compat_l; [interval with (i_prec 120) | exact Av]]. }
   pose proof (lf_ln_fast_value_ok h Fh Ph) as FP. destruct (lf_ln_fast_value h) as [a b].
   destruct FP as [Fa [Fb [Dw [Aa [Ab E]]]]].
   set (eps:=(/2^64)*(1+/2^43)+/2^93).
   assert (Ep : 0<=eps<=/100) by (unfold eps; split; interval with (i_prec 180)).
   assert (ES : Rabs(B a+B b+B (fdiv l h)-v)<=eps*Rabs v).
   { replace (B a+B b+B (fdiv l h)-v) with ((B a+B b-ln(B h))+(B (fdiv l h)-ln(1+q))) by lra.
     apply Rle_trans with (1:=Rabs_triang _ _). assert (0<=/2^64) by interval with (i_prec 100). unfold eps; nra. }
   assert (N : B a+B b+B (fdiv l h)<>0).
   { intro Z. rewrite Z,Rminus_0_l,Rabs_Ropp in ES. pose proof (Rabs_pos_lt v V0); nra. }
   assert (Big : forall t, Rabs t<=2048 -> Rabs t<=bpow radix2 1018).
   { intros t T; apply Rle_trans with 2048; [exact T | interval with (i_prec 80)]. }
   pose proof (add_f64_ieee a b (fdiv l h) Fa Fb Fd Dw (Big (B a) ltac:(lra)) (Big (B b) Ab) (Big (B (fdiv l h)) ltac:(lra))) as A.
   destruct (add_f64_64_ok 2048 0 a b (fdiv l h) Fa Fb Fd
    ltac:(unfold bnd; change (IZR 2048*bpow radix2 0) with (2048*1); lra)
    ltac:(unfold bnd; change (IZR 2048*bpow radix2 0) with (2048*1); lra)
    ltac:(unfold bnd; change (IZR 2048*bpow radix2 0) with (2048*1); lra)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Eq]].
   pose proof (add_f64_dw (B a) (B b) (B (fdiv l h)) (B_fmt a) (B_fmt b) (B_fmt _) Dw) as Dh.
   rewrite <-Eq in Dh. destruct (add_f64_64 a b (fdiv l h)) as [s t]. cbn [fst snd] in Dh.
   destruct A as [Fs [Ft E2]].
   set (er:=(B s+B t-(B a+B b+B (fdiv l h)))/(B a+B b+B (fdiv l h))).
   assert (Er : Rabs er<=776/2^114) by (apply Rle_trans with (1:=E2); unfold prec; interval with (i_prec 180)).
   assert (Vr : B s+B t=(B a+B b+B (fdiv l h))*(1+er)) by (unfold er; field; exact N).
   pose proof (lf_rounded_sum _ _ _ eps er (proj1 Ep) ES Er Vr) as Bnd.
   assert (Bound : Rabs(B s+B t-v)<=/2^63*Rabs v).
   { apply Rle_trans with (1:=Bnd). apply Rmult_le_compat_r; [apply Rabs_pos | unfold eps; interval with (i_prec 200)]. }
   assert (As : Rabs(B s+B t)<=2048).
   { assert (Ap : Rabs(B a+B b)<=1025).
     { pose proof (lf_low_bound (B a) (B b) (B_fmt a) (B_fmt b) Dw). pose proof (Rabs_triang (B a) (B b)). unfold lf_u in H; lra. }
     assert (Er' : Rabs er<=/100) by (apply Rle_trans with (1:=Er); interval with (i_prec 180)).
     rewrite Vr,Rabs_mult. pose proof (Rabs_triang (B a+B b) (B (fdiv l h))).
     pose proof (Rabs_triang 1 er). rewrite Rabs_R1 in H0.
     pose proof (Rabs_pos (B a+B b+B (fdiv l h))). pose proof (Rabs_pos (1+er)); nra. }
   assert (Hs : Rabs(B s)<=2048) by (rewrite Dh; apply rnd_bound; [apply (fmt_pow 11); lia | exact As]).
   assert (Lt : Rabs(B t)<=4096).
   { replace (B t) with ((B s+B t)-B s) by ring. apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
   repeat split; assumption.
Qed.

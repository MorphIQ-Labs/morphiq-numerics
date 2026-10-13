(** The executable shared polynomial and its total relative error. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid.
From Interval Require Import Tactic.
Require Import ExpFast LnFastTables LnFastAdd LnFastSum LnFastPoly LnFastApprox
 LnFastCertificates LnFastCorrection Ln1pLemmas Ln1pApprox StageGappa.
Open Scope R_scope.
Definition lf_polynomial x l := let '(h,t) := lf_first_sum x l in add_f64_64 h t (lf_correction x l).
Theorem lf_polynomial_ok x l : finite x -> finite l ->
 /2^64<=Rabs(B x)<=0.0078126 -> Rabs(B x+B l)<=0.0078126 ->
 B x=rndF(B x+B l) -> Rabs(B l)<=lf_u*Rabs(B x) -> on_grid (-232) (B l) ->
 let '(h,t) := lf_polynomial x l in
 finite h /\ finite t /\ B h=rndF(B h+B t) /\
 Rabs(B h+B t-ln(1+B x+B l))<=3/2^66*Rabs(ln(1+B x+B l)).
Proof.
 intros Fx Fl X Z Dx L Gl.
 assert (X0 : B x<>0) by (intro H; rewrite H,Rabs_R0 in X; assert (0</2^64) by interval with (i_prec 100); lra).
 set (dl:=B l/B x).
 assert (Dl : Rabs dl<=lf_u) by (apply ratio_bound; [apply Rabs_pos_lt; exact X0 | exact L]).
 assert (Vl : B l=B x*dl) by (unfold dl; field; exact X0).
 assert (Gx : on_grid (-116) (B x)).
 { change (-116)%Z with (-64-52)%Z. apply (grid_fmt_bound (FLT_exp emin prec) (-64)); [unfold FLT_exp,prec; lia | apply B_fmt | right].
   apply Rle_trans with (/2^64); [interval with (i_prec 100) | tauto]. }
 assert (XA : /2^64<=Rabs(B x)<=/32) by lra.
 assert (Alow : Rabs(B l)<=1) by (unfold lf_u in L; lra).
 pose proof (lf_first_sum_ok x l Fx Fl XA Dx L) as S.
 unfold lf_polynomial. destruct (lf_first_sum x l) as [a b]. destruct S as [Fa [Fb [Dw [Aa [Ab [d1 [Ed1 V1]]]]]]].
 destruct (lf_correction_ok x l Fx Fl ltac:(lra) Alow Gx Gl) as [Fu [Au [ec [eu [EC [EU VU]]]]]].
 destruct (lf_tail_ok x Fx ltac:(lra)) as [Ft [Vt At]].
 assert (Rx : rn(B x)=B x) by (change (rndF(B x)=B x); apply round_generic; auto with typeclass_instances; apply B_fmt).
 pose proof (lf_tail_certificate (B x) Rx X) as Et.
 pose proof (lf_w_range (B x) (proj2 X)) as W.
 set (T:=B x*B x*B x*lf_w(B x)) in *.
 assert (T0 : T<>0) by (unfold T; repeat apply Rmult_integral_contrapositive_currified; try exact X0; lra).
 set (et:=(B (lf_tail x)-T)/T).
 assert (ET : Rabs et<=/2^50) by (unfold et; rewrite Vt; exact Et).
 assert (VT : B (lf_tail x)=T*(1+et)) by (unfold et; field; exact T0).
 set (z:=B x+B l) in *.
 assert (Z0 : z<>0).
 { intro H. assert (Rabs(B x)=Rabs(B l)) by (unfold z in H; replace (B x) with (-B l) by lra; apply Rabs_Ropp).
   pose proof (Rabs_pos_lt (B x) X0); unfold lf_u in L; lra. }
 pose proof (lf_polynomial_bound z Z) as Ep.
 pose proof (lf_w_range z Z) as Wz.
 set (Tz:=z*z*z*lf_w z) in *.
 assert (Tz0 : Tz<>0) by (unfold Tz; repeat apply Rmult_integral_contrapositive_currified; try exact Z0; lra).
 set (al:=(ln(1+z)-z+z*z/2-Tz)/Tz).
 assert (AL : Rabs al<=535/2^63) by (apply ratio_bound; [apply Rabs_pos_lt; exact Tz0 | exact Ep]).
 assert (VL : ln(1+z)=z-z*z/2+Tz+al*Tz) by (unfold al; field; exact Tz0).
 assert (XR : -0.0078126<=B x<=0.0078126) by (pose proof (Rabs_le_inv _ _ (proj2 X)); lra).
 assert (Small : forall v e, Rabs v<=e -> e<=0.001 -> -0.001<=v<=0.001).
 { intros v e H E. apply Rabs_le_inv in H; lra. }
 pose proof (Small _ _ Dl ltac:(unfold lf_u; lra)) as Dlr.
 pose proof (Small _ _ Ed1 ltac:(interval with (i_prec 140))) as D1r.
 pose proof (Small _ _ ET ltac:(interval with (i_prec 100))) as ETr.
 pose proof (Small _ _ EC ltac:(unfold lf_u; lra)) as ECr.
 pose proof (Small _ _ EU ltac:(unfold lf_u; lra)) as EUr.
 assert (N : B a+B b+B (lf_correction x l)<>0).
 { rewrite V1,VU,VT. unfold z,T. rewrite Vl.
   replace ((B x+B x*dl-B x*B x/2)*(1+d1)+(B x*B x*B x*lf_w(B x)*(1+et)-B x*(B x*dl)*(1+ec))*(1+eu))
    with (B x*((1+dl-B x/2)*(1+d1)+(B x*B x*lf_w(B x)*(1+et)-B x*dl*(1+ec))*(1+eu))) by field.
   apply Rmult_integral_contrapositive_currified; [exact X0 | ].
   assert (0<(1+dl-B x/2)*(1+d1)+(B x*B x*lf_w(B x)*(1+et)-B x*dl*(1+ec))*(1+eu)) by interval with (i_prec 100).
   lra. }
 assert (Big : forall v, Rabs v<=2 -> Rabs v<=bpow radix2 1018).
 { intros v H; apply Rle_trans with 2; [exact H | interval with (i_prec 80)]. }
 pose proof (add_f64_ieee a b (lf_correction x l) Fa Fb Fu Dw (Big (B a) ltac:(lra)) (Big (B b) Ab) (Big (B (lf_correction x l)) ltac:(lra))) as A.
 destruct (add_f64_64_ok 2 0 a b (lf_correction x l) Fa Fb Fu
  ltac:(unfold bnd; change (IZR 2*bpow radix2 0) with (2*1); lra)
  ltac:(unfold bnd; change (IZR 2*bpow radix2 0) with (2*1); lra)
  ltac:(unfold bnd; change (IZR 2*bpow radix2 0) with (2*1); lra)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Eq]].
 pose proof (add_f64_dw (B a) (B b) (B (lf_correction x l)) (B_fmt a) (B_fmt b) (B_fmt _) Dw) as Dh.
 rewrite <-Eq in Dh. destruct (add_f64_64 a b (lf_correction x l)) as [h t]. cbn [fst snd] in Dh.
 destruct A as [Fh [Ft' E2]].
 set (d2:=(B h+B t-(B a+B b+B (lf_correction x l)))/(B a+B b+B (lf_correction x l))).
 assert (ED2 : Rabs d2<=/2^105) by (apply Rle_trans with (1:=E2); unfold prec; interval with (i_prec 140)).
 assert (V2 : B h+B t=(B a+B b+B (lf_correction x l))*(1+d2)) by (unfold d2; field; exact N).
 pose proof (lf_p_certificate (B x) dl et ec eu al d1 d2 X ltac:(apply Rle_trans with (1:=Dl); unfold lf_u; interval with (i_prec 100)) ET
   ltac:(apply Rle_trans with (1:=EC); unfold lf_u; interval with (i_prec 100)) ltac:(apply Rle_trans with (1:=EU); unfold lf_u; interval with (i_prec 100)) AL Ed1 ED2) as C.
 cbv zeta in C. rewrite <-Vl in C. fold z T Tz in C. rewrite <-VL in C.
 rewrite <-V1,<-VT,<-VU,<-V2 in C.
 assert (LN0 : ln(1+z)<>0).
 { intro H. apply Z0.  apply (f_equal exp) in H. rewrite exp_ln in H by (apply Rabs_le_inv in Z; lra). rewrite exp_0 in H; lra. }
 assert (E : Rabs(B h+B t-ln(1+z))<=3/2^66*Rabs(ln(1+z))).
 { replace (B h+B t-ln(1+z)) with (((B h+B t-ln(1+z))/ln(1+z))*ln(1+z)) by (field; exact LN0).
   rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | exact C]. }
 replace (1+B x+B l) with (1+z) by (unfold z; ring).
 repeat split; assumption.
Qed.

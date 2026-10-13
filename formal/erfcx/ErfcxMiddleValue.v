(** Composition of the IEEE middle-tail arithmetic. The analytic approximation
    and 1/sqrt(pi) error are explicit mathematical hypotheses here. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Eft.
From Gappa Require Import Gappa_library.

Require Import StageGappa ErfcxReciprocal ErfcxSquare ErfcxEntryTables ErfcxMiddlePolynomial ErfcxProduct.
Require erfcx_middle_composition.
Open Scope R_scope.

Lemma cs_range : /2 <= B cs <= 5/8 /\ 9/16 <= B cs /\
 - /2^51 <= B csl/B cs <= /2^51.
Proof.
 destruct cs_ok as [_ [C _]]. destruct csl_ok as [_ [L _]]. rewrite C,L.
 unfold cs_r,csl_r,float2R,F2R. simpl. bpow_num. repeat split; lra.
Qed.

Definition middle64 x : f64*f64 :=
 let '(yh,yl) := reciprocal64 x in
 let '(th,tl) := square64 yh yl in
 let '(w,wl) := correction64 th tl in
 let '(zh,zl) := product64 cs csl yh yl in
 product64 zh zl w wl.

Lemma low_sum_positive h l : 0<h -> - /2^51 <= l/h <= /2^51 -> 0<h+l.
Proof. intros H L. assert (E:l=(l/h)*h) by (field;lra). nra. Qed.

Lemma middle_composition_model s ec ey ep ev ea em1 em2 :
 998/1000 <= s <= 1 -> - /2^110 <= ec <= /2^110 -> - /2^98 <= ey <= /2^98 ->
 -(21/16)/2^68 <= ep <= (21/16)/2^68 -> - /2^101 <= ev <= /2^101 ->
 - /2^74 <= ea <= /2^74 -> - /2^77 <= em1 <= /2^77 -> - /2^77 <= em2 <= /2^77 ->
 - /2^67 <= ((1+ec)*(1+ey)*(s+ep+ev+ea)*(1+em1)*(1+em2)-s)/s <= /2^67.
Proof.
 intros S C Y P V A M1 M2. split;
 erfcx_goal (erfcx_middle_composition.l1 ec ey s ep ev ea em1 em2).
Qed.

Theorem middle_ieee x c s : finite x -> 16 <= B x <= 512 -> 0<c ->
 - /2^110 <= ((B cs+B csl)-c)/c <= /2^110 ->
 998/1000 <= s <= 1 ->
 - /2^74 <= correction_exact ((1/B x)*(1/B x))-s <= /2^74 ->
 let '(h,l) := middle64 x in
 finite h /\ finite l /\
 - /2^67 <= ((B h+B l)-(c/B x)*s)/((c/B x)*s) <= /2^67.
Proof.
 intros Fx X Cpos Cerror Srange Approx.
 pose proof (reciprocal_ieee x Fx X) as R.
 pose proof (reciprocal_square_ieee x Fx X) as Sq.
 unfold reciprocal_square64 in Sq. unfold middle64.
 destruct (reciprocal64 x) as [yh yl].
 destruct R as [Fyh [Fyl [Yh [Yl [Yq Ye]]]]].
 destruct (square64 yh yl) as [th tl].
 destruct Sq as [Fth [Ftl [Th [Te Tq]]]].
 pose proof (correction_ieee th tl Fth Ftl Th Tq) as W.
 destruct (correction64 th tl) as [w wl].
 destruct W as [Fw [Fwl [We [Wh Wq]]]].
 assert (Y : /512 <= 1/B x <= /16).
 { unfold Rdiv. rewrite Rmult_1_l. split; apply Rinv_le_contravar; lra. }
 pose proof (correction_sensitivity ((1/B x)*(1/B x))
  ((B th+B tl)-(1/B x)*(1/B x)) ltac:(nra) Te) as Sens.
 replace ((1/B x)*(1/B x)+((B th+B tl)-(1/B x)*(1/B x))) with (B th+B tl) in Sens by ring.
 destruct cs_ok as [Fcs [_ _]]. destruct csl_ok as [Fcsl [_ _]].
 destruct cs_range as [Ch [Chlo Cq]].
 assert (Yq' : - /2^51 <= B yl/B yh <= /2^51) by nra.
 pose proof (product_ieee cs csl yh yl Fcs Fcsl Fyh Fyl
  ltac:(lra) ltac:(lra) Cq Yq') as Z.
 destruct (product64 cs csl yh yl) as [zh zl].
 destruct Z as [Fzh [Fzl [Ze [Zh [Zq Zscale]]]]].
 assert (CZ : 9/8192 <= B cs*B yh <= 5/128) by nra.
 assert (Zid : B zh = (B zh/(B cs*B yh))*(B cs*B yh)) by (field; split; lra).
 assert (Zh' : /1024 <= B zh <= 2).
 { set (p := B cs*B yh) in *. set (r := B zh/p) in *. clear - CZ Zscale Zid. nra. }
 pose proof (product_ieee zh zl w wl Fzh Fzl Fw Fwl Zh' ltac:(lra) Zq Wq) as Out.
 destruct (product64 zh zl w wl) as [h l].
 destruct Out as [Fh [Fl [Oe _]]].
 pose proof (middle_composition_model s
  (((B cs+B csl)-c)/c)
  (((B yh+B yl)-1/B x)/(1/B x))
  ((B w+B wl)-correction_exact (B th+B tl))
  (correction_exact (B th+B tl)-correction_exact ((1/B x)*(1/B x)))
  (correction_exact ((1/B x)*(1/B x))-s)
  (((B zh+B zl)-(B cs+B csl)*(B yh+B yl))/((B cs+B csl)*(B yh+B yl)))
  (((B h+B l)-(B zh+B zl)*(B w+B wl))/((B zh+B zl)*(B w+B wl)))
  Srange Cerror Ye We Sens Approx Ze Oe) as Bound.
 assert (Csum : 0<B cs+B csl) by (apply low_sum_positive; [lra | exact Cq]).
 assert (Ysum : 0<B yh+B yl) by (apply low_sum_positive; [lra | exact Yq']).
 assert (Wsum : 0<B w+B wl) by (apply low_sum_positive; [lra | exact Wq]).
 assert (Zsum : 0<B zh+B zl) by (apply low_sum_positive; [lra | exact Zq]).
 assert (Eq :
  ((1+((B cs+B csl)-c)/c)*(1+((B yh+B yl)-1/B x)/(1/B x))*
   (s+((B w+B wl)-correction_exact (B th+B tl))+
    (correction_exact (B th+B tl)-correction_exact ((1/B x)*(1/B x)))+
    (correction_exact ((1/B x)*(1/B x))-s))*
   (1+((B zh+B zl)-(B cs+B csl)*(B yh+B yl))/((B cs+B csl)*(B yh+B yl)))*
   (1+((B h+B l)-(B zh+B zl)*(B w+B wl))/((B zh+B zl)*(B w+B wl)))-s)/s
  = ((B h+B l)-(c/B x)*s)/((c/B x)*s)).
 { field. repeat split; lra. }
 rewrite Eq in Bound. repeat split; tauto.
Qed.


Require Import ErfcxConstants.
Theorem middle_with_pi_ieee x s : finite x -> 16 <= B x <= 512 ->
 998/1000 <= s <= 1 ->
 - /2^74 <= correction_exact ((1/B x)*(1/B x))-s <= /2^74 ->
 let '(h,l) := middle64 x in
 finite h /\ finite l /\
 - /2^67 <= ((B h+B l)-(inv_sqrt_pi/B x)*s)/((inv_sqrt_pi/B x)*s) <= /2^67.
Proof.
 intros Fx X S A. pose proof (Rabs_le_inv _ _ cs_split_bound) as C.
 exact (middle_ieee x inv_sqrt_pi s Fx X inv_sqrt_pi_positive C S A).
Qed.

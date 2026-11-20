(** The existing relative rounding decision after reduction and selection. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid Encodings RoundingTest RelativeUlp.
From Interval Require Import Tactic.
Require Import StageGappa TrigFastSelection TrigRounding.
Open Scope R_scope.

Definition trig_eps : f64 := b64_of_bits 4327959241903046660.
Lemma trig_eps_finite : finite trig_eps.
Proof. exact (bits_finite 4327959241903046660 _ _ _ eq_refl). Qed.
Lemma trig_eps_value : B trig_eps=4503599627370500/2^114.
Proof. exact (bits_val 4327959241903046660 false 4503599627370500 114 eq_refl). Qed.

Lemma trig_decision_correct h l v y : finite h -> finite l ->
 B h=rndF(B h+B l) -> bpow radix2 (-64)<=Rabs v<=1 ->
 Rabs(B h+B l-v)<=/2^62*Rabs v -> decide_with h l trig_eps=Some y ->
 finite y /\ B y=rndF v.
Proof.
 intros H L Normal [Lo Hi] Error Decision.
 assert (Small:0<=/(2:R)^62<=/2) by interval.
 assert (Sum:Rabs(B h+B l)<=2).
 { pose proof (Rabs_triang (B h+B l-v) v) as T.
   replace (B h+B l-v+v) with (B h+B l) in T by ring.
   pose proof (Rabs_pos v);nra. }
 assert (Head:Rabs(B h)<=2).
 { rewrite Normal. apply abs_round_le_generic;[exact _|exact _| |exact Sum].
   change 2 with (bpow radix2 1);apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
 assert (SumLo:bpow radix2 (-65)<=Rabs(B h+B l)).
 { pose proof (Rabs_triang_inv v (B h+B l)) as T.
   rewrite (Rabs_minus_sym v (B h+B l)) in T.
   assert (Half:bpow radix2 (-65)=(/2)*bpow radix2 (-64)).
   { replace (-65)%Z with ((-1)+(-64))%Z by lia;rewrite bpow_plus;reflexivity. }
   rewrite Half;pose proof (Rabs_pos v);nra. }
 assert (HeadLo:bpow radix2 (-900)<=Rabs(B h)).
 { rewrite Normal. apply Rle_trans with (bpow radix2 (-65));[apply bpow_le;lia|].
   apply abs_round_ge_generic;[exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|exact SumLo]. }
 destruct (decide_with_ok h l trig_eps v (/2^62) y H L trig_eps_finite
   ltac:(split;[exact HeadLo|apply Rle_trans with (1:=Head);interval]) Normal) as [Y Value].
 - split;interval.
 - rewrite trig_eps_value;split;interval with (i_prec 180).
 - rewrite Rabs_minus_sym;exact Error.
 - exact Decision.
 - subst y;split;[exact H|symmetry;exact Value].
Qed.

Definition trig_fast_decision bits negative cosine :=
 let '(h,l):=trig_fast64 bits negative cosine in decide_with h l trig_eps.

Theorem trig_fast_decision_correct x negative cosine y :
 finite x -> bpow radix2 (-63)<=B x ->
 trig_fast_decision (bits_of_b64 x) negative cosine=Some y ->
 finite y /\ B y=rndF(if cosine then cos(if negative then -B x else B x)
                              else sin(if negative then -B x else B x)).
Proof.
 intros F X. pose proof (trig_fast64_correct x negative cosine F X) as Fast.
 unfold trig_fast_decision. destruct (trig_fast64 (bits_of_b64 x) negative cosine) as [h l].
 cbv zeta in Fast. destruct Fast as [H [L [N [E Lo]]]].
 apply trig_decision_correct;try assumption.
 split;[exact Lo|]. destruct cosine;apply Rabs_le;[apply COS_bound|apply SIN_bound].
Qed.

Definition trig_finish bits negative cosine :=
 match trig_fast_decision bits negative cosine with
 | Some y => y
 | None => trig_accurate_result bits negative cosine
 end.

Theorem trig_finish_ulp x negative cosine : finite x -> bpow radix2 (-63)<=B x ->
 let y:=trig_finish (bits_of_b64 x) negative cosine in
 let v:=if cosine then cos(if negative then -B x else B x)
                   else sin(if negative then -B x else B x) in
 finite y /\ Rabs(B y-v)<=(/2+bpow radix2 (-145))*ulp radix2 (FLT_exp emin prec) v.
Proof.
 intros F X;cbv zeta. unfold trig_finish.
 destruct (trig_fast_decision (bits_of_b64 x) negative cosine) as [y|] eqn:D.
 - destruct (trig_fast_decision_correct x negative cosine y F X D) as [Y Value].
   split;[exact Y|]. rewrite Value.
   set (v:=if cosine then cos(if negative then -B x else B x)
                    else sin(if negative then -B x else B x)).
   pose proof (relative_ulp_error 0 v v ltac:(split;[lra|apply bpow_gt_0])
     ltac:(rewrite Rminus_diag_eq,Rabs_R0 by reflexivity;lra)) as Error.
   apply Rle_trans with (1:=Error).
   apply Rmult_le_compat_r;[apply ulp_ge_0|]. pose proof (bpow_ge_0 radix2 (-145));nra.
 - apply trig_accurate_ulp;[exact F|pose proof (bpow_gt_0 radix2 (-63));lra].
Qed.

(** IEEE table Horner evaluation and its reconstruction preconditions. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
Require Import StageGappa ErfcxTableCoefficient ErfcxTableData ErfcxTableProducts.
From Gappa Require Import Gappa_library.
Require Import ErfcxReciprocal.
Require erfcx_table_sums.
Import ListNotations.
Open Scope R_scope.

Definition horner_step64 a h q := fadd a (fmul h q).
Lemma horner_step_ieee a h q : finite a -> Rabs (B a)<=4 ->
 finite h -> Rabs (B h)<=/8 -> finite q -> Rabs (B q)<=5 ->
 finite (horner_step64 a h q) /\ Rabs (B (horner_step64 a h q))<=5 /\
 B (horner_step64 a h q)=rndF (B a+rndF (B h*B q)).
Proof.
 intros Fa A Fh H Fq Q.
 destruct (fmul_bnd 5 (-3) h q Fh Fq ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;change (IZR 5*bpow radix2 (-3)) with (5*/8);
    rewrite Rabs_mult;pose proof (Rabs_pos (B h));pose proof (Rabs_pos (B q));nra)) as [Fm [Bm M]].
 unfold bnd in M. change (IZR 5*bpow radix2 (-3)) with (5*/8) in M.
 destruct (fadd_bnd 5 0 a (fmul h q) Fa Fm ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_r;apply Rle_trans with (Rabs (B a)+Rabs (B (fmul h q)));[apply Rabs_triang|simpl;lra])) as [Fs [Bs S]].
 unfold bnd in S. change (IZR 5*bpow radix2 0) with (5*1) in S.
 unfold horner_step64. split;[exact Fs|]. split;[lra|rewrite Bs,Bm;reflexivity].
Qed.

Fixpoint horner64 h cs : f64 :=
 match cs with
 | [] => b64_of_bits 0
 | [a] => a
 | a::rest => horner_step64 a h (horner64 h rest)
 end.
Fixpoint horner_value h cs : R :=
 match cs with
 | [] => 0
 | [a] => a
 | a::rest => rndF (a+rndF (h*horner_value h rest))
 end.
Theorem horner_ieee h cs : finite h -> Rabs (B h)<=/8 ->
 Forall (fun a => finite a /\ Rabs (B a)<=4) cs ->
 finite (horner64 h cs) /\ Rabs (B (horner64 h cs))<=5 /\
 B (horner64 h cs)=horner_value (B h) (map B cs).
Proof.
 intros Fh H C. induction C as [|a rest A Rest IH].
 - cbn [horner64 horner_value map]. split;[reflexivity|].
   change (Rabs 0<=5 /\ 0=0). rewrite Rabs_R0;split;lra.
 - destruct rest as [|b rest].
   + cbn [horner64 horner_value map]. destruct A as [Fa Ab]. repeat split;try assumption;lra.
   + destruct A as [Fa Ab]. destruct IH as [Fq [Q Eq]].
     destruct (horner_step_ieee a h (horner64 h (b::rest)) Fa Ab Fh H Fq Q) as [F [V E]].
     split;[exact F|]. split;[exact V|].
     change (B (horner_step64 a h (horner64 h (b::rest))) =
       rndF (B a+rndF (B h*horner_value (B h) (map B (b::rest))))).
     rewrite E,Eq. reflexivity.
Qed.


Definition bounded64 x cap := finite x /\ Rabs (B x)<=cap.

Ltac table_bound :=
 first [
   match goal with
   | Ha : Rabs ?a <= ?u, Hb : Rabs ?b <= ?v |- Rabs (?a * ?b) <= ?cap =>
       rewrite Rabs_mult;apply Rle_trans with (u*v);
       [apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Ha|exact Hb]|lra]
   end
 | eapply Rle_trans;[apply Rabs_triang|lra] ].
Ltac table_op op k e a b F V C :=
 destruct (op k e a b ltac:(assumption) ltac:(assumption)
   ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;bpow_num;cbn [IZR];table_bound)) as [F [V C]];
 unfold bnd in C;revert C;bpow_num;cbn [IZR];intro C.

Definition table_rest64 a0l a1 b1 a2h b2 h hh l sq q :=
 let lh := fmul l (fadd h hh) in
 let h2 := fadd sq lh in
 let t3 := fmul (fmul h2 h) q in
 let r1 := fadd (fmul a1 l) (fmul b1 h) in
 let r2 := fadd (fmul a2h lh) (fmul b2 sq) in
 fadd (fadd (fadd a0l r1) r2) t3.
Definition table_rest_value a0l a1 b1 a2h b2 h hh l sq q :=
 let lh := rndF (l*rndF (h+hh)) in
 let h2 := rndF (sq+lh) in
 let t3 := rndF (rndF (h2*h)*q) in
 let r1 := rndF (rndF (a1*l)+rndF (b1*h)) in
 let r2 := rndF (rndF (a2h*lh)+rndF (b2*sq)) in
 rndF (rndF (rndF (a0l+r1)+r2)+t3).

Theorem table_rest_ieee a0l a1 b1 a2h b2 h hh l sq q :
 bounded64 a0l (/2^52) -> bounded64 a1 4 -> bounded64 b1 (/2^32) ->
 bounded64 a2h 4 -> bounded64 b2 (/2^14) ->
 bounded64 h (/8) -> bounded64 hh (/8) -> bounded64 l (/2^21) ->
 bounded64 sq (/64) -> bounded64 q 5 ->
 bounded64 (table_rest64 a0l a1 b1 a2h b2 h hh l sq q) (21/1024) /\
 B (table_rest64 a0l a1 b1 a2h b2 h hh l sq q)=
 table_rest_value (B a0l) (B a1) (B b1) (B a2h) (B b2) (B h) (B hh) (B l) (B sq) (B q).
Proof.
 intros [F0 A0] [F1 A1] [Fb1 B1] [F2 A2] [Fb2 B2]
   [Fh H] [FH HH] [Fl L] [Fs Sq] [Fq Q].
 table_op fadd_bnd 1%Z (-2)%Z h hh Fsum Vsum Csum.
 table_op fmul_bnd 1%Z (-23)%Z l (fadd h hh) Flh Vlh Clh.
 table_op fadd_bnd 1%Z (-5)%Z sq (fmul l (fadd h hh)) Fh2 Vh2 Ch2.
 set (lh := fmul l (fadd h hh)) in *.
 set (h2 := fadd sq lh) in *.
 table_op fmul_bnd 1%Z (-8)%Z h2 h Fh3 Vh3 Ch3.
 table_op fmul_bnd 5%Z (-8)%Z (fmul h2 h) q Ft3 Vt3 Ct3.
 table_op fmul_bnd 1%Z (-19)%Z a1 l Fp1 Vp1 Cp1.
 table_op fmul_bnd 1%Z (-35)%Z b1 h Fp2 Vp2 Cp2.
 table_op fadd_bnd 1%Z (-18)%Z (fmul a1 l) (fmul b1 h) Fr1 Vr1 Cr1.
 table_op fmul_bnd 1%Z (-21)%Z a2h lh Fp3 Vp3 Cp3.
 table_op fmul_bnd 1%Z (-20)%Z b2 sq Fp4 Vp4 Cp4.
 table_op fadd_bnd 1%Z (-19)%Z (fmul a2h lh) (fmul b2 sq) Fr2 Vr2 Cr2.
 set (r1 := fadd (fmul a1 l) (fmul b1 h)) in *.
 set (r2 := fadd (fmul a2h lh) (fmul b2 sq)) in *.
 table_op fadd_bnd 1%Z (-17)%Z a0l r1 Fra1 Vra1 Cra1.
 table_op fadd_bnd 1%Z (-16)%Z (fadd a0l r1) r2 Fra Vra Cra.
 table_op fadd_bnd 21%Z (-10)%Z (fadd (fadd a0l r1) r2) (fmul (fmul h2 h) q) Fr Vr Cr.
 unfold table_rest64. fold lh h2 r1 r2.
 split;[split;[exact Fr|change (21/1024) with (21*/1024);exact Cr]|].
 unfold table_rest_value. rewrite Vr,Vra,Vra1,Vr1,Vr2,Vp1,Vp2,Vp3,Vp4,Vt3,Vh3,Vh2,Vlh,Vsum.
 reflexivity.
Qed.


Lemma table_sums_model a0x r1 r2 restx :
 9/256<=rn a0x<=2 -> -/4<=r1<=/4 -> -/16<=r2<=/16 ->
 -21/1024<=rn restx<=21/1024 ->
 let a0 := rn a0x in let p1 := a0*r1 in let p2 := a0*r2 in
 let s := rn (a0+p1) in let e1 := a0+p1-s in
 let s2 := rn (s+p2) in let e2 := s+p2-s2 in
 let lo := rn (rn (e1+e2)+rn restx) in
 13/512<=s<=3 /\ 3/128<=s2<=4 /\
 3/128<=s-p2<=3 /\ 3/128<=s+p2<=3 /\
 -11/512<=lo<=11/512 /\
 -/2^51<=e1<=/2^51 /\ -/2^50<=e2<=/2^50.
Proof.
 intros A R1 R2 Rest. cbv zeta. repeat split;
 erfcx_goal (erfcx_table_sums.l1 a0x r1 r2 restx).
Qed.

Definition table_sum64 a0 p1 p2 rest :=
 let '(s,e1) := fast_two_sum64 a0 p1 in
 let '(s2,e2) := fast_two_sum64 s p2 in
 fast_two_sum64 s2 (fadd (fadd e1 e2) rest).
Definition table_sum_value a0 p1 p2 rest :=
 let s := rndF (a0+p1) in let e1 := a0+p1-s in
 let s2 := rndF (s+p2) in let e2 := s+p2-s2 in
 s2+rndF (rndF (e1+e2)+rest).

Theorem table_sum_ieee a0 p1 p2 rest :
 finite a0 -> 9/256<=B a0<=2 ->
 finite p1 -> Rabs (B p1)<=B a0/4 ->
 finite p2 -> Rabs (B p2)<=B a0/16 ->
 bounded64 rest (21/1024) ->
 let '(h,l) := table_sum64 a0 p1 p2 rest in
 finite h /\ finite l /\ B h+B l=table_sum_value (B a0) (B p1) (B p2) (B rest).
Proof.
 intros Fa A Fp1 P1 Fp2 P2 [Fr Rest].
 assert (R1 : rn (B a0)=B a0) by (apply round_generic;[exact _|apply B_fmt]).
 assert (Rr : rn (B rest)=B rest) by (apply round_generic;[exact _|apply B_fmt]).
 assert (C1 : B a0*(B p1/B a0)=B p1) by (field;lra).
 assert (C2 : B a0*(B p2/B a0)=B p2) by (field;lra).
 assert (Q1 : -/4<=B p1/B a0<=/4).
 { pose proof (Rabs_le_inv _ _ P1) as P. clear - A C1 P;nra. }
 assert (Q2 : -/16<=B p2/B a0<=/16).
 { pose proof (Rabs_le_inv _ _ P2) as P. clear - A C2 P;nra. }
 pose proof (table_sums_model (B a0) (B p1/B a0) (B p2/B a0) (B rest)
  ltac:(rewrite R1;exact A) Q1 Q2 ltac:(rewrite Rr;apply Rabs_le_inv in Rest;lra)) as M.
 cbv zeta in M. rewrite R1,Rr,C1,C2 in M.
 destruct M as [S [S2 [Minus [Plus [Lo [E1 E2]]]]]].
 assert (Aabs : Rabs (B a0)<=2) by (rewrite Rabs_pos_eq by lra;lra).
 assert (P1abs : Rabs (B p1)<=1) by lra.
 assert (P2abs : Rabs (B p2)<=1) by lra.
 pose proof (fast_two_sum_ieee a0 p1 Fa Fp1
  ltac:(apply Rle_trans with 2;[exact Aabs|change 2 with (bpow radix2 1);apply bpow_le;lia])
  ltac:(apply Rle_trans with 1;[exact P1abs|change 1 with (bpow radix2 0);apply bpow_le;lia])
  ltac:(right;left;rewrite (Rabs_pos_eq (B a0)) by lra;lra)) as FTS1.
 unfold table_sum64. destruct (fast_two_sum64 a0 p1) as [s e1].
 destruct FTS1 as [Fs [Fe1 [Bs Exact1]]].
 assert (Be1 : B e1=B a0+B p1-B s) by lra.
 change (B s=rn (B a0+B p1)) in Bs.
 rewrite <-Bs in S,S2,Minus,Plus,Lo,E1,E2.
 rewrite <-Be1 in Lo,E1.
 assert (Sabs : Rabs (B s)<=4) by (apply Rabs_le;lra).
 assert (P2s : Rabs (B p2)<=Rabs (B s)).
 { rewrite (Rabs_pos_eq (B s)) by lra. apply Rabs_le; lra. }
 pose proof (fast_two_sum_ieee s p2 Fs Fp2
  ltac:(apply Rle_trans with 4;[exact Sabs|change 4 with (bpow radix2 2);apply bpow_le;lia])
  ltac:(apply Rle_trans with 1;[exact P2abs|change 1 with (bpow radix2 0);apply bpow_le;lia])
  ltac:(right;left;exact P2s)) as FTS2.
 destruct (fast_two_sum64 s p2) as [s2 e2].
 destruct FTS2 as [Fs2 [Fe2 [Bs2 Exact2]]].
 assert (Be2 : B e2=B s+B p2-B s2) by lra.
 change (B s2=rn (B s+B p2)) in Bs2.
 rewrite <-Bs2 in S2,Lo,E2. rewrite <-Be2 in Lo,E2.
 assert (E1abs : Rabs (B e1)<=/2^51) by (apply Rabs_le;lra).
 assert (E2abs : Rabs (B e2)<=/2^50) by (apply Rabs_le;lra).
 table_op fadd_bnd 1%Z (-49)%Z e1 e2 Fe Ve Ce.
 table_op fadd_bnd 1%Z (-5)%Z (fadd e1 e2) rest Fl Vl Cl.
 assert (Low : -11/512<=B (fadd (fadd e1 e2) rest)<=11/512).
 { rewrite Vl,Ve. exact Lo. }
 assert (Last : Rabs (B (fadd (fadd e1 e2) rest))<=Rabs (B s2)).
 { rewrite (Rabs_pos_eq (B s2)) by lra. apply Rabs_le;lra. }
 pose proof (fast_two_sum_ieee s2 (fadd (fadd e1 e2) rest) Fs2 Fl
  ltac:(apply Rle_trans with 4;[apply Rabs_le;lra|change 4 with (bpow radix2 2);apply bpow_le;lia])
  ltac:(apply Rle_trans with 1;[lra|change 1 with (bpow radix2 0);apply bpow_le;lia])
  ltac:(right;left;exact Last)) as FTS3.
 destruct (fast_two_sum64 s2 (fadd (fadd e1 e2) rest)) as [h l].
 destruct FTS3 as [Fh [Flast [Bh Exact]]]. repeat split;try assumption.
 rewrite Exact,Vl,Ve,Be1,Be2,Bs2,Bs. reflexivity.
Qed.

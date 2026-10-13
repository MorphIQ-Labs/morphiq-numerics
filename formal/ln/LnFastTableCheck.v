(** Kernel-checked binary64 table and split-ln(2) errors. *)
From Coq Require Import Reals ZArith Lia Lra List.
From Flocq Require Import Core IEEE754.Bits.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import LnTables LnTableCheck LnFastTables.
Open Scope R_scope.
Ltac lf_decode := repeat match goal with
 | |- context [B (b64_of_bits ?n)] =>
   let d := eval vm_compute in (dec n) in
   match d with Some (?m,?e) =>
    let F:=fresh "F" in let V:=fresh "V" in
    destruct (dec_ok n m e eq_refl) as [F V]; rewrite V
   end
 end.
Definition lf_table_ok i : Prop :=
 let '(h,l):=lf_neg_ln_r i in
 finite h /\ finite l /\ Rabs(B h)<=1 /\ Rabs(B l)<=/2^53 /\
 Rabs(B h+B l+ln(B (ln_r i)))<=984/2^117*Rabs(ln(B (ln_r i))).
Lemma lf_table_all : forall i, (i<128)%nat -> lf_table_ok i.
Proof.
 intros i H. do 128 (destruct i as [|i]; [unfold lf_table_ok,lf_neg_ln_r,lf_table,ln_r,ln_r_bits; cbn [nth]; lf_decode;
  repeat split; try assumption; try reflexivity; interval with (i_prec 180) | ]). lia.
Qed.
Lemma lf_ln2_error : Rabs(B lf_lh+B lf_ll-ln 2)+(/2^53)*Rabs(B lf_ll)<=745/2^106*ln 2.
Proof. rewrite lf_lh_val,lf_ll_val. interval with (i_prec 180). Qed.

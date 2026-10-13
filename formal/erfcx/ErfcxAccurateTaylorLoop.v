(** The Rust Taylor loop: two consecutive small terms, or the fixed cap. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateCenterModel ErfcxAccurateCenters
  ErfcxAccurateTaylorStep ErfcxAccurateTaylorInitial ErfcxAccurateTaylorCoefficients
  ErfcxAccurateTaylorPower ErfcxAccurateTaylorTerms ErfcxAccurateTaylorSum.
Import ListNotations.
Open Scope R_scope.
Definition q_taylor_small i term := Z.ltb (top term) (top(q_center i)-262).
Fixpoint q_taylor_loop c h limit n fuel prev cur hp sum (small : bool) :=
  match fuel with
  | O => sum
  | S rest =>
      let next:=q_taylor_step c prev cur (S n) in
      let hp':=mul hp h in let term:=mul next hp' in let sum':=add sum term in
      if Z.ltb (top term) limit then
        if small then sum' else q_taylor_loop c h limit (S n) rest cur next hp' sum' true
      else q_taylor_loop c h limit (S n) rest cur next hp' sum' false
  end.
Definition q_taylor_series c i h :=
  q_taylor_loop c h (top(q_center i)-262) 0 98 (q_center i) (q_taylor_first c i) h
    (add(q_center i)(mul(q_taylor_first c i)h)) false.

Lemma q_taylor_coefficient_next c i n :
  q_taylor_step c (fst(q_taylor_coefficients c i n)) (snd(q_taylor_coefficients c i n)) (S n)=
  snd(q_taylor_coefficients c i (S n)).
Proof. cbn [q_taylor_coefficients]. destruct(q_taylor_coefficients c i n);reflexivity. Qed.
Lemma q_taylor_coefficient_shift c i n :
  snd(q_taylor_coefficients c i n)=fst(q_taylor_coefficients c i (S n)).
Proof. cbn [q_taylor_coefficients]. destruct(q_taylor_coefficients c i n);reflexivity. Qed.

Lemma q_taylor_loop_unroll c i h n fuel small :
  q_taylor_loop c h (top(q_center i)-262) n (S fuel)
    (fst(q_taylor_coefficients c i n)) (snd(q_taylor_coefficients c i n))
    (q_taylor_power h n) (q_taylor_sum c i h (S n)) small=
  if q_taylor_small i (q_taylor_term c i h (S n)) then
    if small then q_taylor_sum c i h (S(S n))
    else q_taylor_loop c h (top(q_center i)-262) (S n) fuel
      (fst(q_taylor_coefficients c i (S n))) (snd(q_taylor_coefficients c i (S n)))
      (q_taylor_power h (S n)) (q_taylor_sum c i h (S(S n))) true
  else q_taylor_loop c h (top(q_center i)-262) (S n) fuel
      (fst(q_taylor_coefficients c i (S n))) (snd(q_taylor_coefficients c i (S n)))
      (q_taylor_power h (S n)) (q_taylor_sum c i h (S(S n))) false.
Proof.
  unfold q_taylor_small,q_taylor_term.
  cbn [q_taylor_loop q_taylor_coefficients q_taylor_power q_taylor_sum q_taylor_term q_taylor_small].
  unfold q_taylor_term. cbn [q_taylor_coefficients].
  destruct(q_taylor_coefficients c i n);reflexivity.
Qed.

Theorem q_taylor_loop_prefix c i h n fuel small :
  (n+fuel<=98)%nat ->
  (small=true -> (1<=n)%nat /\ q_taylor_small i (q_taylor_term c i h n)=true) ->
  exists j, (S n<=j<=S(n+fuel))%nat /\
    q_taylor_loop c h (top(q_center i)-262) n fuel
      (fst(q_taylor_coefficients c i n)) (snd(q_taylor_coefficients c i n))
      (q_taylor_power h n) (q_taylor_sum c i h (S n)) small=q_taylor_sum c i h j /\
    (j=S(n+fuel) \/ ((3<=j)%nat /\
      q_taylor_small i (q_taylor_term c i h (j-2))=true /\
      q_taylor_small i (q_taylor_term c i h (j-1))=true)).
Proof.
  revert n small. induction fuel as [|fuel IH]; intros n small Cap Previous.
  - exists (S n). cbn [q_taylor_loop]. rewrite Nat.add_0_r. split; [lia|]. split; [reflexivity|left;reflexivity].
  - rewrite q_taylor_loop_unroll.
    assert (Advance : forall b,
      (b=true -> q_taylor_small i (q_taylor_term c i h (S n))=true) ->
      exists j,(S n<=j<=S(n+S fuel))%nat /\
        q_taylor_loop c h (top(q_center i)-262) (S n) fuel
          (fst(q_taylor_coefficients c i (S n))) (snd(q_taylor_coefficients c i (S n)))
          (q_taylor_power h (S n)) (q_taylor_sum c i h (S(S n))) b=q_taylor_sum c i h j /\
        (j=S(n+S fuel) \/ ((3<=j)%nat /\
          q_taylor_small i (q_taylor_term c i h (j-2))=true /\
          q_taylor_small i (q_taylor_term c i h (j-1))=true))).
    { intros b B. destruct(IH (S n) b ltac:(lia) ltac:(intros E;split;[lia|apply B;exact E])) as [j [J [Value Stop]]].
      exists j. split; [lia|]. split; [exact Value|]. destruct Stop as [End|Stop];[left;lia|right;exact Stop]. }
    destruct(q_taylor_small i (q_taylor_term c i h (S n))) eqn:Small.
    + destruct small.
      * destruct(Previous eq_refl) as [N Last]. exists(S(S n)). split;[lia|]. split;[reflexivity|].
        right. split;[lia|]. replace (S(S n)-2)%nat with n by lia.
        replace (S(S n)-1)%nat with (S n) by lia. split;assumption.
      * apply Advance. intros _;reflexivity.
    + apply Advance. discriminate.
Qed.

Theorem q_taylor_series_prefix c i h :
  exists j,(1<=j<=99)%nat /\ q_taylor_series c i h=q_taylor_sum c i h j /\
    (j=99%nat \/ ((3<=j)%nat /\ q_taylor_small i (q_taylor_term c i h (j-2))=true /\
      q_taylor_small i (q_taylor_term c i h (j-1))=true)).
Proof. exact(q_taylor_loop_prefix c i h 0 98 false ltac:(lia) ltac:(discriminate)). Qed.

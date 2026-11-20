From Coq Require Import Reals ZArith Lia Lra Psatz List Bool.
From Flocq Require Import Core.
Require Import TrigConstants.
Open Scope R_scope.

(** A determinant-one bracket excludes a nearer rational at every smaller
    denominator. The integer basis is explicit; no continued-fraction oracle
    or premise about best approximations is needed. *)
Theorem farey_gap alpha delta (pl ql ph qh n k : Z) :
  (0<ql)%Z -> (0<qh)%Z -> (ql*ph-qh*pl=1)%Z ->
  (0<n<ql+qh)%Z -> 0<=delta ->
  delta<=alpha*IZR ql-IZR pl -> delta<=IZR ph-alpha*IZR qh ->
  delta<=Rabs(alpha*IZR n-IZR k).
Proof.
  intros Ql Qh Det N D L H.
  set (a := (ph*n-qh*k)%Z).
  set (b := (ql*k-pl*n)%Z).
  assert (En : n=(a*ql+b*qh)%Z).
  { unfold a,b. replace ((ph*n-qh*k)*ql+(ql*k-pl*n)*qh)%Z
      with (n*(ql*ph-qh*pl))%Z by ring. rewrite Det; ring. }
  assert (Ek : k=(a*pl+b*ph)%Z).
  { unfold a,b. replace ((ph*n-qh*k)*pl+(ql*k-pl*n)*ph)%Z
      with (k*(ql*ph-qh*pl))%Z by ring. rewrite Det; ring. }
  assert (Value : alpha*IZR n-IZR k =
    IZR a*(alpha*IZR ql-IZR pl)-IZR b*(IZR ph-alpha*IZR qh)).
  { rewrite En,Ek,!plus_IZR,!mult_IZR; ring. }
  clearbody a b.
  rewrite Value.
  destruct (Z_lt_ge_dec 0 a) as [Ap|An].
  - assert (Bn : (b<=0)%Z) by (clear -En N Ql Qh Ap; nia).
    assert (Ar : 1<=IZR a) by (apply IZR_le; lia).
    assert (Br : IZR b<=0) by (apply IZR_le; exact Bn).
    pose proof (Rmult_le_pos (IZR a-1) (alpha*IZR ql-IZR pl) ltac:(lra) ltac:(lra)) as LA.
    pose proof (Rmult_le_pos (-IZR b) (IZR ph-alpha*IZR qh) ltac:(lra) ltac:(lra)) as HB.
    clear -L H D Ar Br LA HB. rewrite Rabs_pos_eq; nra.
  - assert (Bp : (1<=b)%Z) by (clear -En N Ql Qh An; nia).
    assert (Ar : IZR a<=0) by (apply IZR_le; lia).
    assert (Br : 1<=IZR b) by (apply IZR_le; exact Bp).
    pose proof (Rmult_le_pos (-IZR a) (alpha*IZR ql-IZR pl) ltac:(lra) ltac:(lra)) as LA.
    pose proof (Rmult_le_pos (IZR b-1) (IZR ph-alpha*IZR qh) ltac:(lra) ltac:(lra)) as HB.
    clear -L H D Ar Br LA HB. rewrite Rabs_left1; nra.
Qed.

Record separation_witness := witness {
  lower_numerator : Z;
  lower_denominator : Z;
  upper_numerator : Z;
  upper_denominator : Z
}.

Definition separation_check (e : Z) (w : separation_witness) : bool :=
  let s := (2^(1408-e))%Z in
  let pl := lower_numerator w in let ql := lower_denominator w in
  let ph := upper_numerator w in let qh := upper_denominator w in
  ((0 <? ql) && (0 <? qh) && (ql*ph-qh*pl =? 1) &&
   (2^53 <=? ql+qh) &&
   (s <=? (ql*trig_two_over_pi-pl*s)*2^62) &&
   (s <=? (ph*s-qh*(trig_two_over_pi+1))*2^62))%Z.

Fixpoint separation_check_from (e : Z) (ws : list separation_witness) : bool :=
  match ws with
  | nil => true
  | w :: rest => separation_check e w && separation_check_from (e+1)%Z rest
  end.

Lemma separation_check_at e ws n d :
  separation_check_from e ws=true -> (n<length ws)%nat ->
  separation_check (e+Z.of_nat n)%Z (nth n ws d)=true.
Proof.
  revert e n. induction ws as [|w ws IH]; intros e [|n] V N; simpl in *; try lia.
  - apply andb_true_iff in V. replace (e+0)%Z with e by ring; exact (proj1 V).
  - apply andb_true_iff in V.
    replace (e+Z.pos (Pos.of_succ_nat n))%Z with ((e+1)+Z.of_nat n)%Z by lia.
    apply IH; [exact (proj2 V)|lia].
Qed.

Lemma trig_IZR_pow2 e : (0<=e)%Z -> IZR (2^e)=bpow radix2 e.
Proof. intro E. change (IZR (Zpower radix2 e)=bpow radix2 e). apply IZR_Zpower; exact E. Qed.

Lemma trig_scaled_table e : (e<=1408)%Z ->
  let s := IZR (2^(1408-e)) in
  IZR trig_two_over_pi < (bpow radix2 e * (2/PI))*s < IZR trig_two_over_pi+1.
Proof.
  intros E; cbv zeta.
  pose proof trig_two_over_pi_bits as [L H].
  rewrite (pow_IZR 2 1408) in L,H.
  change (IZR trig_two_over_pi / IZR (2^1408)<2/PI) in L.
  change (2/PI<(IZR trig_two_over_pi+1) / IZR (2^1408)) in H.
  assert (T : 0<IZR (2^1408)) by (apply IZR_lt; apply Z.pow_pos_nonneg; lia).
  pose proof (Rmult_lt_compat_r (IZR (2^1408)) _ _ T L) as LL.
  pose proof (Rmult_lt_compat_r (IZR (2^1408)) _ _ T H) as HH.
  replace (IZR trig_two_over_pi / IZR (2^1408) * IZR (2^1408))
    with (IZR trig_two_over_pi) in LL by (field; lra).
  replace ((IZR trig_two_over_pi+1) / IZR (2^1408) * IZR (2^1408))
    with (IZR trig_two_over_pi+1) in HH by (field; lra).
  assert (Scale : bpow radix2 e * IZR (2^(1408-e))=IZR (2^1408)).
  { rewrite !trig_IZR_pow2 by lia. rewrite <-bpow_plus. f_equal; ring. }
  replace (bpow radix2 e * (2/PI)*IZR (2^(1408-e)))
    with ((2/PI)*(bpow radix2 e*IZR (2^(1408-e)))) by ring.
  rewrite Scale; split; assumption.
Qed.

Lemma enclosed_residuals alpha a s d pl ql ph qh :
  0<s -> 0<d -> 0<ql -> 0<qh -> a<alpha*s<a+1 ->
  s<=(ql*a-pl*s)*d -> s<=(ph*s-qh*(a+1))*d ->
  /d<=alpha*ql-pl /\ /d<=ph-alpha*qh.
Proof.
  intros S D Ql Qh [Lo Hi] L H. split.
  - assert (A : ql*a*d <= ql*(alpha*s)*d).
    { apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_l; lra. }
    apply Rmult_le_reg_r with (s*d); [apply Rmult_lt_0_compat; assumption|].
    replace (/d*(s*d)) with s by (field; lra).
    clear -L A; nra.
  - assert (A : qh*(alpha*s)*d <= qh*(a+1)*d).
    { apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_l; lra. }
    apply Rmult_le_reg_r with (s*d); [apply Rmult_lt_0_compat; assumption|].
    replace (/d*(s*d)) with s by (field; lra).
    clear -H A; nra.
Qed.

Theorem separation_check_sound e w (m k : Z) :
  (e<=1408)%Z -> separation_check e w=true -> (0<m<2^53)%Z ->
  /2^62 <= Rabs((bpow radix2 e*(2/PI))*IZR m-IZR k).
Proof.
  intros E V M. destruct w as [pl ql ph qh].
  unfold separation_check in V.
  cbn [lower_numerator lower_denominator upper_numerator upper_denominator] in V.
  rewrite !andb_true_iff, !Z.ltb_lt, !Z.eqb_eq, !Z.leb_le in V.
  destruct V as [[[[[Ql Qh]Det]Cover]L]H].
  assert (S : 0<IZR (2^(1408-e))) by (apply IZR_lt; apply Z.pow_pos_nonneg; lia).
  assert (D : 0<IZR (2^62)) by (apply IZR_lt; apply Z.pow_pos_nonneg; lia).
  assert (QlR : 0<IZR ql) by (apply IZR_lt; exact Ql).
  assert (QhR : 0<IZR qh) by (apply IZR_lt; exact Qh).
  apply IZR_le in L,H.
  rewrite !mult_IZR,minus_IZR,!mult_IZR in L,H.
  rewrite plus_IZR in H.
  destruct (enclosed_residuals (bpow radix2 e*(2/PI)) (IZR trig_two_over_pi)
    (IZR (2^(1408-e))) (IZR (2^62)) (IZR pl) (IZR ql) (IZR ph) (IZR qh)
    S D QlR QhR (trig_scaled_table e E) L H) as [Lo Hi].
  rewrite (pow_IZR 2 62).
  apply (farey_gap _ _ pl ql ph qh m k Ql Qh Det).
  - lia.
  - left; apply Rinv_0_lt_compat; exact D.
  - exact Lo.
  - exact Hi.
Qed.

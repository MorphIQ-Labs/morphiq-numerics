(** expm1's exponential stages, including cancellation, the interval decision,
    exact final scaling and the executable domain screen. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingTest.
From Interval Require Import Tactic.
Require Import StageGappa ExpStageA ExpStageB ExpStageReduction Expm1Scale Ln1pLemmas Ln1pReduction.
Open Scope R_scope.

Lemma em_k_lower x ni j k : -37 < x -> ni = (512*k+j)%Z -> (0 <= j < 512)%Z ->
 Rabs (x - IZR ni * L) <= 0.000677 -> (-54 <= k)%Z.
Proof.
 intros X N J R. apply Rabs_le_inv in R.
 assert (Ln : 0.693147 <= ln 2 <= 0.693148) by (split; interval with (i_prec 64)).
 destruct (Z_le_gt_dec (-54) k); [assumption | ].
 assert (Ni : IZR ni <= -27649) by (apply IZR_le; lia).
 unfold L in R. nra.
Qed.

Definition em_a_base : f64 := b64_of_bits 4341470040785158144.
Lemma em_a_base_ok : finite em_a_base /\ B em_a_base = bpow radix2 (-59).
Proof. exact (enc_pow2 (-59) ltac:(lia)). Qed.
Definition em_a x :=
 let '(n,j,k,r1) := stage_of x in
 let '(h,l) := stage_a_value n r1 (Z.to_nat j) in em_decide h l em_a_base k.
Theorem em_a_ok x v : finite x -> Rabs (B x) < 704 -> -37 < B x -> /32 <= Rabs (B x) ->
 em_a x = Some v -> finite v /\ B v = rndF (exp (B x) - 1).
Proof.
 intros Fx X Xlo Xs. pose proof (stage_of_ok x Fx X) as SO.
 unfold em_a. revert SO. generalize (stage_of x).
 intros [[[n j] k] r1] [ni [Bn [Fn [Hn [Hjk [Hj [Hk [Fr1 [Br1 [HR [Hr1 [G1 Z1]]]]]]]]]]]].
 assert (Jn : (Z.to_nat j < 512)%nat) by lia.
 pose proof (stage_a_value_ok x n r1 ni (Z.to_nat j) Fx Fn Bn Hn Fr1 Br1 HR Hr1 Jn) as SV.
 revert SV. generalize (stage_a_value n r1 (Z.to_nat j)). intros [h l] [Fh [Fl [Ah [Al Err]]]] Hd.
 set (r := B x - IZR ni * L) in *.
 set (z := exp (INR (Z.to_nat j) * ln 2 / 512) * exp r) in *.
 assert (Ex : exp (B x) = z * bpow radix2 k).
 { unfold z. rewrite <- exp_split. f_equal. rewrite Z2Nat.id by lia. unfold r. rewrite Hjk. ring. }
 assert (K : (-54 <= k <= 1016)%Z).
 { split; [apply (em_k_lower (B x) ni j); assumption | lia]. }
 destruct em_a_base_ok as [Fb Bb].
 apply (em_decide_ok h l em_a_base k (B x) z v Fh Fl Fb Ah); try assumption.
 - bpow_num_all. lra.
 - rewrite Bb. bpow_num_all. lra.
 - rewrite Bb. bpow_num_all. lra.
 - unfold z. apply z_range; assumption.
Qed.

Definition em_b_base : f64 := b64_of_bits 4300937644138823680.
Lemma em_b_base_ok : finite em_b_base /\ B em_b_base = bpow radix2 (-68).
Proof. exact (enc_pow2 (-68) ltac:(lia)). Qed.
Definition em_b x :=
 let '(n,j,k,r1) := stage_of x in
 let '(h,l) := stage_b_value n r1 (Z.to_nat j) in em_decide h l em_b_base k.
Theorem em_b_ok x v : finite x -> Rabs (B x) < 704 -> -37 < B x -> /32 <= Rabs (B x) ->
 em_b x = Some v -> finite v /\ B v = rndF (exp (B x) - 1).
Proof.
 intros Fx X Xlo Xs. pose proof (stage_of_ok x Fx X) as SO.
 unfold em_b. revert SO. generalize (stage_of x).
 intros [[[n j] k] r1] [ni [Bn [Fn [Hn [Hjk [Hj [Hk [Fr1 [Br1 [HR [Hr1 [G1 Z1]]]]]]]]]]]].
 assert (Jn : (Z.to_nat j < 512)%nat) by lia.
 pose proof (stage_b_value_ok x n r1 ni (Z.to_nat j) Fx Fn Bn Hn Fr1 Br1 HR Hr1 G1 Z1 Jn) as SV.
 revert SV. generalize (stage_b_value n r1 (Z.to_nat j)). intros [h l] [Fh [Fl [Ah [Al Err]]]] Hd.
 set (r := B x - IZR ni * L) in *.
 set (z := exp (INR (Z.to_nat j) * ln 2 / 512) * exp r) in *.
 assert (Ex : exp (B x) = z * bpow radix2 k).
 { unfold z. rewrite <- exp_split. f_equal. rewrite Z2Nat.id by lia. unfold r. rewrite Hjk. ring. }
 assert (K : (-54 <= k <= 1016)%Z).
 { split; [apply (em_k_lower (B x) ni j); assumption | lia]. }
 destruct em_b_base_ok as [Fb Bb].
 apply (em_decide_ok h l em_b_base k (B x) z v Fh Fl Fb Ah); try assumption.
 - bpow_num_all. lra.
 - rewrite Bb. bpow_num_all. lra.
 - rewrite Bb. bpow_num_all. lra.
 - unfold z. apply z_range; assumption.
Qed.

Definition em_small : f64 := b64_of_bits 4584664420663164928.
Definition em_floor : f64 := b64_of_bits 13853776141233422336.
Lemma em_small_ok : finite em_small /\ B em_small = /32.
Proof. exact (enc_pow2 (-5) ltac:(lia)). Qed.
Lemma em_floor_ok : finite em_floor /\ B em_floor = -37.
Proof.
 split; [exact (bits_finite 13853776141233422336 true 5207287069147136 (-47) eq_refl) | ].
 unfold em_floor. rewrite (bits_val 13853776141233422336 true 5207287069147136 47 eq_refl). simpl cond_Zopp. field.
Qed.
Definition em_screen x :=
 if ExpStageB.screen x then
 match Bcompare 53 1024 em_floor x, Bcompare 53 1024 (b64_abs x) em_small with
 | Some Lt, Some Lt => false
 | Some Lt, Some Eq => true
 | Some Lt, Some Gt => true
 | _, _ => false
 end else false.
Theorem em_screen_ok x : em_screen x = true -> finite x /\ Rabs (B x) < 704 /\ -37 < B x /\ /32 <= Rabs (B x).
Proof.
 unfold em_screen. destruct (ExpStageB.screen x) eqn:S; [ | discriminate].
 destruct (screen_ok x S) as [Fx Ax].
 destruct em_small_ok as [Fs Bs]. destruct em_floor_ok as [Ff Bf].
 assert (Fa : finite (b64_abs x)) by (unfold b64_abs; rewrite is_finite_Babs; exact Fx).
 rewrite !Bcompare_correct by assumption. rewrite Bf, Bs, B_abs.
 destruct (Rcompare (-37) (B x)) eqn:C; try discriminate.
 apply Rcompare_Lt_inv in C.
 destruct (Rcompare (Rabs (B x)) (/32)) eqn:D; try discriminate;
 [apply Rcompare_Eq_inv in D | apply Rcompare_Gt_inv in D]; intros _; repeat split; try assumption; lra.
Qed.
Definition expm1_stages x := if em_screen x then match em_a x with Some v => Some v | None => em_b x end else None.
Theorem expm1_stages_ok x v : expm1_stages x = Some v -> finite v /\ B v = rndF (exp (B x) - 1).
Proof.
 unfold expm1_stages. destruct (em_screen x) eqn:S; [ | discriminate].
 destruct (em_screen_ok x S) as [Fx [Ax [Lx Sx]]].
 destruct (em_a x) as [w | ] eqn:A.
 - intros H. injection H as <-. apply em_a_ok; assumption.
 - apply em_b_ok; assumption.
Qed.

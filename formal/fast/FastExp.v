(** The explicit bounded exponential's accelerated binary64 sequence.
    Unlike stage_a, this entry rounds the stage-A pair directly and does not
    perform a correct-rounding decision. Scaling is exact on its domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingConstant RoundingTest RoundingGaps Grid.
From Interval Require Import Tactic.
Require Import StageGappa ExpStageTables ExpStageReduction ExpStageA.
Open Scope R_scope.

Definition fast_exp_scale64 k := b64_of_bits ((k+1023)*2^52).
Definition fast_exp_entry64 x :=
 let '(n,j,k,r1) := stage_of x in
 let '(h,l) := stage_a_value n r1 (Z.to_nat j) in
 fmul (fadd h l) (fast_exp_scale64 k).

Lemma fast_exp_scale_ok k : (-1016<=k<=1016)%Z ->
 finite (fast_exp_scale64 k) /\ B (fast_exp_scale64 k)=bpow radix2 k.
Proof.
 intros K. unfold fast_exp_scale64.
 replace ((k+1023)*2^52)%Z with (join_bits 52 11 false 0 (k+1023))
   by (rewrite join_eq; ring).
 destruct (join_val 0 (k+1023) ltac:(lia) ltac:(lia)) as [F V].
 split; [exact F|]. rewrite V.
 replace (0+2^52)%Z with (2^52)%Z by ring.
 change (IZR (2^52)) with (bpow radix2 52).
 rewrite <- bpow_plus. f_equal; lia.
Qed.

Lemma fast_exp_scale_exact h k : finite h -> /2<=B h<=4 ->
 (-1016<=k<=1016)%Z ->
 finite (fmul h (fast_exp_scale64 k)) /\
 B (fmul h (fast_exp_scale64 k))=B h*bpow radix2 k.
Proof.
 intros Fh H K. destruct (fast_exp_scale_ok k K) as [Fs S].
 assert (M : (0<=mag radix2 (B h))%Z).
 { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra.
   change (bpow radix2 (0-1)) with (/2). lra. }
 assert (Round : rndF (B h*bpow radix2 k)=B h*bpow radix2 k).
 { rewrite round_scale by (lra || lia).
   rewrite round_generic by (auto with typeclass_instances || apply B_fmt).
   reflexivity. }
 assert (Format : F64 (B h*bpow radix2 k)).
 { rewrite <- Round. apply generic_format_round; auto with typeclass_instances. }
 assert (Bound : Rabs (B h*bpow radix2 k)<bpow radix2 1024).
 { rewrite Rabs_mult, (Rabs_pos_eq (B h)) by lra.
   rewrite (Rabs_pos_eq (bpow radix2 k)) by apply bpow_ge_0.
   apply Rle_lt_trans with (4*bpow radix2 1016).
   - apply Rmult_le_compat; try lra; try apply bpow_ge_0.
     apply bpow_le; lia.
   - change 4 with (bpow radix2 2). rewrite <- bpow_plus. apply bpow_lt; lia. }
 destruct (fmul_exact h (fast_exp_scale64 k) Fh Fs) as [F V].
 - rewrite S. exact Format.
 - rewrite S. exact Bound.
 - split; [exact F|rewrite V,S;reflexivity].
Qed.

Theorem fast_exp_entry_ok x : finite x -> Rabs (B x)<704 ->
 finite (fast_exp_entry64 x) /\
 Rabs (B (fast_exp_entry64 x)-exp (B x))<=bpow radix2 (-51)*exp (B x).
Proof.
 intros Fx X. pose proof (stage_of_ok x Fx X) as SO.
 unfold fast_exp_entry64. revert SO.
 generalize (stage_of x). intros [[[n j] k] r1] SO.
 destruct SO as [ni [Bn [Fn [Hn [Hjk [Hj [Hk [Fr1 [Br1 [HR [Hr1 _]]]]]]]]]]].
 assert (Jn : (Z.to_nat j<512)%nat) by lia.
 pose proof (stage_a_value_ok x n r1 ni (Z.to_nat j) Fx Fn Bn Hn Fr1 Br1 HR Hr1 Jn) as SV.
 revert SV. generalize (stage_a_value n r1 (Z.to_nat j)). intros [h l] SV.
 destruct SV as [Fh [Fl [Hh [Hl Error]]]].
 set (R := B x-IZR ni*L) in *.
 set (z := exp (INR (Z.to_nat j)*ln 2/512)*exp R) in *.
 assert (Z : 9/10<=z<=21/10) by (apply z_range;assumption).
 assert (Ex : exp (B x)=z*bpow radix2 k).
 { unfold z. rewrite <- exp_split. f_equal.
   rewrite Z2Nat.id by lia. unfold R. rewrite Hjk. ring. }
 assert (Sum : /2<=B h+B l<=3).
 { apply Rabs_le_inv in Error. clear - Error Z. bpow_num_all; lra. }
 destruct (fadd16 h l Fh Fl) as [Fa A].
 { rewrite Rabs_pos_eq by lra. lra. }
 assert (Round : Rabs (B (fadd h l)-(B h+B l))<=bpow radix2 (-52)).
 { rewrite A. apply (rnd_err_below _ 2); [lia|].
   change (bpow radix2 2) with 4. rewrite Rabs_pos_eq by lra. lra. }
 assert (A_range : /2<=B (fadd h l)<=4).
 { pose proof (Rabs_le_inv _ _ Error) as E.
   pose proof (Rabs_le_inv _ _ Round) as H.
   clear - Z E H. bpow_num_all; lra. }
 assert (A_error : Rabs (B (fadd h l)-z)<=bpow radix2 (-51)*z).
 { pose proof (Rabs_le_inv _ _ Error) as E.
   pose proof (Rabs_le_inv _ _ Round) as H.
   apply Rabs_le. clear - Z E H. bpow_num_all; nra. }
 destruct (fast_exp_scale_exact (fadd h l) k Fa A_range Hk) as [F V].
 split; [exact F|]. rewrite V,Ex.
 replace (B (fadd h l)*bpow radix2 k-z*bpow radix2 k)
   with ((B (fadd h l)-z)*bpow radix2 k) by ring.
 rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 k)) by apply bpow_ge_0.
 replace (bpow radix2 (-51)*(z*bpow radix2 k))
   with ((bpow radix2 (-51)*z)*bpow radix2 k) by ring.
 apply Rmult_le_compat_r; [apply bpow_ge_0|exact A_error].
Qed.

Theorem fast_exp_entry_positive x : finite x -> Rabs (B x)<704 ->
 0<B (fast_exp_entry64 x).
Proof.
 intros Fx X. destruct (fast_exp_entry_ok x Fx X) as [_ Error].
 pose proof (Rabs_le_inv _ _ Error) as E.
 pose proof (exp_pos (B x)). clear - E H. bpow_num_all; nra.
Qed.

Theorem fast_exp_nonpositive_range x : finite x -> -32<=B x<=0 ->
 bpow radix2 (-47)<=B (fast_exp_entry64 x)<=2.
Proof.
 intros Fx X. assert (Domain : Rabs (B x)<704) by (apply Rabs_lt;lra).
 destruct (fast_exp_entry_ok x Fx Domain) as [_ Error].
 pose proof (Rabs_le_inv _ _ Error) as E.
 assert (Range : 1/100000000000000<=exp (B x)<=1).
 { split; interval with (i_prec 80). }
 clear - E Range. bpow_num_all; nra.
Qed.

(** Public dispatch reuses the existing exp stage screen, equivalent to the
    Rust absolute-value comparison. The strong owner's result is an explicit
    parameter: this theorem does not re-prove the existing strong fallback. *)
Require ExpStageB.
Definition fast_exp_public64 x strong_result :=
 if ExpStageB.screen x then fast_exp_entry64 x else strong_result.

Theorem fast_exp_public_accelerated x strong_result :
 ExpStageB.screen x=true ->
 finite (fast_exp_public64 x strong_result) /\
 Rabs (B (fast_exp_public64 x strong_result)-exp (B x))<=
   bpow radix2 (-51)*exp (B x).
Proof.
 intros Screen. unfold fast_exp_public64;rewrite Screen.
 destruct (ExpStageB.screen_ok x Screen) as [Fx X].
 apply fast_exp_entry_ok;assumption.
Qed.

Theorem fast_exp_public_fallback x strong_result :
 ExpStageB.screen x=false -> fast_exp_public64 x strong_result=strong_result.
Proof. intros Screen;unfold fast_exp_public64;rewrite Screen;reflexivity. Qed.

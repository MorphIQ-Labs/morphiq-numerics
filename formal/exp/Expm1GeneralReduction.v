(** exp's 128-entry fallback reduction, including the table index and scale
    computed from the input. The integer is recovered from the shifter bits;
    it equals n exactly throughout the Rust i32 conversion's proved range. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid.
Require Import ExpReduction ExpStageReduction ExpFast ExpAccurate Ln1pLemmas Ln1pReduction.
Open Scope R_scope.
Definition em_index x :=
 (bits_of_b64 (fadd (fmul x ExpReduction.c_inv_l) ExpReduction.shifter)
  - bits_of_b64 ExpReduction.shifter)%Z.
Definition em_reduce x :=
 let '(n,r1,p2,e2,rh,rl) := ExpReduction.reduce x in
 let ni := em_index x in
 (Z.modulo ni 128, Z.div ni 128, n,r1,p2,e2,rh,rl).

Lemma em_index_ok x : finite x -> -745.1333 <= B x <= 709.79 ->
 B (fsub (fadd (fmul x ExpReduction.c_inv_l) ExpReduction.shifter) ExpReduction.shifter) = IZR (em_index x).
Proof.
 intros Fx X. destruct ExpReduction.c_finite as [Fi _].
 assert (I : 184 <= B ExpReduction.c_inv_l <= 185).
 { rewrite ExpReduction.c_inv_l_val. cbn [F2R Fnum Fexp]. split; interval with (i_prec 64). }
 assert (P : Rabs (B x * B ExpReduction.c_inv_l) <= bpow radix2 18).
 { rewrite Rabs_mult, (Rabs_pos_eq (B ExpReduction.c_inv_l)) by lra.
   assert (Rabs (B x) <= 746) by (apply Rabs_le; lra). change (bpow radix2 18) with 262144. nra. }
 destruct (fmul_s x ExpReduction.c_inv_l Fx Fi) as [Fy By].
 { apply Rle_trans with (1 := P). apply bpow_le; lia. }
 set (y := fmul x ExpReduction.c_inv_l) in *.
 assert (Y : Rabs (B y) <= bpow radix2 18) by (rewrite By; apply rnd_bound; [apply fmt_pow; lia | exact P]).
 assert (Y50 : Rabs (B y) <= bpow radix2 50) by (apply Rle_trans with (1 := Y); apply bpow_le; lia).
 destruct (shifter_add y Fy Y50) as [Ft Bt].
 destruct (ExpReduction.shifter_round y Fy Y50) as [_ Bn].
 set (ni := Znearest ne (B y)) in *.
 assert (N : (Z.abs ni <= 2^50)%Z).
 { pose proof (Znearest_half ne (B y)) as H. fold ni in H.
   assert (Rabs (IZR ni) <= 262145).
   { pose proof (Rabs_triang_inv (IZR ni) (B y)) as T. rewrite Rabs_minus_sym in T. change (bpow radix2 18) with 262144 in Y. lra. }
   rewrite <- abs_IZR in H0. apply le_IZR in H0. lia. }
 unfold em_index. fold y. rewrite (shifted_bits _ ni Ft Bt N), shifter_bits.
 replace (4843621399236968448+ni-4843621399236968448)%Z with ni by ring. exact Bn.
Qed.

Lemma reduce_first x :
 let '(n,_,_,_,_,_) := ExpReduction.reduce x in
 n = fsub (fadd (fmul x ExpReduction.c_inv_l) ExpReduction.shifter) ExpReduction.shifter.
Proof.
 unfold ExpReduction.reduce.
 repeat match goal with
 | |- context [two_prod64 ?a ?b] => destruct (two_prod64 a b)
 | |- context [two_sum64 ?a ?b] => destruct (two_sum64 a b)
 end.
 reflexivity.
Qed.

Theorem em_reduce_ok x : finite x -> -37.43 <= B x -> B x < B ExpFast.c_x_overflow ->
 /32 <= Rabs (B x) ->
 let '(j,k,n,r1,p2,e2,rh,rl) := em_reduce x in
 (0 <= j < 128)%Z /\ (-54 <= k <= 1024)%Z /\
 B n = IZR (128*k+j) /\
 finite rh /\ finite rl /\ B rh = rndF (B rh+B rl) /\
 on_grid (-151) (B rh) /\ on_grid (-151) (B rl) /\
 Rabs (B rh+B rl-(B x-IZR (128*k+j)*(ln 2/128))) <= bpow radix2 (-113) /\
 Rabs (B x-IZR (128*k+j)*(ln 2/128)) <= 0.0027076063 /\
 NZ (acc_r n r1 p2 e2) /\
 Rabs (Q128.qval (acc_r n r1 p2 e2)-(B x-IZR (128*k+j)*(ln 2/128))) <= /2^131.
Proof.
 intros Fx Lo Hi X.
 assert (Over : B ExpFast.c_x_overflow <= 709.783) by (rewrite ExpFast.c_x_overflow_val; interval with (i_prec 64)).
 assert (Range : -745.1333 <= B x <= 709.79) by lra.
 set (dL := ln 2/128-(ExpReduction.l1v+ExpReduction.l2v+ExpReduction.l3v+ExpReduction.l4v)).
 pose proof ExpFast.l_split_dL as DL. fold dL in DL.
 pose proof (ExpReduction.reduce_ok x dL Fx Range DL) as RD.
 pose proof (reduce_first x) as First.
 unfold em_reduce. revert RD First. generalize (ExpReduction.reduce x).
 intros [[[[[n r1] p2] e2] rh] rl] RD First.
 cbv zeta in RD.
 destruct RD as [ni [Bn [Ni [Fn [F1 [F2 [Fe [Fh [Fl [R1 [P2 [E2 [R [Dw [Grid Err]]]]]]]]]]]]]]].
 assert (Index : em_index x = ni) by (apply eq_IZR; rewrite <- Bn, First; symmetry; apply em_index_ok; assumption).
 rewrite Index.
 set (j := (ni mod 128)%Z). set (k := (ni/128)%Z).
 assert (JK : ni = (128*k+j)%Z) by (unfold k,j; apply Z.div_mod; lia).
 assert (J : (0 <= j < 128)%Z) by (unfold j; apply Z.mod_pos_bound; lia).
 assert (L : ExpReduction.l1v+ExpReduction.l2v+ExpReduction.l3v+ExpReduction.l4v+dL = ln 2/128) by (unfold dL; ring).
 rewrite L in R, Err.
 assert (Nreal : -6913 < IZR ni < 131073).
 { apply Rabs_le_inv in R. set (r := B x-IZR ni*(ln 2/128)) in *.
   assert (Lr : 0.0054152123 <= ln 2/128 <= 0.0054152124) by (split; interval with (i_prec 100)).
   replace (IZR ni) with ((B x-r)/(ln 2/128)) by (unfold r; field; lra).
   assert (Xr : -37.43 <= B x <= 709.783) by lra. split; interval with (i_prec 100). }
 apply Rabs_le_inv in R.
 assert (K : (-54 <= k <= 1024)%Z).
 { destruct Nreal as [Nlo Nhi]. apply lt_IZR in Nlo, Nhi. lia. }
 assert (X99 : bpow radix2 (-99) <= Rabs (B x)) by (apply Rle_trans with (/32); [change (/32) with (bpow radix2 (-5)); apply bpow_le; lia | exact X]).
 destruct (Grid X99) as [Gh Gl].
 assert (HL : Rabs (ln 2/128-(ExpReduction.l1v+ExpReduction.l2v+ExpReduction.l3v+ExpReduction.l4v)) <= /2^206).
 { change (Rabs dL <= /2^206). change (-206)%Z with (-Z.of_nat 206)%Z in DL. rewrite ExpFast.bpow_m in DL. exact DL. }
 assert (HR : Rabs (B x-IZR ni*(ln 2/128)) <= 0.0027076063) by (apply Rabs_le; exact R).
 destruct (acc_r_ok x n r1 p2 e2 ni (ln 2/128) Fn F1 F2 Fe Bn Ni R1 P2 E2 HL HR) as [Nr Er].
 rewrite <- JK. repeat split; try assumption; try lia.
Qed.

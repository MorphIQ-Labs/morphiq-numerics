(** The uniform table's actual IEEE reduction, including subnormal inputs. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Encodings Grid.
From Q Require Q128Mul.
Require Import StageGappa ExpReduction ExpStageReduction ErfcxTableSplit ErfcxReciprocal.
Open Scope R_scope.

Definition thirty_two : f64 := b64_of_bits 4629700416936869888.
Definition one_over_thirty_two : f64 := b64_of_bits 4584664420663164928.
Lemma table_scale_ok : finite thirty_two /\ B thirty_two=32 /\
 finite one_over_thirty_two /\ B one_over_thirty_two=/32.
Proof.
 split;[exact (bits_finite 4629700416936869888 false 4503599627370496 (-47) eq_refl)|].
 split.
 - pose proof (bits_val 4629700416936869888 false 4503599627370496 47 eq_refl) as V.
   unfold thirty_two. rewrite V. simpl;field.
 - split;[exact (bits_finite 4584664420663164928 false 4503599627370496 (-57) eq_refl)|].
   pose proof (bits_val 4584664420663164928 false 4503599627370496 57 eq_refl) as V.
   unfold one_over_thirty_two. rewrite V. simpl;field.
Qed.

(** The exponent-scaled table: masks select a binade's 32 midpoints. *)
Definition table_binade64 x : Z*f64*f64*Z :=
 let b := bits_of_b64 x in
 let e := (Z.shiftr b 52-1023)%Z in
 let i := Z.land (Z.shiftr b 47) 31 in
 let c := b64_of_bits (Z.lor (Z.land b (Z.lnot (2^47-1))) (2^46)) in
 ((49+32*e+i)%Z,c,fsub x c,e).

Lemma midpoint_bits b : (0<=b)%Z ->
 Z.lor (Z.land b (Z.lnot (2^47-1))) (2^46) = (b/2^47*2^47+2^46)%Z.
Proof.
 intros Pos. rewrite <-Z.ldiff_land. change (2^47-1)%Z with (Z.ones 47).
 rewrite Z.ldiff_ones_r by lia.
 rewrite Z.lor_comm,Q128Mul.lor_disjoint_low by (try rewrite Z.shiftr_div_pow2 by lia;try apply Z.div_pos;lia).
 rewrite Z.shiftr_div_pow2 by lia. ring.
Qed.

Theorem table_binade_ieee x : finite x -> 1<=B x<16 ->
 let '(i,c,h,e) := table_binade64 x in
 (0<=e<=3)%Z /\ (49+32*e<=i<81+32*e)%Z /\
 finite c /\ finite h /\ B c+B h=B x /\
 B c=(1+(IZR (i-49-32*e)+/2)/32)*bpow radix2 e /\
 Rabs (B h)<=bpow radix2 (e-6).
Proof.
 intros Fx X.
 assert (Normal : bpow radix2 (-1022)<=B x).
 { apply Rle_trans with 1;[change 1 with (bpow radix2 0);apply bpow_le;lia|lra]. }
 destruct (pos_normal x Fx Normal) as [mx [ex [Hx [_ [Mx [Ex [V [Mag [_ Bits]]]]]]]]].
 assert (Magb : (1<=mag radix2 (B x)<=4)%Z).
 { split.
   - apply mag_ge_bpow. change (bpow radix2 (1-1)) with 1. rewrite Rabs_pos_eq by lra;lra.
   - apply mag_le_bpow;[lra|]. change (bpow radix2 4) with 16. rewrite Rabs_pos_eq by lra;lra. }
 assert (E : (-52<=ex<= -49)%Z) by lia.
 set (f := (Zpos mx-2^52)%Z).
 set (q := (f/2^47)%Z).
 assert (F : (0<=f<2^52)%Z) by (unfold f;lia).
 assert (Q : (0<=q<32)%Z).
 { unfold q. split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia. }
 assert (Qf : (q*2^47<=f<(q+1)*2^47)%Z).
 { unfold q. pose proof (Z.mul_div_le f (2^47) ltac:(lia)).
   pose proof (Z.mul_succ_div_gt f (2^47) ltac:(lia)). lia. }
 assert (Sh : Z.shiftr (bits_of_b64 x) 52=(ex+1075)%Z).
 { rewrite Bits,join_eq,Z.shiftr_div_pow2 by lia.
   rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. ring. }
 assert (Div : (bits_of_b64 x/2^47=(ex+1075)*32+q)%Z).
 { rewrite Bits,join_eq. fold f.
   replace ((ex+1075)*2^52+f)%Z with (((ex+1075)*32)*2^47+f)%Z by ring.
   rewrite Z.div_add_l by lia. reflexivity. }
 assert (Ix : Z.land (Z.shiftr (bits_of_b64 x) 47) 31=q).
 { change 31%Z with (Z.ones 5). rewrite Z.land_ones,Z.shiftr_div_pow2 by lia.
   rewrite Div. change (2^5)%Z with 32%Z. rewrite Z.add_comm,Z.mod_add by lia.
   apply Z.mod_small;exact Q. }
 assert (Cb : Z.lor (Z.land (bits_of_b64 x) (Z.lnot (2^47-1))) (2^46)=
   join_bits 52 11 false (q*2^47+2^46) (ex+1075)).
 { rewrite midpoint_bits,Div,join_eq;[ring|rewrite Bits,join_eq;lia]. }
 destruct (join_val (q*2^47+2^46) (ex+1075) ltac:(lia) ltac:(lia)) as [Fc Bc].
 replace (ex+1075-1075)%Z with ex in Bc by ring.
 set (c := b64_of_bits (join_bits 52 11 false (q*2^47+2^46) (ex+1075))) in *.
 assert (D : Rabs (B x-B c)<=bpow radix2 (ex+46)).
 { rewrite V,Bc.
   replace (IZR (Zpos mx)*bpow radix2 ex-IZR (q*2^47+2^46+2^52)*bpow radix2 ex)
    with (IZR (Zpos mx-(q*2^47+2^46+2^52))*bpow radix2 ex)
    by (rewrite minus_IZR;ring).
   rewrite Rabs_mult,(Rabs_pos_eq (bpow radix2 ex)) by apply bpow_ge_0.
   rewrite bpow_plus. replace (bpow radix2 46) with (IZR (2^46)) by reflexivity.
   replace (bpow radix2 ex*IZR (2^46)) with (IZR (2^46)*bpow radix2 ex) by ring.
   apply Rmult_le_compat_r;[apply bpow_ge_0|].
   rewrite <-abs_IZR. apply IZR_le. unfold f in Qf. lia. }
 assert (Gx : on_grid ex (B x)) by (exists (Zpos mx);exact V).
 assert (Gc : on_grid ex (B c)) by (exists (q*2^47+2^46+2^52)%Z;exact Bc).
 assert (Fmt : fmtF (B x-B c)).
 { apply (Ln1pReduction.grid_repr ex);[lia|apply grid_minus;assumption|].
   apply Rle_lt_trans with (1:=D). apply bpow_lt;lia. }
 assert (Small : Rabs (B x-B c)<=1).
 { apply Rle_trans with (1:=D). change 1 with (bpow radix2 0). apply bpow_le;lia. }
 destruct (fsub_ok 1 0 x c Fx Fc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_l;change (bpow radix2 0) with 1;exact Small)) as [Fh Bh].
 rewrite round_generic in Bh by (exact _ || exact Fmt).
 unfold table_binade64. cbv zeta. rewrite Sh,Ix,Cb. fold c.
 replace (ex+1075-1023)%Z with (ex+52)%Z by ring.
 repeat split;try assumption;try lia;try lra.
 - rewrite Bc. replace (49+32*(ex+52)+q-49-32*(ex+52))%Z with q by ring.
   rewrite !plus_IZR,mult_IZR,bpow_plus.
   change (IZR (2^47)) with 140737488355328.
   change (IZR (2^46)) with 70368744177664.
   change (IZR (2^52)) with 4503599627370496.
   change (bpow radix2 52) with 4503599627370496. field.
 - rewrite Bh. replace (ex+52-6)%Z with (ex+46)%Z by ring. exact D.
Qed.

(** Reading the shifted encoding gives the same integer as the Rust i32
    conversion; the theorem proves both integrality and its in-range value. *)
Definition uniform_index x :=
 (bits_of_b64 (fadd (fmul x thirty_two) shifter)-bits_of_b64 shifter+16)%Z.
Definition table_uniform64 x : Z*f64*f64 :=
 let n := fsub (fadd (fmul x thirty_two) shifter) shifter in
 let c := fmul n one_over_thirty_two in
 (uniform_index x,c,fsub x c).

Theorem table_uniform_ieee x : finite x -> -/2<=B x<=1 ->
 let '(i,c,h) := table_uniform64 x in
 (0<=i<=48)%Z /\ finite c /\ finite h /\
 B c=IZR (i-16)/32 /\ B c+B h=B x /\ Rabs (B h)<=/64 /\
 (i-16)%Z=Znearest ne (32*B x) /\
 B (fsub (fadd (fmul x thirty_two) shifter) shifter)=IZR (i-16).
Proof.
 intros Fx X. destruct table_scale_ok as [Fs [Bs [Fi Bi]]].
 destruct (fmul_ok 1 5 x thirty_two Fx Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Bs,Rmult_1_l;change (bpow radix2 5) with 32;apply Rabs_le;lra)) as [Fy By].
 assert (Ye : B (fmul x thirty_two)=B x*32).
 { rewrite By,Bs. change 32 with (bpow radix2 5).
   apply round_generic;[exact _|]. apply mult_bpow_pos_exact_FLT;[apply B_fmt|lia]. }
 destruct (shifter_round (fmul x thirty_two) Fy
   ltac:(rewrite Ye;change (bpow radix2 50) with 1125899906842624;apply Rabs_le;lra)) as [Fn Bn].
 set (n := fsub (fadd (fmul x thirty_two) shifter) shifter) in *.
 rewrite Ye in Bn. set (K := Znearest ne (B x*32)) in *.
 assert (Near : Rabs (B x*32-IZR K)<=/2) by (unfold K;apply Znearest_half).
 assert (Kb : (-16<=K<=32)%Z).
 { pose proof (Rabs_le_inv _ _ Near) as N.
   assert (L : IZR (-17)<IZR K) by (change (IZR (-17)) with (-17);lra).
   assert (U : IZR K<IZR 33) by (change (IZR 33) with 33;lra).
   apply lt_IZR in L,U. lia. }
 assert (Kr : -16<=IZR K<=32).
 { split;[change (-16) with (IZR (-16))|change 32 with (IZR 32)];apply IZR_le;lia. }
 destruct (fmul_ok 1 0 n one_over_thirty_two Fn Fi ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Bn,Bi,Rmult_1_l;change (bpow radix2 0) with 1;apply Rabs_le;lra)) as [Fc Bc].
 assert (Ce : B (fmul n one_over_thirty_two)=IZR K*bpow radix2 (-5)).
 { rewrite Bc,Bn,Bi. change (/32) with (bpow radix2 (-5)). apply round_generic;[exact _|].
   apply generic_format_FLT. exists (Float radix2 K (-5)).
   - reflexivity.
   - change (Z.abs K<9007199254740992)%Z. lia.
   - change (-1074<= -5)%Z. lia. }
 destruct (nearest_residual_ieee x (fmul n one_over_thirty_two) (-5) K Fx Fc ltac:(lia) Ce
  ltac:(change (bpow radix2 (- -5)) with 32;exact Near)) as [Fh [Bh Hb]].
 assert (Index : uniform_index x=(K+16)%Z).
 { destruct (shifter_add (fmul x thirty_two) Fy
    ltac:(rewrite Ye;change (bpow radix2 50) with 1125899906842624;apply Rabs_le;lra)) as [Ft Bt].
   rewrite Ye in Bt. fold K in Bt. unfold uniform_index.
   rewrite (shifted_bits _ K Ft Bt ltac:(lia)),shifter_bits. ring. }
 unfold table_uniform64. fold n. rewrite Index.
 change (bpow radix2 (-5-1)) with (/64) in Hb.
 change (bpow radix2 (-5)) with (/32) in Ce.
 repeat split;try assumption;try lia;try lra.
 - replace (K+16-16)%Z with K by ring. exact Ce.
 - rewrite Bh. exact Hb.
 - replace (K+16-16)%Z with K by ring. unfold K. rewrite Rmult_comm. reflexivity.
 - replace (K+16-16)%Z with K by ring. exact Bn.
Qed.


Definition table_reduce64 x : Z*f64*f64*Z :=
 match Bcompare 53 1024 x ErfcxReciprocal.one with
 | Some Lt => let '(i,c,h) := table_uniform64 x in (i,c,h,0%Z)
 | _ => table_binade64 x
 end.

Theorem table_reduce_ieee x : finite x -> -/2<=B x<16 ->
 let '(i,c,h,e) := table_reduce64 x in
 (0<=i<177)%Z /\ (0<=e<=3)%Z /\ finite c /\ finite h /\
 B c+B h=B x /\ Rabs (B h)<=bpow radix2 (e-6).
Proof.
 intros Fx X. destruct ErfcxReciprocal.one_ok as [Fo Bo].
 unfold table_reduce64. rewrite (Bcompare_correct 53 1024 x ErfcxReciprocal.one Fx Fo),Bo.
 destruct (Rcompare_spec (B x) 1) as [L|Eq|G].
 - pose proof (table_uniform_ieee x Fx ltac:(lra)) as T.
   destruct (table_uniform64 x) as [[i c] h].
   change (bpow radix2 (0-6)) with (/64). cbv zeta in T.
   destruct T as [I [Fc [Fh [C [H [Hb _]]]]]]. repeat split;try lia;assumption.
 - pose proof (table_binade_ieee x Fx ltac:(lra)) as T.
   destruct (table_binade64 x) as [[[i c] h] e]. cbv zeta in T.
   destruct T as [E [I [Fc [Fh [H [C Hb]]]]]]. repeat split;try lia;assumption.
 - pose proof (table_binade_ieee x Fx ltac:(lra)) as T.
   destruct (table_binade64 x) as [[[i c] h] e]. cbv zeta in T.
   destruct T as [E [I [Fc [Fh [H [C Hb]]]]]]. repeat split;try lia;assumption.
Qed.

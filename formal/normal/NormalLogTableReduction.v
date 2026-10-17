(** Exact half-unit reduction for the first log-tail table. *)
(** The uniform table's actual IEEE reduction, including subnormal inputs. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Encodings Grid.
From Q Require Q128Mul.
Require Import ErfcxTableReduction.
Require Import StageGappa ExpReduction ExpStageReduction ErfcxTableSplit ErfcxReciprocal.
Open Scope R_scope.

Theorem normal_log_table_reduce_ieee x : finite x -> 37<=B x<64 ->
 let '(i,c,h,e) := table_binade64 x in
 e=5%Z /\ (214<=i<241)%Z /\
 finite c /\ finite h /\ B c+B h=B x /\
 B c=(1+(IZR (i-49-32*e)+/2)/32)*bpow radix2 e /\
 Rabs (B h)<=bpow radix2 (e-6).
Proof.
 intros Fx X.
 assert (Normal : bpow radix2 (-1022)<=B x).
 { apply Rle_trans with 1;[change 1 with (bpow radix2 0);apply bpow_le;lia|lra]. }
 destruct (pos_normal x Fx Normal) as [mx [ex [Hx [_ [Mx [Ex [V [Mag [_ Bits]]]]]]]]].
 assert (Magb : (6<=mag radix2 (B x)<=6)%Z).
 { split.
   - apply mag_ge_bpow. change (bpow radix2 (6-1)) with 32. rewrite Rabs_pos_eq by lra;lra.
   - apply mag_le_bpow;[lra|]. change (bpow radix2 6) with 64. rewrite Rabs_pos_eq by lra;lra. }
 assert (E : (-47<=ex<= -47)%Z) by lia.
 set (f := (Zpos mx-2^52)%Z).
 set (q := (f/2^47)%Z).
 assert (F : (0<=f<2^52)%Z) by (unfold f;lia).
 assert (Fmin : (5*2^47<=f)%Z).
 { apply le_IZR. unfold f. rewrite minus_IZR.
   assert (Ex47 : ex=(-47)%Z) by lia.
   rewrite Ex47 in V. bpow_num_all. simpl. lra. }
 assert (Q : (5<=q<32)%Z).
 { unfold q. split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];lia. }
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
   apply Z.mod_small;lia. }
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

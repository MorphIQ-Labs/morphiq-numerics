(** Exact exponent-field scaling of the generated high words. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Encodings.
Require Import ExpStageTables.
Import ListNotations.
Open Scope R_scope.
Definition fast_high_bits j := fst (nth j st_t_bits (0%Z,0%Z)).
Definition fast_high64 j := b64_of_bits (fast_high_bits j).
Definition fast_scaled_high64 j k :=
 b64_of_bits ((fast_high_bits j+k*2^52) mod 2^64).
Lemma fast_high_encoding j : (j<512)%nat ->
 (1023*2^52<=fast_high_bits j<1024*2^52)%Z.
Proof.
 intros J.
 assert (All:forallb (fun p => (1023*2^52<=?fst p)%Z && (fst p<?1024*2^52)%Z) st_t_bits=true).
 { vm_compute;reflexivity. }
 apply forallb_forall with (x:=nth j st_t_bits (0%Z,0%Z)) in All.
 - apply andb_true_iff in All as [L U]. apply Z.leb_le in L;apply Z.ltb_lt in U. exact (conj L U).
 - apply nth_In. change (j<512)%nat;exact J.
Qed.
Lemma fast_scaled_high_ok j k : (j<512)%nat -> (-1016<=k<=1016)%Z ->
 finite(fast_scaled_high64 j k) /\
 B(fast_scaled_high64 j k)=B(fast_high64 j)*bpow radix2 k.
Proof.
 intros J K. pose proof (fast_high_encoding j J) as H.
 set (m:=(fast_high_bits j-1023*2^52)%Z).
 assert (M:(0<=m<2^52)%Z) by (unfold m;lia).
 assert (Plain:fast_high_bits j=join_bits 52 11 false m 1023).
 { rewrite join_eq;unfold m;ring. }
 assert (Scaled:((fast_high_bits j+k*2^52) mod 2^64)%Z=join_bits 52 11 false m (1023+k)).
 { rewrite Z.mod_small by lia. rewrite join_eq;unfold m;ring. }
 destruct (join_val m 1023 M ltac:(lia)) as [Fh Vh].
 destruct (join_val m (1023+k) M ltac:(lia)) as [Fs Vs].
 unfold fast_scaled_high64;rewrite Scaled. split;[exact Fs|].
 unfold fast_high64;rewrite Plain,Vh,Vs.
 rewrite Rmult_assoc,<-bpow_plus. f_equal;f_equal;lia.
Qed.

(** The shifter encoding is divisible by 2^21. Hence taking raw bits 9..20
    and shifting them into the exponent is the same modular scale as using
    the signed reduced integer. This also covers negative reduced integers. *)
Lemma fast_raw_scale j raw :
 fast_scaled_high64 j (Z.shiftr (raw-4843621399236968448) 9)=
 b64_of_bits ((fast_high_bits j+Z.shiftl (Z.shiftr raw 9) 52) mod 2^64).
Proof.
 unfold fast_scaled_high64. rewrite !Z.shiftr_div_pow2 by lia.
 rewrite Z.shiftl_mul_pow2 by lia.
 set (q:=(4843621399236968448/512)%Z).
 set (d:=(4843621399236968448/2^21)%Z).
 assert (Q:(4843621399236968448=q*512)%Z) by (unfold q;vm_compute;reflexivity).
 assert (D:(q*2^52=d*2^64)%Z) by (unfold q,d;vm_compute;reflexivity).
 change (2^9)%Z with 512%Z.
 replace (raw-4843621399236968448)%Z with (raw+(-q)*512)%Z by (rewrite Q;ring).
 rewrite Z.div_add by lia.
 replace (fast_high_bits j+(raw/512+-q)*2^52)%Z with
   ((fast_high_bits j+(raw/512)*2^52)+(-d)*2^64)%Z by nia.
 rewrite Z.mod_add by lia;reflexivity.
Qed.

Lemma fast_raw_index raw :
 Z.land raw 511=Z.land (raw-4843621399236968448) 511.
Proof.
 change 511%Z with (Z.ones 9).
 rewrite !Z.land_ones by lia. change (2^9)%Z with 512%Z.
 replace (raw-4843621399236968448)%Z with
   (raw+(-9460198045384704)*512)%Z by ring.
 rewrite Z.mod_add by lia;reflexivity.
Qed.

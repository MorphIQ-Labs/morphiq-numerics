(** Integer-domain certificate for the shared open uniform and octant fold.
    Their casts and power-of-two scaling are exact (docs/random.md). *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
Require Import FastRandomAngular FastRandomBound.
Open Scope R_scope.

Definition bm_word_uniform w := IZR(2*(w/4096)+1)/2^53.
Definition bm_word_m w : Z :=
 let k:=(w/2048)%Z in let o:=(k/2^50)%Z in let j:=(k mod 2^50)%Z in
 if Z.odd o then (2^50-j)%Z else j.
Definition bm_word_angle w := rndF(8*bm_limit*(IZR(bm_word_m w)/2^53)).

Theorem bm_word_uniform_range w : (0<=w<2^64)%Z ->
 bm_unit<=bm_word_uniform w<=1-bm_unit.
Proof.
 intros W. assert (Q:(0<=w/4096<2^52)%Z).
 { split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
 assert (N:(1<=2*(w/4096)+1<=2^53-1)%Z) by lia.
 destruct N as [Lo Hi]. apply IZR_le in Lo. apply IZR_le in Hi.
 unfold bm_word_uniform,bm_unit.
 replace ((2:R)^53) with 9007199254740992 by ring.
 change (1<=IZR(2*(w/4096)+1)) in Lo.
 change (IZR(2*(w/4096)+1)<=9007199254740991) in Hi. lra.
Qed.

Theorem bm_word_m_range w : (0<=bm_word_m w<=2^50)%Z.
Proof.
 unfold bm_word_m;cbv zeta.
 pose proof (Z.mod_pos_bound (w/2048) (2^50) ltac:(lia)) as J.
 destruct (Z.odd ((w/2048)/2^50));lia.
Qed.

Lemma bm_limit_format : fmtF bm_limit.
Proof.
 replace bm_limit with (B(b64_of_bits 4605249457297304856)).
 - apply B_fmt.
 - rewrite (bits_val 4605249457297304856 false 7074237752028440 53 eq_refl).
   unfold bm_limit;cbn;field.
Qed.

Theorem bm_word_angle_range w : 0<=bm_word_angle w<=bm_limit.
Proof.
 pose proof (bm_word_m_range w) as [Lo Hi].
 apply IZR_le in Lo. apply IZR_le in Hi.
 change (0<=IZR(bm_word_m w)) in Lo.
 change (IZR(bm_word_m w)<=1125899906842624) in Hi.
 assert (V:0<=8*bm_limit*(IZR(bm_word_m w)/2^53)<=bm_limit).
 { unfold bm_limit. replace ((2:R)^53) with 9007199254740992 by ring. nra. }
 unfold bm_word_angle. split.
 - replace 0 with (rndF 0) at 1 by (rewrite round_0 by exact _;reflexivity).
   apply round_le;auto with typeclass_instances;lra.
 - apply round_le_generic;auto with typeclass_instances;[apply bm_limit_format|lra].
Qed.

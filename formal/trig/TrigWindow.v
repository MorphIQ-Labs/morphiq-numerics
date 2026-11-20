(** The integer portion of trig/mod.rs::reduce: table-word extraction, the
    five-limb window and its six-limb product. Constants come from the same
    generator as Rust. Every supported exponent is checked in the kernel. *)
From Coq Require Import ZArith Lia Psatz List Bool.
From Q Require Import Limbs Shifts Q256.
From Binary64 Require Import IEEE64.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
Require Import TrigConstants.
Import ListNotations.
Open Scope Z_scope.

Definition trig_two_bits (last : Z) : Z :=
  if last <? 1 then 0 else
  let p := last-1 in let w := p/64 in let o := p mod 64 in
  let here := Z.shiftr (nth (Z.to_nat w) trig_two_over_pi_words 0) (63-o) in
  if (o =? 63) || (w =? 0) then here else
  Z.lor here (u64_shl (nth (Z.to_nat (w-1)) trig_two_over_pi_words 0) (o+1)).

Definition trig_window_limb (e j : Z) : Z :=
  let i0 := Z.max (e-1) 1 in
  let last := e+trig_fraction_bits-64*j in
  let keep := last-i0 in
  if keep <? 0 then 0 else
  if 63 <=? keep then trig_two_bits last else
  Z.land (trig_two_bits last) (Z.shiftl 1 (keep+1)-1).
Definition trig_window e := map (trig_window_limb e) [0;1;2;3;4].
Definition trig_prefix e := trig_two_over_pi / 2^(1408-(e+trig_fraction_bits)).

Definition trig_two_bits_safe last :=
  if last <? 1 then true else
  let p:=last-1 in let w:=p/64 in let o:=p mod 64 in
  (0<=?w) && (w<?Z.of_nat (length trig_two_over_pi_words)) &&
  (0<=?63-o) && (63-o<?64) &&
  (if (o=?63)||(w=?0) then true else
    (0<=?w-1) && (0<=?o+1) && (o+1<?64)).
Definition trig_window_step_safe e j :=
  let last:=e+trig_fraction_bits-64*j in
  let keep:=last-Z.max (e-1) 1 in
  if keep<?0 then true else
  trig_two_bits_safe last &&
  (if 63<=?keep then true else (0<=?keep+1)&&(keep+1<?64)).
Definition trig_window_check e :=
  let ws:=trig_window e in
  (Limbs.v ws =? trig_prefix e mod 2^317) &&
  forallb (fun x => (0<=?x)&&(x<?Limbs.B)) ws &&
  forallb (trig_window_step_safe e) [0;1;2;3;4].
Definition trig_window_exponents := map (fun n => Z.of_nat n-53) (seq 0 1025).

Theorem trig_window_checked : forallb trig_window_check trig_window_exponents=true.
Proof. vm_compute; reflexivity. Qed.

Lemma trig_window_check_all e : -53<=e<=971 -> trig_window_check e=true.
Proof.
  intro E. pose proof trig_window_checked as V.
  rewrite forallb_forall in V. apply V.
  unfold trig_window_exponents. apply in_map_iff.
  exists (Z.to_nat (e+53)). split.
  - rewrite Z2Nat.id by lia; lia.
  - apply in_seq. split; [lia|]. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia; simpl; lia.
Qed.

Theorem trig_window_exact e : -53<=e<=971 ->
  limbs_ok (trig_window e) /\ length (trig_window e)=5%nat /\
  Limbs.v (trig_window e)=trig_prefix e mod 2^317 /\
  forallb (trig_window_step_safe e) [0;1;2;3;4]=true.
Proof.
  intro E. pose proof (trig_window_check_all e E) as V.
  unfold trig_window_check in V. rewrite !andb_true_iff,Z.eqb_eq in V.
  destruct V as [[Value Words] Safe]. split.
  - apply Forall_forall. intros x X. rewrite forallb_forall in Words.
    specialize (Words x X). rewrite andb_true_iff,Z.leb_le,Z.ltb_lt in Words; exact Words.
  - split; [reflexivity|]. split; assumption.
Qed.

(** The source's u128 multiply/carry step cannot overflow. *)
Theorem trig_product_step_fits m word carry :
  0<=m<Limbs.B -> 0<=word<Limbs.B -> 0<=carry<Limbs.B ->
  0<=m*word+carry<2^128.
Proof.
  intros M W C. change (0<=m*word+carry<Limbs.B*Limbs.B).
  pose proof Limbs.B_pos; nia.
Qed.

Definition trig_product e m :=
  let ws:=trig_window e in
  let '(out,carry):=mac m ws (repeat 0 (length ws)) 0 in out++[carry].
Lemma trig_zero_limbs n : Limbs.v (repeat 0 n)=0 /\ limbs_ok (repeat 0 n).
Proof.
  induction n as [|n [V O]]; cbn [repeat Limbs.v]; split; try reflexivity.
  - constructor.
  - rewrite V; ring.
  - constructor; [pose proof Limbs.B_pos; lia|exact O].
Qed.

Theorem trig_product_exact e m : -53<=e<=971 -> 0<=m<2^53 ->
  limbs_ok (trig_product e m) /\ length (trig_product e m)=6%nat /\
  Limbs.v (trig_product e m)=m*(trig_prefix e mod 2^317).
Proof.
  intros E M. destruct (trig_window_exact e E) as [W [Len [Value Safe]]].
  assert (Mb : 0<=m<Limbs.B) by (unfold Limbs.B; lia).
  destruct (trig_zero_limbs (length (trig_window e))) as [Zero Zok].
  pose proof (mac_ok m (trig_window e) (repeat 0 (length (trig_window e))) 0
    ltac:(rewrite repeat_length; reflexivity) Mb W Zok ltac:(pose proof Limbs.B_pos; lia)) as P.
  unfold trig_product. destruct (mac m (trig_window e) (repeat 0 (length (trig_window e))) 0) as [out carry].
  destruct P as [Product [O [C L]]]. split.
  - apply limbs_ok_app; [exact O|]. constructor; [exact C|constructor].
  - split.
    + rewrite app_length,L,Len; reflexivity.
    + rewrite v_app,L. cbn [Limbs.v]. rewrite Zero,Value in Product. lia.
Qed.

(** Complete executable reduction transcription for the Rust/Coq comparison.
    The window/product theorems above do not establish the final remainder
    bound; quadrant selection and reconstruction are separate obligations. *)
Definition trig_reduce_large (bits : Z) : Z * q256 :=
  let m:=Z.lor (Z.land bits (2^52-1)) (Z.shiftl 1 52) in
  let e:=Z.shiftr bits 52-1075 in
  let product:=trig_product e m in
  let word:=trig_fraction_bits/64 in let bit:=trig_fraction_bits mod 64 in
  let k:=Z.land (Z.land
    (Z.lor (Z.shiftr (nth (Z.to_nat word) product 0) bit)
      (u64_shl (nth (Z.to_nat (word+1)) product 0) (64-bit))) (2^32-1)) 3 in
  let fraction:=firstn (Z.to_nat word) product ++
    [Z.land (nth (Z.to_nat word) product 0) (2^bit-1)] in
  let negative:=Z.shiftr (nth (Z.to_nat word) fraction 0) (bit-1)=?1 in
  let '(quadrant,mag):=
    if negative then
      let '(raw,_):=sub_chain (repeat 0 5) fraction 0 in
      (Z.land (k+1) 3, firstn (Z.to_nat word) raw ++
        [Z.land (nth (Z.to_nat word) raw 0) (2^bit-1)])
    else (k,fraction) in
  let f:=Q256.from_limbs negative mag (-trig_fraction_bits) in
  (quadrant,Q256.mul f (Q256.new false trig_half_pi_words trig_half_pi_exponent)).
Definition trig_reduce64 bits : Z * q256 :=
  match Bcompare 53 1024 (b64_of_bits bits) (b64_of_bits 4605249457297304856) with
  | Some Lt | Some Eq => (0,Q256.from_f64 bits)
  | _ => trig_reduce_large bits
  end.

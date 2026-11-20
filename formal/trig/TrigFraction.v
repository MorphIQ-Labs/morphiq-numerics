(** The limb-level quadrant and fractional-part decision in trig::reduce.
    Every helper is definitionally tied to the executable transcription. *)
From Coq Require Import ZArith Lia List.
From Q Require Import Limbs Shifts Q256.
Require Import TrigConstants TrigWindow.
Import ListNotations.
Open Scope Z_scope.
Definition trig_fraction (p : list Z) := firstn 4 p ++ [Z.land (nth 4 p 0) (2^59-1)].
Lemma trig_fraction_value p : limbs_ok p -> (5<=length p)%nat ->
  limbs_ok (trig_fraction p) /\ length (trig_fraction p)=5%nat /\
  v (trig_fraction p)=v p mod 2^315.
Proof.
  intros O L. destruct p as [|a [|b [|c [|d [|e p]]]]];
    cbn [length] in L; try lia.
  unfold limbs_ok in O. repeat rewrite Forall_cons_iff in O.
  destruct O as [A [B0 [C [D [E0 Rest]]]]].
  assert (Low : 0<=v [a;b;c;d]<B^4).
  { apply v_bounds. repeat (apply Forall_cons; [assumption|]); apply Forall_nil. }
  assert (M : 0<=e mod 2^59<2^59) by (apply Z.mod_pos_bound; lia).
  unfold trig_fraction. cbn [firstn nth app].
  change (2^59-1) with (Z.ones 59). rewrite Z.land_ones by lia.
  assert (E : v (a::b::c::d::e::p) = v [a;b;c;d;e mod 2^59] +
      (e/2^59+32*v p)*2^315).
  { pose proof (Z.div_mod e (2^59) ltac:(lia)) as Div.
    cbn [v]; unfold B. nia. }
  split.
  - repeat (apply Forall_cons; [unfold B in *; lia|]); apply Forall_nil.
  - split; [reflexivity|]. rewrite E,Z.mod_add by lia.
    symmetry. apply Z.mod_small.
    cbn [v] in Low |- *. unfold B in *; lia.
Qed.

Definition trig_quadrant p :=
  Z.land (Z.land (Z.lor (Z.shiftr (nth 4 p 0) 59)
    (u64_shl (nth 5 p 0) 5)) (2^32-1)) 3.
Definition trig_negative f := (Z.shiftr (nth 4 f 0) 58 =? 1).
Definition trig_complement f :=
  let '(raw,_):=sub_chain (repeat 0 5) f 0 in trig_fraction raw.
Definition trig_select p :=
  let k:=trig_quadrant p in let f:=trig_fraction p in
  if trig_negative f then (Z.land (k+1) 3,trig_complement f) else (k,f).

Theorem trig_reduce_large_parts bits : trig_reduce_large bits =
  let m:=Z.lor (Z.land bits (2^52-1)) (Z.shiftl 1 52) in
  let e:=Z.shiftr bits 52-1075 in let p:=trig_product e m in
  let '(k,mag):=trig_select p in
  (k,Q256.mul
    (Q256.from_limbs (trig_negative (trig_fraction p)) mag (-trig_fraction_bits))
    (Q256.new false trig_half_pi_words trig_half_pi_exponent)).
Proof. reflexivity. Qed.

Lemma trig_mod_nested x a b : 0<a -> 0<b -> (a | b) ->
  (x mod b) mod a=x mod a.
Proof.
  intros A B [k K]. pose proof (Z.div_mod x b ltac:(lia)) as D.
  replace x with (x mod b+(k*(x/b))*a) at 2 by nia.
  rewrite Z.mod_add by lia; reflexivity.
Qed.

Theorem trig_quadrant_value p : limbs_ok p -> length p=6%nat ->
  trig_quadrant p=(v p/2^315) mod 4.
Proof.
  intros O L. destruct p as [|a [|b [|c [|d [|e [|f p]]]]]];
    cbn [length] in L; try discriminate.
  destruct p; [|discriminate].
  unfold limbs_ok in O. repeat rewrite Forall_cons_iff in O.
  destruct O as [A [B0 [C [D [E0 [F _]]]]]].
  assert (Low : 0<=v [a;b;c;d]<B^4).
  { apply v_bounds. repeat (apply Forall_cons; [assumption|]); apply Forall_nil. }
  assert (Eq : 0<=e/2^59<2^5).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; unfold B in *; lia. }
  unfold trig_quadrant. cbn [nth].
  rewrite Z.shiftr_div_pow2, u64_shl_mul by lia.
  rewrite Z.lor_comm,lor_low_high by lia.
  change (2^32-1) with (Z.ones 32). change 3 with (Z.ones 2).
  rewrite !Z.land_ones by lia. change (2^2) with 4.
  rewrite trig_mod_nested by (try lia; exists (2^30); reflexivity).
  assert (Mod : ((f*2^5) mod B+e/2^59) mod 4=(e/2^59) mod 4).
  { pose proof (Z.div_mod (f*2^5) B ltac:(unfold B; lia)) as T.
    replace ((f*2^5) mod B+e/2^59) with
      (e/2^59+(8*f-2^62*((f*2^5)/B))*4) by (unfold B in *; lia).
    apply Z.mod_add; lia. }
  rewrite Mod.
  assert (Rem : 0<=v [a;b;c;d;e mod 2^59]<2^315).
  { pose proof (Z.mod_pos_bound e (2^59) ltac:(lia)).
    cbn [v] in Low |- *. unfold B in *; lia. }
  assert (Value : v [a;b;c;d;e;f] =
    v [a;b;c;d;e mod 2^59]+(e/2^59+32*f)*2^315).
  { pose proof (Z.div_mod e (2^59) ltac:(lia)). cbn [v]; unfold B; nia. }
  rewrite Value,Z.div_add by lia. rewrite (Z.div_small (v [a;b;c;d;e mod 2^59]) (2^315) Rem).
  replace (0+(e/2^59+32*f)) with (e/2^59+(8*f)*4) by ring.
  rewrite Z.mod_add by lia; reflexivity.
Qed.

Theorem trig_negative_value f : limbs_ok f -> length f=5%nat ->
  0<=v f<2^315 -> (trig_negative f=true <-> 2^314<=v f).
Proof.
  intros O L V. destruct f as [|a [|b [|c [|d [|e f]]]]];
    cbn [length] in L; try discriminate.
  destruct f; [|discriminate].
  unfold limbs_ok in O. repeat rewrite Forall_cons_iff in O.
  destruct O as [A [B0 [C [D [E0 _]]]]].
  assert (Low : 0<=v [a;b;c;d]<B^4).
  { apply v_bounds. repeat (apply Forall_cons; [assumption|]); apply Forall_nil. }
  assert (Top : 0<=e<2^59).
  { cbn [v] in V. unfold B in *; lia. }
  assert (Q : 0<=e/2^58<2).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  pose proof (Z.div_mod e (2^58) ltac:(lia)) as Eq.
  pose proof (Z.mod_pos_bound e (2^58) ltac:(lia)) as Rem.
  unfold trig_negative. cbn [nth]. rewrite Z.shiftr_div_pow2,Z.eqb_eq by lia.
  cbn [v] in Low |- *. unfold B in *; lia.
Qed.

Theorem trig_complement_value f : limbs_ok f -> length f=5%nat ->
  0<v f<2^315 -> limbs_ok (trig_complement f) /\
  length (trig_complement f)=5%nat /\ v (trig_complement f)=2^315-v f.
Proof.
  intros O L V. destruct (trig_zero_limbs 5) as [Zero Zok].
  pose proof (sub_chain_ok (repeat 0 5) f 0 ltac:(rewrite repeat_length,L; reflexivity)
    Zok O ltac:(lia)) as S.
  unfold trig_complement. destruct (sub_chain (repeat 0 5) f 0) as [raw borrow].
  destruct S as [Value [R [Borrow Len]]].
  rewrite repeat_length in Value,Len. rewrite Zero in Value.
  assert (Borrow1 : borrow=1).
  { pose proof (v_nonneg raw R). unfold B in Value. lia. }
  rewrite Borrow1 in Value. change (Z.of_nat 5) with 5 in Value.
  destruct (trig_fraction_value raw R ltac:(lia)) as [O' [L' F]].
  split; [exact O'|]. split; [exact L'|]. rewrite F.
  replace (v raw) with ((2^315-v f)+31*2^315) by (unfold B in Value; lia).
  rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Definition trig_nearest_integer p :=
  v p/2^315 + if trig_negative (trig_fraction p) then 1 else 0.

Theorem trig_select_exact p : limbs_ok p -> length p=6%nat ->
  fst (trig_select p)=trig_nearest_integer p mod 4 /\
  limbs_ok (snd (trig_select p)) /\ length (snd (trig_select p))=5%nat /\
  (if trig_negative (trig_fraction p) then -v (snd (trig_select p))
   else v (snd (trig_select p))) = v p-trig_nearest_integer p*2^315 /\
  -2^314<=v p-trig_nearest_integer p*2^315<2^314.
Proof.
  intros O L. destruct (trig_fraction_value p O ltac:(lia)) as [Fo [Fl Fv]].
  pose proof (trig_quadrant_value p O L) as K.
  pose proof (Z.mod_pos_bound (v p) (2^315) ltac:(lia)) as R.
  pose proof (Z.div_mod (v p) (2^315) ltac:(lia)) as Div.
  pose proof (trig_negative_value (trig_fraction p) Fo Fl ltac:(lia)) as Half.
  unfold trig_select,trig_nearest_integer; cbv zeta.
  destruct (trig_negative (trig_fraction p)) eqn:N; cbn [fst snd].
  - assert (High : 2^314<=v (trig_fraction p)) by (apply Half; reflexivity).
    destruct (trig_complement_value (trig_fraction p) Fo Fl ltac:(lia)) as [Co [Cl Cv]].
    split.
    + change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4.
      rewrite K. rewrite (Z.add_mod (v p/2^315) 1 4) by lia.
      reflexivity.
    + split; [exact Co|]. split; [exact Cl|]. rewrite Cv. split; lia.
  - assert (Low : v (trig_fraction p)<2^314).
    { destruct (Z_le_gt_dec (2^314) (v (trig_fraction p))); [|lia].
      assert (false=true) by (apply Half; assumption). discriminate. }
    split; [rewrite K; f_equal; lia|].
    split; [exact Fo|]. split; [exact Fl|]. split; lia.
Qed.

(** Composition from the actual signed Q256 remainder to the table index
    and normalized scalar residual consumed by the polynomial proofs. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid.
Require Import TrigQSplit TrigInput.
Open Scope R_scope.

Definition trig_negative h :=
  match Bcompare 53 1024 h (b64_of_bits 0) with Some Lt=>true | _=>false end.
Definition trig_flip (n:bool) h := if n then fneg h else h.
Definition trig_sign (n:bool) (x:R) := if n then -x else x.

Lemma trig_negative_correct h : finite h ->
  (trig_negative h=true <-> B h<0) /\ (trig_negative h=false <-> 0<=B h).
Proof.
  intros F. assert (Zero:finite(b64_of_bits 0)) by reflexivity.
  unfold trig_negative. rewrite (Bcompare_correct 53 1024 h _ F Zero).
  change (B(b64_of_bits 0)) with 0.
  destruct (Rcompare_spec (B h) 0);split;split;intros;try reflexivity;try discriminate;lra.
Qed.

Lemma trig_flip_correct n h : finite h -> finite(trig_flip n h) /\
  B(trig_flip n h)=trig_sign n (B h) /\ Rabs(B(trig_flip n h))=Rabs(B h).
Proof.
  intros F;destruct n;unfold trig_flip,trig_sign.
  - assert (Value:B(fneg h) = -B h) by apply B2R_Bopp.
    split;[unfold fneg,b64_opp;rewrite is_finite_Bopp;exact F|].
    split;[exact Value|rewrite Value,Rabs_Ropp;reflexivity].
  - repeat split;assumption.
Qed.

Definition trig_input r :=
  let '(h,l):=trig_q_split r in
  let n:=trig_negative h in
  let '(i,(th,tl)):=trig_table_residual (trig_flip n h) (trig_flip n l) in
  (n,(i,(th,tl))).

Theorem trig_input_correct r : valid r ->
  bpow radix2 (-64)<=Rabs(qval r)<=0.785399 ->
  let '(n,(i,(th,tl))):=trig_input r in
  finite i /\ (exists k:Z, (0<=k<=50)%Z /\ B i=IZR k) /\
  finite th /\ finite tl /\ B th=rndF(B th+B tl) /\
  Rabs(B th)<=0.0078126 /\ Rabs(B th+B tl)<=0.0078126 /\
  (B th=0 \/ bpow radix2 (-320)<=Rabs(B th)) /\
  Rabs(B tl)<=bpow radix2 (-53)*Rabs(B th) /\ on_grid (-320) (B tl) /\
  Rabs(B i/64+(B th+B tl)-trig_sign n (qval r))<=bpow radix2 (-105)*Rabs(qval r).
Proof.
  intros V Range. pose proof (trig_q_split_correct r V Range) as Split.
  unfold trig_input. destruct (trig_q_split r) as [h l] eqn:SplitWords.
  cbn zeta iota in Split |- *.
  destruct Split as [Fh [Fl [[Lower Upper] [Low [Gh [Gl Error]]]]]].
  set (n:=trig_negative h).
  destruct (trig_flip_correct n h Fh) as [Fah [Ah AbsH]].
  destruct (trig_flip_correct n l Fl) as [Fal [Al AbsL]].
  assert (Positive:0<=B(trig_flip n h)<=0.7854).
  { rewrite Ah. destruct (trig_negative_correct h Fh) as [Neg Pos].
    unfold n,trig_sign. destruct (trig_negative h) eqn:N.
    - pose proof (proj1 Neg eq_refl) as Negative. rewrite Rabs_left in Upper by lra;lra.
    - pose proof (proj1 Pos eq_refl) as Nonnegative. rewrite Rabs_pos_eq in Upper by lra;lra. }
  assert (Ga:on_grid (-320) (B(trig_flip n h))).
  { rewrite Ah;unfold trig_sign;destruct n;[apply grid_opp|];exact Gh. }
  assert (Gb:on_grid (-320) (B(trig_flip n l))).
  { rewrite Al;unfold trig_sign;destruct n;[apply grid_opp|];exact Gl. }
  pose proof (trig_table_residual_correct _ _ Fah Fal Positive ltac:(rewrite AbsL;exact Low) Ga Gb) as Table.
  destruct (trig_table_residual (trig_flip n h) (trig_flip n l)) as [i [th tl]] eqn:Words.
  cbn zeta iota in Table |- *.
  destruct Table as [Fi [K [Index [Fth [Ftl [Sum [Normal [Head [Full [LowerT [LowT GridT]]]]]]]]]]].
  split;[exact Fi|]. split;[eexists;split;[exact K|exact Index]|].
  split;[exact Fth|]. split;[exact Ftl|]. split;[exact Normal|].
  split;[exact Head|]. split;[exact Full|]. split;[exact LowerT|].
  split;[exact LowT|]. split;[exact GridT|].
  rewrite Sum,Ah,Al.
  unfold trig_sign;destruct n.
  - replace (B i/64+(-B h+-B l-B i/64)- -qval r) with (-(B h+B l-qval r)) by ring.
    rewrite Rabs_Ropp;exact Error.
  - replace (B i/64+(B h+B l-B i/64)-qval r) with (B h+B l-qval r) by ring;exact Error.
Qed.

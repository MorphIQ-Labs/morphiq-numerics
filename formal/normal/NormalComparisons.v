(** IEEE comparisons used by the scalar normal-family dispatch. *)
From Coq Require Import Reals ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
Open Scope R_scope.
Definition normal_zero : f64 := b64_of_bits 0.
Definition normal_lt x y := match Bcompare 53 1024 x y with Some Lt=>true | _=>false end.
Definition normal_le x y := match Bcompare 53 1024 x y with Some Lt|Some Eq=>true | _=>false end.
Definition normal_eq x y := match Bcompare 53 1024 x y with Some Eq=>true | _=>false end.
Lemma normal_lt_true x y : finite x -> finite y -> (normal_lt x y=true <-> B x<B y).
Proof.
  intros Fx Fy;unfold normal_lt;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec(B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.
Lemma normal_lt_false x y : finite x -> finite y -> (normal_lt x y=false <-> B y<=B x).
Proof.
  intros Fx Fy;unfold normal_lt;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec(B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.
Lemma normal_le_true x y : finite x -> finite y -> (normal_le x y=true <-> B x<=B y).
Proof.
  intros Fx Fy;unfold normal_le;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec(B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.
Lemma normal_le_false x y : finite x -> finite y -> (normal_le x y=false <-> B y<B x).
Proof.
  intros Fx Fy;unfold normal_le;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec(B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.

Lemma normal_eq_true x y : finite x -> finite y -> (normal_eq x y=true <-> B x=B y).
Proof.
  intros Fx Fy;unfold normal_eq;rewrite Bcompare_correct by assumption.
  destruct(Rcompare_spec(B x)(B y));split;intros;try discriminate;try reflexivity;lra.
Qed.

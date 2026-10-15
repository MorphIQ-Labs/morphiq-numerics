(** The last erfcx table binade has quarter-unit cells. A rounded lookup
    can leave its true argument outside a cell only at the lower endpoint. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Encodings.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ExpReduction ErfcxTableReduction NormalTableLookup
  NormalResidualGrid ErfcxAccurateInputs NormalErfcxTaylor.
Open Scope R_scope.

Lemma normal_last_binade_bits h : finite h -> 8<=B h<16 ->
  exists m,(2^52<=m<2^53)%Z /\ B h=IZR m*bpow radix2 (-49) /\
  bits_of_b64 h=(1026*2^52+(m-2^52))%Z.
Proof.
  intros F H.
  assert (Normal : bpow radix2 (-1022)<=B h).
  { eapply Rle_trans;[|exact(proj1 H)]. change 8 with(bpow radix2 3);apply bpow_le;lia. }
  destruct(pos_normal h F Normal)as[m [e [Hm [_ [M [E [Value [Mag [_ Bits]]]]]]]]].
  assert (Magnitude : (Raux.mag radix2(B h):Z)=4%Z).
  { assert (Lower : (4<=Raux.mag radix2(B h))%Z).
    { apply mag_ge_bpow;change(bpow radix2(4-1))with 8;rewrite Rabs_pos_eq;lra. }
    assert (Upper : (Raux.mag radix2(B h)<=4)%Z).
    { apply mag_le_bpow;[lra|change(bpow radix2 4)with 16;rewrite Rabs_pos_eq;lra]. } lia. }
  assert(e= -49)%Z by lia;subst e.
  exists(Zpos m);split;[exact M|]. split;[exact Value|].
  rewrite Bits,join_eq;reflexivity.
Qed.

Theorem normal_last_cell h : finite h -> 8<=B h<16 ->
  let '(i,c,r,e):=table_binade64 h in
  exists j,(0<=j<32)%Z /\ i=(145+j)%Z /\ e=3%Z /\
  finite c /\ B c=(65+2*IZR j)/8 /\
  8+IZR j/4<=B h<8+(IZR j+1)/4.
Proof.
  intros F H. destruct(normal_last_binade_bits h F H)as[m [M [Value Bits]]].
  set(f:=(m-2^52)%Z);set(j:=(f/2^47)%Z).
  assert (Fbits : (0<=f<2^52)%Z)by(unfold f;lia).
  assert (J : (0<=j<32)%Z).
  { unfold j;split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia. }
  assert (Cell : (j*2^47<=f<(j+1)*2^47)%Z).
  { unfold j;pose proof(Z.mul_div_le f (2^47) ltac:(lia));
    pose proof(Z.mul_succ_div_gt f (2^47) ltac:(lia));lia. }
  assert (Sh : Z.shiftr(bits_of_b64 h)52=1026%Z).
  { rewrite Bits,Z.shiftr_div_pow2 by lia;fold f.
    rewrite Z.div_add_l,Z.div_small by lia;reflexivity. }
  assert (Div : (bits_of_b64 h/2^47=1026*32+j)%Z).
  { rewrite Bits;fold f.
    replace(1026*2^52+f)%Z with((1026*32)*2^47+f)%Z by ring.
    rewrite Z.div_add_l by lia;reflexivity. }
  assert (Ix : Z.land(Z.shiftr(bits_of_b64 h)47)31=j).
  { change 31%Z with(Z.ones 5);rewrite Z.land_ones,Z.shiftr_div_pow2 by lia.
    rewrite Div;change(2^5)%Z with 32%Z;rewrite Z.add_comm,Z.mod_add by lia.
    apply Z.mod_small;exact J. }
  assert (Fields : let '(i,c,r,e):=table_binade64 h in i=(145+j)%Z /\ e=3%Z).
  { unfold table_binade64;rewrite Sh,Ix;split;reflexivity. }
  pose proof(table_binade_ieee h F ltac:(split;lra))as Reduction.
  destruct(table_binade64 h)as[[[i c]r]e];cbv zeta in Fields,Reduction.
  destruct Fields as[Idx Exponent];subst i e.
  destruct Reduction as[_ [_ [Fc [_ [_ [Center _]]]]]].
  exists j;split;[exact J|]. split;[reflexivity|]. split;[reflexivity|]. split;[exact Fc|]. split.
  - rewrite Center;replace(145+j-49-32*3)%Z with j by ring.
    change(bpow radix2 3)with 8;field.
  - assert (Lower : IZR(j*2^47)<=IZR f)by(apply IZR_le;lia).
    assert (Upper : IZR f<IZR((j+1)*2^47))by(apply IZR_lt;lia).
    rewrite !mult_IZR in Lower,Upper;rewrite plus_IZR in Upper.
    unfold f in Lower,Upper;rewrite minus_IZR in Lower,Upper.
    rewrite Value;bpow_num_all;split;lra.
Qed.

Lemma normal_rounded_cell z h lower upper : h=rndF z -> fmtF lower -> fmtF upper ->
  lower<=h<upper -> z<upper /\ (z<lower -> h=lower).
Proof.
  intros Rounded Lower Upper Cell. split.
  - destruct(Rlt_dec z upper);[assumption|].
    assert (upper<=rndF z)by(apply round_ge_generic;[exact _|exact _|exact Upper|lra]).
    rewrite <-Rounded in H;lra.
  - intros Below.
    assert (rndF z<=lower)by(apply round_le_generic;[exact _|exact _|exact Lower|lra]).
    rewrite <-Rounded in H;lra.
Qed.

Theorem normal_extended_last_cell_miss x : valid x -> /4<=qval x<16 ->
  8<=B(Q256.to_f64 x)<16 ->
  let '(i,c,r,e):=table_binade64(Q256.to_f64 x) in
  /8<Rabs(qval(normal_q_erfcx_residual x c)) ->
  B(Q256.to_f64 x)=B c-/8 /\ qval x<B(Q256.to_f64 x).
Proof.
  intros X Range High.
  destruct(normal_table_input_round x X ltac:(split;lra))as[Fh [_ [Rounded _]]].
  pose proof(normal_last_cell _ Fh High)as Cell.
  destruct(table_binade64(Q256.to_f64 x))as[[[i c]r]e];cbv zeta in Cell.
  destruct Cell as[j [J [_ [_ [Fc [Center Lookup]]]]]]. intros Miss.
  assert (LowerFormat : fmtF(8+IZR j/4)).
  { replace(8+IZR j/4)with(IZR(32+j)*bpow radix2 (-2))by(rewrite plus_IZR;change(bpow radix2 (-2))with(/4);field).
    apply fmt_int;lia. }
  assert (UpperFormat : fmtF(8+(IZR j+1)/4)).
  { replace(8+(IZR j+1)/4)with(IZR(33+j)*bpow radix2 (-2))by(rewrite plus_IZR;change(bpow radix2 (-2))with(/4);field).
    apply fmt_int;lia. }
  destruct(normal_rounded_cell _ _ _ _ Rounded LowerFormat UpperFormat Lookup)as[Upper AtLower].
  assert (CenterRange : 0<B c<=16).
  { assert (Index : 0<=IZR j<=31)by(split;[apply IZR_le;lia|change 31 with(IZR 31);apply IZR_le;lia]).
    rewrite Center;split;lra. }
  assert (Below : qval x<8+IZR j/4).
  { destruct(Rlt_dec(qval x)(8+IZR j/4));[assumption|exfalso].
    assert (Radius : Rabs(qval x-B c)<=/8).
    { rewrite Center;apply Rabs_le;split;lra. }
    pose proof(normal_extended_residual_radius x c X ltac:(split;lra) Fc CenterRange Radius)as Inside.
    unfold normal_q_erfcx_residual in Miss;lra. }
  specialize(AtLower Below);split;[rewrite AtLower,Center;field|rewrite AtLower;exact Below].
Qed.


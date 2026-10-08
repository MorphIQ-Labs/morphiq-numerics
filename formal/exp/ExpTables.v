(** Constants of [exp]'s fast path, written by generators/exp_constants.py;
    do not edit. Each is given by its binary64 encoding, as in
    crates/morphiq-numerics/src/exp/tables.rs, with its value. Each bound the
    certificates take about them is proved here by CoqInterval, from the
    definitions of [ln] and [exp]. *)

From Coq Require Import Reals ZArith List Lia.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Grid Encodings.
From Interval Require Import Tactic.
Import ListNotations.

Open Scope R_scope.

(** [L = ln 2 / 128 = L1 + L2 + L3 + L4 + dL] with [|dL| <= 2^-206]
    (docs/exp.md, section 3; [dL] in formal/exp/reduction.g). *)
Definition exp_l1 : f64 := b64_of_bits 4572893336921964544.
Lemma exp_l1_val : B exp_l1 = 6243314768281600 / 2 ^ 60.
Proof. exact (bits_val 4572893336921964544 false 6243314768281600 60 eq_refl). Qed.
Lemma exp_l1_finite : finite exp_l1.
Proof. exact (bits_finite 4572893336921964544 _ _ _ eq_refl). Qed.
Definition exp_l2 : f64 := b64_of_bits 13635880478764185753.
Lemma exp_l2_val : B exp_l2 = (- 7988006341064857) / 2 ^ 96.
Proof. exact (bits_val 13635880478764185753 true 7988006341064857 96 eq_refl). Qed.
Lemma exp_l2_finite : finite exp_l2.
Proof. exact (bits_finite 13635880478764185753 _ _ _ eq_refl). Qed.
Definition exp_l3 : f64 := b64_of_bits 4163582197559673075.
Lemma exp_l3_val : B exp_l3 = 6759741496705267 / 2 ^ 151.
Proof. exact (bits_val 4163582197559673075 false 6759741496705267 151 eq_refl). Qed.
Lemma exp_l3_finite : finite exp_l3.
Proof. exact (bits_finite 4163582197559673075 _ _ _ eq_refl). Qed.
Definition exp_l4 : f64 := b64_of_bits 3918353350452415331.
Lemma exp_l4_val : B exp_l4 = 4725274267454307 / 2 ^ 205.
Proof. exact (bits_val 3918353350452415331 false 4725274267454307 205 eq_refl). Qed.
Lemma exp_l4_finite : finite exp_l4.
Proof. exact (bits_finite 3918353350452415331 _ _ _ eq_refl). Qed.
Theorem exp_l_split : Rabs (B exp_l1 + B exp_l2 + B exp_l3 + B exp_l4 - ln 2 / 128) <= / 2 ^ 206.
Proof.
  rewrite exp_l1_val, exp_l2_val, exp_l3_val, exp_l4_val.
  interval with (i_prec 260).
Qed.

(** The polynomial's coefficients, and its approximation error on
    [|r| <= 0.0027077] (generators/exp_poly.sollya's supnorm bound; [a] in
    formal/exp/fast.g). *)
Definition exp_c3 : f64 := b64_of_bits 4595172819793695888.
Lemma exp_c3_val : B exp_c3 = 6004799503160464 / 2 ^ 55.
Proof. exact (bits_val 4595172819793695888 false 6004799503160464 55 eq_refl). Qed.
Lemma exp_c3_finite : finite exp_c3.
Proof. exact (bits_finite 4595172819793695888 _ _ _ eq_refl). Qed.
Definition exp_c4 : f64 := b64_of_bits 4586165620538954943.
Lemma exp_c4_val : B exp_c4 = 6004799503160511 / 2 ^ 57.
Proof. exact (bits_val 4586165620538954943 false 6004799503160511 57 eq_refl). Qed.
Lemma exp_c4_finite : finite exp_c4.
Proof. exact (bits_finite 4586165620538954943 _ _ _ eq_refl). Qed.
Definition exp_c5 : f64 := b64_of_bits 4575957462630761033.
Lemma exp_c5_val : B exp_c5 = 4803840849707593 / 2 ^ 59.
Proof. exact (bits_val 4575957462630761033 false 4803840849707593 59 eq_refl). Qed.
Lemma exp_c5_finite : finite exp_c5.
Proof. exact (bits_finite 4575957462630761033 _ _ _ eq_refl). Qed.
Definition exp_c6 : f64 := b64_of_bits 4564047943863703478.
Lemma exp_c6_val : B exp_c6 = 6405120964761526 / 2 ^ 62.
Proof. exact (bits_val 4564047943863703478 false 6405120964761526 62 eq_refl). Qed.
Lemma exp_c6_finite : finite exp_c6.
Proof. exact (bits_finite 4564047943863703478 _ _ _ eq_refl). Qed.
Definition exp_poly_bound : R := 16264149585115708508880501 / 2 ^ 161.
Theorem exp_poly_approx r : Rabs r <= 0.0027077 ->
  Rabs (exp r - 1 - r - r * r * (1 / 2 + r * (B exp_c3 + r * (B exp_c4 + r * (B exp_c5 + r * B exp_c6)))))
  <= exp_poly_bound.
Proof.
  intros H. rewrite exp_c3_val, exp_c4_val, exp_c5_val, exp_c6_val. unfold exp_poly_bound.
  interval with (i_taylor r, i_degree 12, i_bisect r, i_prec 120, i_depth 12).
Qed.

(** [T_j = 2^(j/128)] as a double-word [(hi, lo)], within [2^-107]
    relatively ([d4] in formal/exp/fast.g); both words are multiples of
    [2^-120], so a nonzero one is at least that in magnitude. *)
Definition exp_t_bits : list (Z * Z) := [
  (4607182418800017408%Z, 0%Z);
  (4607206872900645685%Z, 4367191094983183799%Z);
  (4607231459784622177%Z, 13578793245212346461%Z);
  (4607256180172947333%Z, 13587539416858478958%Z);
  (4607281034790536564%Z, 4363271031250859109%Z);
  (4607306024366241502%Z, 13586394566636944423%Z);
  (4607331149632871368%Z, 4350906866888508671%Z);
  (4607356411327214467%Z, 4364349194537886006%Z);
  (4607381810190059791%Z, 4366422556490359051%Z);
  (4607407346966218743%Z, 4364021969547579249%Z);
  (4607433022404546978%Z, 4341533911911070547%Z);
  (4607458837257966363%Z, 13577116947141541243%Z);
  (4607484792283487057%Z, 13589265599107996474%Z);
  (4607510888242229708%Z, 13569826252758230471%Z);
  (4607537125899447776%Z, 13588257000691676830%Z);
  (4607563506024549969%Z, 4360118216378198794%Z);
  (4607590029391122811%Z, 13583296563091311222%Z);
  (4607616696776953322%Z, 13587659296779734892%Z);
  (4607643508964051829%Z, 4363525473012639972%Z);
  (4607670466738674900%Z, 13589985186450175495%Z);
  (4607697570891348394%Z, 4367930260564632636%Z);
  (4607724822216890653%Z, 13587887394723182476%Z);
  (4607752221514435798%Z, 4363362921486124181%Z);
  (4607779769587457174%Z, 4360233750371804654%Z);
  (4607807467243790904%Z, 4366715371991270771%Z);
  (4607835315295659583%Z, 4362511763081852068%Z);
  (4607863314559696093%Z, 4360255418560211417%Z);
  (4607891465856967553%Z, 13590258639888649598%Z);
  (4607919770012999393%Z, 4361194079743971925%Z);
  (4607948227857799568%Z, 13565135496219728548%Z);
  (4607976840225882891%Z, 4363990544311599573%Z);
  (4608005607956295510%Z, 4355484481588896643%Z);
  (4608034531892639509%Z, 4361442028785074916%Z);
  (4608063612883097649%Z, 4362471707397063804%Z);
  (4608092851780458239%Z, 4364875488757701030%Z);
  (4608122249442140145%Z, 13586054879713838632%Z);
  (4608151806730217931%Z, 13589113705542642402%Z);
  (4608181524511447142%Z, 13591465159290324157%Z);
  (4608211403657289719%Z, 13580011175581709795%Z);
  (4608241445043939557%Z, 13591582166996560323%Z);
  (4608271649552348194%Z, 4362538921552289468%Z);
  (4608302018068250652%Z, 13589559253539420659%Z);
  (4608332551482191402%Z, 13573553959711314552%Z);
  (4608363250689550487%Z, 13583357706942511513%Z);
  (4608394116590569773%Z, 4343892788969963728%Z);
  (4608425150090379351%Z, 4367528791999023734%Z);
  (4608456352099024080%Z, 4356038173484147440%Z);
  (4608487723531490270%Z, 4366744939570249302%Z);
  (4608519265307732519%Z, 4358714333135127266%Z);
  (4608550978352700685%Z, 4366500267238783027%Z);
  (4608582863596367015%Z, 13588682830448777187%Z);
  (4608614921973753410%Z, 13587208916176835567%Z);
  (4608647154424958850%Z, 13582991433109945517%Z);
  (4608679561895186959%Z, 13586630674096186779%Z);
  (4608712145334773722%Z, 4366727111384077229%Z);
  (4608744905699215357%Z, 4360212184385068520%Z);
  (4608777843949196329%Z, 4365732190869669805%Z);
  (4608810961050617527%Z, 4340426722385692322%Z);
  (4608844257974624584%Z, 4367267852856649310%Z);
  (4608877735697636361%Z, 13588453276408798791%Z);
  (4608911395201373573%Z, 13588349367777014935%Z);
  (4608945237472887584%Z, 13586313600378439987%Z);
  (4608979263504589349%Z, 13590656452562328628%Z);
  (4609013474294278515%Z, 4350539561172418149%Z);
  (4609047870845172685%Z, 13590699516259099734%Z);
  (4609082454165936831%Z, 13579066830680427277%Z);
  (4609117225270712879%Z, 13577154659704670379%Z);
  (4609152185179149444%Z, 13585174311714819830%Z);
  (4609187334916431732%Z, 13583259204604951193%Z);
  (4609222675513311604%Z, 13587545727556769084%Z);
  (4609258208006137801%Z, 13587400041910332883%Z);
  (4609293933436886335%Z, 4366352779363620397%Z);
  (4609329852853191047%Z, 13584005980894828847%Z);
  (4609365967308374322%Z, 4368230284707384790%Z);
  (4609402277861477986%Z, 4355083105960556926%Z);
  (4609438785577294354%Z, 13588059942349018923%Z);
  (4609475491526397459%Z, 13591102941469946584%Z);
  (4609512396785174445%Z, 13585344141126127099%Z);
  (4609549502435857133%Z, 13591800971496060602%Z);
  (4609586809566553753%Z, 4366684878742009146%Z);
  (4609624319271280859%Z, 4365934111530306343%Z);
  (4609662032649995404%Z, 13578587477079876522%Z);
  (4609699950808626998%Z, 4361116198887462764%Z);
  (4609738074859110342%Z, 13591255066430940452%Z);
  (4609776405919417829%Z, 13575924912210935484%Z);
  (4609814945113592335%Z, 13580124724857794617%Z);
  (4609853693571780176%Z, 13591046031677294033%Z);
  (4609892652430264250%Z, 13587768808785765938%Z);
  (4609931822831497360%Z, 4358495182437610174%Z);
  (4609971205924135715%Z, 4357273091511307374%Z);
  (4610010802863072613%Z, 13588302672336573747%Z);
  (4610050614809472307%Z, 4365730062588982955%Z);
  (4610090642930804061%Z, 13591071403650400737%Z);
  (4610130888400876376%Z, 4367308009094079431%Z);
  (4610171352399871423%Z, 4364263780368514353%Z);
  (4610212036114379642%Z, 13587239356240194768%Z);
  (4610252940737434541%Z, 4366136266477915265%Z);
  (4610294067468547686%Z, 13590701445652472869%Z);
  (4610335417513743867%Z, 13574553368877389576%Z);
  (4610376992085596474%Z, 13590862981238517219%Z);
  (4610418792403263047%Z, 13579857349850737723%Z);
  (4610460819692521034%Z, 13591578708859431214%Z);
  (4610503075185803730%Z, 4360115354860363396%Z);
  (4610545560122236425%Z, 13591579770539973747%Z);
  (4610588275747672732%Z, 4359783942552832221%Z);
  (4610631223314731130%Z, 4367160369958077962%Z);
  (4610674404082831691%Z, 4364700857452215469%Z);
  (4610717819318233013%Z, 4355452239314181188%Z);
  (4610761470294069353%Z, 4356392388485794267%Z);
  (4610805358290387962%Z, 13586753400162393458%Z);
  (4610849484594186620%Z, 13590944721038572188%Z);
  (4610893850499451378%Z, 13591098945498350968%Z);
  (4610938457307194503%Z, 4360307985706858247%Z);
  (4610983306325492632%Z, 13587675367378640872%Z);
  (4611028398869525125%Z, 4367404223318308146%Z);
  (4611073736261612640%Z, 4364791058101442755%Z);
  (4611119319831255903%Z, 13587823851967368028%Z);
  (4611165150915174697%Z, 13589530681406002326%Z);
  (4611211230857347062%Z, 4360503177631091855%Z);
  (4611257561009048707%Z, 4364785334270856674%Z);
  (4611304142728892634%Z, 13591472399984634003%Z);
  (4611350977382868977%Z, 13590900450404707724%Z);
  (4611398066344385063%Z, 4367867066664138416%Z);
  (4611445410994305687%Z, 4365010197099155011%Z);
  (4611493012720993600%Z, 4366754277802680715%Z);
  (4611540872920350228%Z, 13591224939947898122%Z);
  (4611588992995856600%Z, 4361534289538814750%Z);
  (4611637374358614513%Z, 4351299075965286887%Z)
].
Definition exp_t_hi (j : nat) : f64 := b64_of_bits (fst (nth j exp_t_bits (0%Z, 0%Z))).
Definition exp_t_lo (j : nat) : f64 := b64_of_bits (snd (nth j exp_t_bits (0%Z, 0%Z))).

Definition exp_t_ok (j : nat) : Prop :=
  finite (exp_t_hi j) /\ finite (exp_t_lo j) /\
  on_grid (-120) (B (exp_t_hi j)) /\ on_grid (-120) (B (exp_t_lo j)) /\
  Rabs (B (exp_t_hi j)) <= 2 /\ Rabs (B (exp_t_lo j)) <= 1 /\
  Rabs ((B (exp_t_hi j) + B (exp_t_lo j) - exp (INR j * ln 2 / 128)) / exp (INR j * ln 2 / 128))
    <= / 2 ^ 107.

Lemma exp_t_ok_0 : exp_t_ok 0.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607182418800017408 _ _ _ eq_refl) | split; [exact (bits_finite_zero 0 false eq_refl) | ]].
  rewrite (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl), (bits_zero 0 false eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply grid_0 | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 0) with 0%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_1 : exp_t_ok 1.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607206872900645685 _ _ _ eq_refl) | split; [exact (bits_finite 4367191094983183799 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607206872900645685 false 4528053727998773 52 eq_refl), (bits_val 4367191094983183799 false 7706655688543671 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 1) with 1%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_2 : exp_t_ok 2.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607231459784622177 _ _ _ eq_refl) | split; [exact (bits_finite 13578793245212346461 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607231459784622177 false 4552640611975265 52 eq_refl), (bits_val 13578793245212346461 true 4943968317671517 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 2) with 2%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_3 : exp_t_ok 3.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607256180172947333 _ _ _ eq_refl) | split; [exact (bits_finite 13587539416858478958 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607256180172947333 false 4577361000300421 52 eq_refl), (bits_val 13587539416858478958 true 4682940709063022 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 3) with 3%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_4 : exp_t_ok 4.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607281034790536564 _ _ _ eq_refl) | split; [exact (bits_finite 4363271031250859109 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607281034790536564 false 4602215617889652 52 eq_refl), (bits_val 4363271031250859109 false 8290191583589477 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 4) with 4%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_5 : exp_t_ok 5.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607306024366241502 _ _ _ eq_refl) | split; [exact (bits_finite 13586394566636944423 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607306024366241502 false 4627205193594590 52 eq_refl), (bits_val 13586394566636944423 true 8041690114898983 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 5) with 5%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_6 : exp_t_ok 6.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607331149632871368 _ _ _ eq_refl) | split; [exact (bits_finite 4350906866888508671 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607331149632871368 false 4652330460224456 52 eq_refl), (bits_val 4350906866888508671 false 4933226475980031 109 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 6) with 6%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_7 : exp_t_ok 7.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607356411327214467 _ _ _ eq_refl) | split; [exact (bits_finite 4364349194537886006 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607356411327214467 false 4677592154567555 52 eq_refl), (bits_val 4364349194537886006 false 4864755243245878 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 7) with 7%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_8 : exp_t_ok 8.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607381810190059791 _ _ _ eq_refl) | split; [exact (bits_finite 4366422556490359051 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607381810190059791 false 4702991017412879 52 eq_refl), (bits_val 4366422556490359051 false 6938117195718923 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 8) with 8%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_9 : exp_t_ok 9.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607407346966218743 _ _ _ eq_refl) | split; [exact (bits_finite 4364021969547579249 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607407346966218743 false 4728527793571831 52 eq_refl), (bits_val 4364021969547579249 false 4537530252939121 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 9) with 9%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_10 : exp_t_ok 10.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607433022404546978 _ _ _ eq_refl) | split; [exact (bits_finite 4341533911911070547 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607433022404546978 false 4754203231900066 52 eq_refl), (bits_val 4341533911911070547 false 4567470753282899 111 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 10) with 10%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_11 : exp_t_ok 11.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607458837257966363 _ _ _ eq_refl) | split; [exact (bits_finite 13577116947141541243 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607458837257966363 false 4780018085319451 52 eq_refl), (bits_val 13577116947141541243 true 7771269874236795 109 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 11) with 11%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_12 : exp_t_ok 12.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607484792283487057 _ _ _ eq_refl) | split; [exact (bits_finite 13589265599107996474 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607484792283487057 false 4805973110840145 52 eq_refl), (bits_val 13589265599107996474 true 6409122958580538 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 12) with 12%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_13 : exp_t_ok 13.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607510888242229708 _ _ _ eq_refl) | split; [exact (bits_finite 13569826252758230471 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607510888242229708 false 4832069069582796 52 eq_refl), (bits_val 13569826252758230471 true 4984175118296519 110 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 13) with 13%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_14 : exp_t_ok 14.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607537125899447776 _ _ _ eq_refl) | split; [exact (bits_finite 13588257000691676830 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607537125899447776 false 4858306726800864 52 eq_refl), (bits_val 13588257000691676830 true 5400524542260894 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 14) with 14%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_15 : exp_t_ok 15.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607563506024549969 _ _ _ eq_refl) | split; [exact (bits_finite 4360118216378198794 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607563506024549969 false 4884686851903057 52 eq_refl), (bits_val 4360118216378198794 false 5137376710929162 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 15) with 15%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_16 : exp_t_ok 16.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607590029391122811 _ _ _ eq_refl) | split; [exact (bits_finite 13583296563091311222 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607590029391122811 false 4911210218475899 52 eq_refl), (bits_val 13583296563091311222 true 4943686569265782 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 16) with 16%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_17 : exp_t_ok 17.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607616696776953322 _ _ _ eq_refl) | split; [exact (bits_finite 13587659296779734892 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607616696776953322 false 4937877604306410 52 eq_refl), (bits_val 13587659296779734892 true 4802820630318956 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 17) with 17%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_18 : exp_t_ok 18.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607643508964051829 _ _ _ eq_refl) | split; [exact (bits_finite 4363525473012639972 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607643508964051829 false 4964689791404917 52 eq_refl), (bits_val 4363525473012639972 false 8544633345370340 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 18) with 18%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_19 : exp_t_ok 19.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607670466738674900 _ _ _ eq_refl) | split; [exact (bits_finite 13589985186450175495 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607670466738674900 false 4991647566027988 52 eq_refl), (bits_val 13589985186450175495 true 7128710300759559 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 19) with 19%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_20 : exp_t_ok 20.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607697570891348394 _ _ _ eq_refl) | split; [exact (bits_finite 4367930260564632636 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607697570891348394 false 5018751718701482 52 eq_refl), (bits_val 4367930260564632636 false 8445821269992508 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 20) with 20%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_21 : exp_t_ok 21.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607724822216890653 _ _ _ eq_refl) | split; [exact (bits_finite 13587887394723182476 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607724822216890653 false 5046003044243741 52 eq_refl), (bits_val 13587887394723182476 true 5030918573766540 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 21) with 21%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_22 : exp_t_ok 22.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607752221514435798 _ _ _ eq_refl) | split; [exact (bits_finite 4363362921486124181 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607752221514435798 false 5073402341788886 52 eq_refl), (bits_val 4363362921486124181 false 8382081818854549 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 22) with 22%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_23 : exp_t_ok 23.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607779769587457174 _ _ _ eq_refl) | split; [exact (bits_finite 4360233750371804654 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607779769587457174 false 5100950414810262 52 eq_refl), (bits_val 4360233750371804654 false 5252910704535022 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 23) with 23%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_24 : exp_t_ok 24.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607807467243790904 _ _ _ eq_refl) | split; [exact (bits_finite 4366715371991270771 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607807467243790904 false 5128648071143992 52 eq_refl), (bits_val 4366715371991270771 false 7230932696630643 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 24) with 24%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_25 : exp_t_ok 25.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607835315295659583 _ _ _ eq_refl) | split; [exact (bits_finite 4362511763081852068 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607835315295659583 false 5156496123012671 52 eq_refl), (bits_val 4362511763081852068 false 7530923414582436 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 25) with 25%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_26 : exp_t_ok 26.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607863314559696093 _ _ _ eq_refl) | split; [exact (bits_finite 4360255418560211417 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607863314559696093 false 5184495387049181 52 eq_refl), (bits_val 4360255418560211417 false 5274578892941785 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 26) with 26%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_27 : exp_t_ok 27.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607891465856967553 _ _ _ eq_refl) | split; [exact (bits_finite 13590258639888649598 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607891465856967553 false 5212646684320641 52 eq_refl), (bits_val 13590258639888649598 true 7402163739233662 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 27) with 27%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_28 : exp_t_ok 28.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607919770012999393 _ _ _ eq_refl) | split; [exact (bits_finite 4361194079743971925 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607919770012999393 false 5240950840352481 52 eq_refl), (bits_val 4361194079743971925 false 6213240076702293 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 28) with 28%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_29 : exp_t_ok 29.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607948227857799568 _ _ _ eq_refl) | split; [exact (bits_finite 13565135496219728548 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607948227857799568 false 5269408685152656 52 eq_refl), (bits_val 13565135496219728548 true 4797018207165092 111 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 29) with 29%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_30 : exp_t_ok 30.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4607976840225882891 _ _ _ eq_refl) | split; [exact (bits_finite 4363990544311599573 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4607976840225882891 false 5298021053235979 52 eq_refl), (bits_val 4363990544311599573 false 4506105016959445 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 30) with 30%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_31 : exp_t_ok 31.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608005607956295510 _ _ _ eq_refl) | split; [exact (bits_finite 4355484481588896643 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608005607956295510 false 5326788783648598 52 eq_refl), (bits_val 4355484481588896643 false 5007241548997507 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 31) with 31%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_32 : exp_t_ok 32.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608034531892639509 _ _ _ eq_refl) | split; [exact (bits_finite 4361442028785074916 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608034531892639509 false 5355712719992597 52 eq_refl), (bits_val 4361442028785074916 false 6461189117805284 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 32) with 32%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_33 : exp_t_ok 33.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608063612883097649 _ _ _ eq_refl) | split; [exact (bits_finite 4362471707397063804 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608063612883097649 false 5384793710450737 52 eq_refl), (bits_val 4362471707397063804 false 7490867729794172 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 33) with 33%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_34 : exp_t_ok 34.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608092851780458239 _ _ _ eq_refl) | split; [exact (bits_finite 4364875488757701030 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608092851780458239 false 5414032607811327 52 eq_refl), (bits_val 4364875488757701030 false 5391049463060902 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 34) with 34%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_35 : exp_t_ok 35.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608122249442140145 _ _ _ eq_refl) | split; [exact (bits_finite 13586054879713838632 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608122249442140145 false 5443430269493233 52 eq_refl), (bits_val 13586054879713838632 true 7702003191793192 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 35) with 35%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_36 : exp_t_ok 36.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608151806730217931 _ _ _ eq_refl) | split; [exact (bits_finite 13589113705542642402 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608151806730217931 false 5472987557571019 52 eq_refl), (bits_val 13589113705542642402 true 6257229393226466 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 36) with 36%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_37 : exp_t_ok 37.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608181524511447142 _ _ _ eq_refl) | split; [exact (bits_finite 13591465159290324157 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608181524511447142 false 5502705338800230 52 eq_refl), (bits_val 13591465159290324157 true 8608683140908221 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 37) with 37%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_38 : exp_t_ok 38.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608211403657289719 _ _ _ eq_refl) | split; [exact (bits_finite 13580011175581709795 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608211403657289719 false 5532584484642807 52 eq_refl), (bits_val 13580011175581709795 true 6161898687034851 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 38) with 38%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_39 : exp_t_ok 39.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608241445043939557 _ _ _ eq_refl) | split; [exact (bits_finite 13591582166996560323 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608241445043939557 false 5562625871292645 52 eq_refl), (bits_val 13591582166996560323 true 8725690847144387 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 39) with 39%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_40 : exp_t_ok 40.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608271649552348194 _ _ _ eq_refl) | split; [exact (bits_finite 4362538921552289468 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608271649552348194 false 5592830379701282 52 eq_refl), (bits_val 4362538921552289468 false 7558081885019836 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 40) with 40%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_41 : exp_t_ok 41.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608302018068250652 _ _ _ eq_refl) | split; [exact (bits_finite 13589559253539420659 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608302018068250652 false 5623198895603740 52 eq_refl), (bits_val 13589559253539420659 true 6702777390004723 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 41) with 41%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_42 : exp_t_ok 42.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608332551482191402 _ _ _ eq_refl) | split; [exact (bits_finite 13573553959711314552 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608332551482191402 false 5653732309544490 52 eq_refl), (bits_val 13573553959711314552 true 8711882071380600 110 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 42) with 42%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_43 : exp_t_ok 43.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608363250689550487 _ _ _ eq_refl) | split; [exact (bits_finite 13583357706942511513 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608363250689550487 false 5684431516903575 52 eq_refl), (bits_val 13583357706942511513 true 5004830420466073 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 43) with 43%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_44 : exp_t_ok 44.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608394116590569773 _ _ _ eq_refl) | split; [exact (bits_finite 4343892788969963728 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608394116590569773 false 5715297417922861 52 eq_refl), (bits_val 4343892788969963728 false 6926347812176080 111 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 44) with 44%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_45 : exp_t_ok 45.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608425150090379351 _ _ _ eq_refl) | split; [exact (bits_finite 4367528791999023734 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608425150090379351 false 5746330917732439 52 eq_refl), (bits_val 4367528791999023734 false 8044352704383606 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 45) with 45%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_46 : exp_t_ok 46.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608456352099024080 _ _ _ eq_refl) | split; [exact (bits_finite 4356038173484147440 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608456352099024080 false 5777532926377168 52 eq_refl), (bits_val 4356038173484147440 false 5560933444248304 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 46) with 46%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_47 : exp_t_ok 47.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608487723531490270 _ _ _ eq_refl) | split; [exact (bits_finite 4366744939570249302 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608487723531490270 false 5808904358843358 52 eq_refl), (bits_val 4366744939570249302 false 7260500275609174 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 47) with 47%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_48 : exp_t_ok 48.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608519265307732519 _ _ _ eq_refl) | split; [exact (bits_finite 4358714333135127266 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608519265307732519 false 5840446135085607 52 eq_refl), (bits_val 4358714333135127266 false 8237093095228130 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 48) with 48%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_49 : exp_t_ok 49.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608550978352700685 _ _ _ eq_refl) | split; [exact (bits_finite 4366500267238783027 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608550978352700685 false 5872159180053773 52 eq_refl), (bits_val 4366500267238783027 false 7015827944142899 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 49) with 49%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_50 : exp_t_ok 50.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608582863596367015 _ _ _ eq_refl) | split; [exact (bits_finite 13588682830448777187 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608582863596367015 false 5904044423720103 52 eq_refl), (bits_val 13588682830448777187 true 5826354299361251 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 50) with 50%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_51 : exp_t_ok 51.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608614921973753410 _ _ _ eq_refl) | split; [exact (bits_finite 13587208916176835567 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608614921973753410 false 5936102801106498 52 eq_refl), (bits_val 13587208916176835567 true 8856039654790127 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 51) with 51%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_52 : exp_t_ok 52.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608647154424958850 _ _ _ eq_refl) | split; [exact (bits_finite 13582991433109945517 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608647154424958850 false 5968335252311938 52 eq_refl), (bits_val 13582991433109945517 true 4638556587900077 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 52) with 52%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_53 : exp_t_ok 53.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608679561895186959 _ _ _ eq_refl) | split; [exact (bits_finite 13586630674096186779 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608679561895186959 false 6000742722540047 52 eq_refl), (bits_val 13586630674096186779 true 8277797574141339 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 53) with 53%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_54 : exp_t_ok 54.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608712145334773722 _ _ _ eq_refl) | split; [exact (bits_finite 4366727111384077229 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608712145334773722 false 6033326162126810 52 eq_refl), (bits_val 4366727111384077229 false 7242672089437101 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 54) with 54%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_55 : exp_t_ok 55.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608744905699215357 _ _ _ eq_refl) | split; [exact (bits_finite 4360212184385068520 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608744905699215357 false 6066086526568445 52 eq_refl), (bits_val 4360212184385068520 false 5231344717798888 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 55) with 55%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_56 : exp_t_ok 56.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608777843949196329 _ _ _ eq_refl) | split; [exact (bits_finite 4365732190869669805 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608777843949196329 false 6099024776549417 52 eq_refl), (bits_val 4365732190869669805 false 6247751575029677 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 56) with 56%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_57 : exp_t_ok 57.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608810961050617527 _ _ _ eq_refl) | split; [exact (bits_finite 4340426722385692322 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608810961050617527 false 6132141877970615 52 eq_refl), (bits_val 4340426722385692322 false 7963880855275170 112 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 57) with 57%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_58 : exp_t_ok 58.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608844257974624584 _ _ _ eq_refl) | split; [exact (bits_finite 4367267852856649310 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608844257974624584 false 6165438801977672 52 eq_refl), (bits_val 4367267852856649310 false 7783413562009182 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 58) with 58%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_59 : exp_t_ok 59.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608877735697636361 _ _ _ eq_refl) | split; [exact (bits_finite 13588453276408798791 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608877735697636361 false 6198916524989449 52 eq_refl), (bits_val 13588453276408798791 true 5596800259382855 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 59) with 59%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_60 : exp_t_ok 60.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608911395201373573 _ _ _ eq_refl) | split; [exact (bits_finite 13588349367777014935 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608911395201373573 false 6232576028726661 52 eq_refl), (bits_val 13588349367777014935 true 5492891627598999 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 60) with 60%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_61 : exp_t_ok 61.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608945237472887584 _ _ _ eq_refl) | split; [exact (bits_finite 13586313600378439987 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608945237472887584 false 6266418300240672 52 eq_refl), (bits_val 13586313600378439987 true 7960723856394547 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 61) with 61%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_62 : exp_t_ok 62.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4608979263504589349 _ _ _ eq_refl) | split; [exact (bits_finite 13590656452562328628 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4608979263504589349 false 6300444331942437 52 eq_refl), (bits_val 13590656452562328628 true 7799976412912692 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 62) with 62%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_63 : exp_t_ok 63.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609013474294278515 _ _ _ eq_refl) | split; [exact (bits_finite 4350539561172418149 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609013474294278515 false 6334655121631603 52 eq_refl), (bits_val 4350539561172418149 false 4565920759889509 109 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 63) with 63%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_64 : exp_t_ok 64.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609047870845172685 _ _ _ eq_refl) | split; [exact (bits_finite 13590699516259099734 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609047870845172685 false 6369051672525773 52 eq_refl), (bits_val 13590699516259099734 true 7843040109683798 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 64) with 64%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_65 : exp_t_ok 65.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609082454165936831 _ _ _ eq_refl) | split; [exact (bits_finite 13579066830680427277 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609082454165936831 false 6403634993289919 52 eq_refl), (bits_val 13579066830680427277 true 5217553785752333 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 65) with 65%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_66 : exp_t_ok 66.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609117225270712879 _ _ _ eq_refl) | split; [exact (bits_finite 13577154659704670379 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609117225270712879 false 6438406098065967 52 eq_refl), (bits_val 13577154659704670379 true 7808982437365931 109 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 66) with 66%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_67 : exp_t_ok 67.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609152185179149444 _ _ _ eq_refl) | split; [exact (bits_finite 13585174311714819830 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609152185179149444 false 6473366006502532 52 eq_refl), (bits_val 13585174311714819830 true 6821435192774390 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 67) with 67%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_68 : exp_t_ok 68.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609187334916431732 _ _ _ eq_refl) | split; [exact (bits_finite 13583259204604951193 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609187334916431732 false 6508515743784820 52 eq_refl), (bits_val 13583259204604951193 true 4906328082905753 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 68) with 68%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_69 : exp_t_ok 69.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609222675513311604 _ _ _ eq_refl) | split; [exact (bits_finite 13587545727556769084 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609222675513311604 false 6543856340664692 52 eq_refl), (bits_val 13587545727556769084 true 4689251407353148 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 69) with 69%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_70 : exp_t_ok 70.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609258208006137801 _ _ _ eq_refl) | split; [exact (bits_finite 13587400041910332883 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609258208006137801 false 6579388833490889 52 eq_refl), (bits_val 13587400041910332883 true 4543565760916947 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 70) with 70%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_71 : exp_t_ok 71.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609293933436886335 _ _ _ eq_refl) | split; [exact (bits_finite 4366352779363620397 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609293933436886335 false 6615114264239423 52 eq_refl), (bits_val 4366352779363620397 false 6868340068980269 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 71) with 71%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_72 : exp_t_ok 72.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609329852853191047 _ _ _ eq_refl) | split; [exact (bits_finite 13584005980894828847 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609329852853191047 false 6651033680544135 52 eq_refl), (bits_val 13584005980894828847 true 5653104372783407 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 72) with 72%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_73 : exp_t_ok 73.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609365967308374322 _ _ _ eq_refl) | split; [exact (bits_finite 4368230284707384790 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609365967308374322 false 6687148135727410 52 eq_refl), (bits_val 4368230284707384790 false 8745845412744662 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 73) with 73%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_74 : exp_t_ok 74.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609402277861477986 _ _ _ eq_refl) | split; [exact (bits_finite 4355083105960556926 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609402277861477986 false 6723458688831074 52 eq_refl), (bits_val 4355083105960556926 false 4605865920657790 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 74) with 74%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_75 : exp_t_ok 75.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609438785577294354 _ _ _ eq_refl) | split; [exact (bits_finite 13588059942349018923 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609438785577294354 false 6759966404647442 52 eq_refl), (bits_val 13588059942349018923 true 5203466199602987 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 75) with 75%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_76 : exp_t_ok 76.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609475491526397459 _ _ _ eq_refl) | split; [exact (bits_finite 13591102941469946584 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609475491526397459 false 6796672353750547 52 eq_refl), (bits_val 13591102941469946584 true 8246465320530648 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 76) with 76%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_77 : exp_t_ok 77.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609512396785174445 _ _ _ eq_refl) | split; [exact (bits_finite 13585344141126127099 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609512396785174445 false 6833577612527533 52 eq_refl), (bits_val 13585344141126127099 true 6991264604081659 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 77) with 77%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_78 : exp_t_ok 78.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609549502435857133 _ _ _ eq_refl) | split; [exact (bits_finite 13591800971496060602 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609549502435857133 false 6870683263210221 52 eq_refl), (bits_val 13591800971496060602 true 8944495346644666 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 78) with 78%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_79 : exp_t_ok 79.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609586809566553753 _ _ _ eq_refl) | split; [exact (bits_finite 4366684878742009146 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609586809566553753 false 6907990393906841 52 eq_refl), (bits_val 4366684878742009146 false 7200439447369018 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 79) with 79%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_80 : exp_t_ok 80.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609624319271280859 _ _ _ eq_refl) | split; [exact (bits_finite 4365934111530306343 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609624319271280859 false 6945500098633947 52 eq_refl), (bits_val 4365934111530306343 false 6449672235666215 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 80) with 80%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_81 : exp_t_ok 81.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609662032649995404 _ _ _ eq_refl) | split; [exact (bits_finite 13578587477079876522 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609662032649995404 false 6983213477348492 52 eq_refl), (bits_val 13578587477079876522 true 4738200185201578 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 81) with 81%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_82 : exp_t_ok 82.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609699950808626998 _ _ _ eq_refl) | split; [exact (bits_finite 4361116198887462764 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609699950808626998 false 7021131635980086 52 eq_refl), (bits_val 4361116198887462764 false 6135359220193132 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 82) with 82%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_83 : exp_t_ok 83.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609738074859110342 _ _ _ eq_refl) | split; [exact (bits_finite 13591255066430940452 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609738074859110342 false 7059255686463430 52 eq_refl), (bits_val 13591255066430940452 true 8398590281524516 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 83) with 83%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_84 : exp_t_ok 84.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609776405919417829 _ _ _ eq_refl) | split; [exact (bits_finite 13575924912210935484 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609776405919417829 false 7097586746770917 52 eq_refl), (bits_val 13575924912210935484 true 6579234943631036 109 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 84) with 84%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_85 : exp_t_ok 85.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609814945113592335 _ _ _ eq_refl) | split; [exact (bits_finite 13580124724857794617 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609814945113592335 false 7136125940945423 52 eq_refl), (bits_val 13580124724857794617 true 6275447963119673 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 85) with 85%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_86 : exp_t_ok 86.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609853693571780176 _ _ _ eq_refl) | split; [exact (bits_finite 13591046031677294033 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609853693571780176 false 7174874399133264 52 eq_refl), (bits_val 13591046031677294033 true 8189555527878097 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 86) with 86%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_87 : exp_t_ok 87.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609892652430264250 _ _ _ eq_refl) | split; [exact (bits_finite 13587768808785765938 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609892652430264250 false 7213833257617338 52 eq_refl), (bits_val 13587768808785765938 true 4912332636350002 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 87) with 87%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_88 : exp_t_ok 88.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609931822831497360 _ _ _ eq_refl) | split; [exact (bits_finite 4358495182437610174 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609931822831497360 false 7253003658850448 52 eq_refl), (bits_val 4358495182437610174 false 8017942397711038 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 88) with 88%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_89 : exp_t_ok 89.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4609971205924135715 _ _ _ eq_refl) | split; [exact (bits_finite 4357273091511307374 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4609971205924135715 false 7292386751488803 52 eq_refl), (bits_val 4357273091511307374 false 6795851471408238 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 89) with 89%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_90 : exp_t_ok 90.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610010802863072613 _ _ _ eq_refl) | split; [exact (bits_finite 13588302672336573747 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610010802863072613 false 7331983690425701 52 eq_refl), (bits_val 13588302672336573747 true 5446196187157811 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 90) with 90%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_91 : exp_t_ok 91.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610050614809472307 _ _ _ eq_refl) | split; [exact (bits_finite 4365730062588982955 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610050614809472307 false 7371795636825395 52 eq_refl), (bits_val 4365730062588982955 false 6245623294342827 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 91) with 91%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_92 : exp_t_ok 92.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610090642930804061 _ _ _ eq_refl) | split; [exact (bits_finite 13591071403650400737 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610090642930804061 false 7411823758157149 52 eq_refl), (bits_val 13591071403650400737 true 8214927500984801 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 92) with 92%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_93 : exp_t_ok 93.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610130888400876376 _ _ _ eq_refl) | split; [exact (bits_finite 4367308009094079431 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610130888400876376 false 7452069228229464 52 eq_refl), (bits_val 4367308009094079431 false 7823569799439303 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 93) with 93%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_94 : exp_t_ok 94.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610171352399871423 _ _ _ eq_refl) | split; [exact (bits_finite 4364263780368514353 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610171352399871423 false 7492533227224511 52 eq_refl), (bits_val 4364263780368514353 false 4779341073874225 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 94) with 94%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_95 : exp_t_ok 95.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610212036114379642 _ _ _ eq_refl) | split; [exact (bits_finite 13587239356240194768 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610212036114379642 false 7533216941732730 52 eq_refl), (bits_val 13587239356240194768 true 8886479718149328 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 95) with 95%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_96 : exp_t_ok 96.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610252940737434541 _ _ _ eq_refl) | split; [exact (bits_finite 4366136266477915265 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610252940737434541 false 7574121564787629 52 eq_refl), (bits_val 4366136266477915265 false 6651827183275137 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 96) with 96%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_97 : exp_t_ok 97.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610294067468547686 _ _ _ eq_refl) | split; [exact (bits_finite 13590701445652472869 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610294067468547686 false 7615248295900774 52 eq_refl), (bits_val 13590701445652472869 true 7844969503056933 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 97) with 97%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_98 : exp_t_ok 98.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610335417513743867 _ _ _ eq_refl) | split; [exact (bits_finite 13574553368877389576 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610335417513743867 false 7656598341096955 52 eq_refl), (bits_val 13574553368877389576 true 5207691610085128 109 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 98) with 98%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_99 : exp_t_ok 99.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610376992085596474 _ _ _ eq_refl) | split; [exact (bits_finite 13590862981238517219 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610376992085596474 false 7698172912949562 52 eq_refl), (bits_val 13590862981238517219 true 8006505089101283 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 99) with 99%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_100 : exp_t_ok 100.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610418792403263047 _ _ _ eq_refl) | split; [exact (bits_finite 13579857349850737723 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610418792403263047 false 7739973230616135 52 eq_refl), (bits_val 13579857349850737723 true 6008072956062779 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 100) with 100%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_101 : exp_t_ok 101.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610460819692521034 _ _ _ eq_refl) | split; [exact (bits_finite 13591578708859431214 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610460819692521034 false 7782000519874122 52 eq_refl), (bits_val 13591578708859431214 true 8722232710015278 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 101) with 101%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_102 : exp_t_ok 102.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610503075185803730 _ _ _ eq_refl) | split; [exact (bits_finite 4360115354860363396 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610503075185803730 false 7824256013156818 52 eq_refl), (bits_val 4360115354860363396 false 5134515193093764 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 102) with 102%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_103 : exp_t_ok 103.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610545560122236425 _ _ _ eq_refl) | split; [exact (bits_finite 13591579770539973747 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610545560122236425 false 7866740949589513 52 eq_refl), (bits_val 13591579770539973747 true 8723294390557811 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 103) with 103%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_104 : exp_t_ok 104.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610588275747672732 _ _ _ eq_refl) | split; [exact (bits_finite 4359783942552832221 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610588275747672732 false 7909456575025820 52 eq_refl), (bits_val 4359783942552832221 false 4803102885562589 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 104) with 104%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_105 : exp_t_ok 105.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610631223314731130 _ _ _ eq_refl) | split; [exact (bits_finite 4367160369958077962 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610631223314731130 false 7952404142084218 52 eq_refl), (bits_val 4367160369958077962 false 7675930663437834 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 105) with 105%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_106 : exp_t_ok 106.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610674404082831691 _ _ _ eq_refl) | split; [exact (bits_finite 4364700857452215469 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610674404082831691 false 7995584910184779 52 eq_refl), (bits_val 4364700857452215469 false 5216418157575341 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 106) with 106%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_107 : exp_t_ok 107.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610717819318233013 _ _ _ eq_refl) | split; [exact (bits_finite 4355452239314181188 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610717819318233013 false 8039000145586101 52 eq_refl), (bits_val 4355452239314181188 false 4974999274282052 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 107) with 107%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_108 : exp_t_ok 108.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610761470294069353 _ _ _ eq_refl) | split; [exact (bits_finite 4356392388485794267 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610761470294069353 false 8082651121422441 52 eq_refl), (bits_val 4356392388485794267 false 5915148445895131 108 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 108) with 108%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_109 : exp_t_ok 109.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610805358290387962 _ _ _ eq_refl) | split; [exact (bits_finite 13586753400162393458 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610805358290387962 false 8126539117741050 52 eq_refl), (bits_val 13586753400162393458 true 8400523640348018 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 109) with 109%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_110 : exp_t_ok 110.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610849484594186620 _ _ _ eq_refl) | split; [exact (bits_finite 13590944721038572188 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610849484594186620 false 8170665421539708 52 eq_refl), (bits_val 13590944721038572188 true 8088244889156252 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 110) with 110%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_111 : exp_t_ok 111.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610893850499451378 _ _ _ eq_refl) | split; [exact (bits_finite 13591098945498350968 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610893850499451378 false 8215031326804466 52 eq_refl), (bits_val 13591098945498350968 true 8242469348935032 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 111) with 111%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_112 : exp_t_ok 112.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610938457307194503 _ _ _ eq_refl) | split; [exact (bits_finite 4360307985706858247 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610938457307194503 false 8259638134547591 52 eq_refl), (bits_val 4360307985706858247 false 5327146039588615 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 112) with 112%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_113 : exp_t_ok 113.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4610983306325492632 _ _ _ eq_refl) | split; [exact (bits_finite 13587675367378640872 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4610983306325492632 false 8304487152845720 52 eq_refl), (bits_val 13587675367378640872 true 4818891229224936 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 113) with 113%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_114 : exp_t_ok 114.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611028398869525125 _ _ _ eq_refl) | split; [exact (bits_finite 4367404223318308146 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611028398869525125 false 8349579696878213 52 eq_refl), (bits_val 4367404223318308146 false 7919784023668018 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 114) with 114%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_115 : exp_t_ok 115.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611073736261612640 _ _ _ eq_refl) | split; [exact (bits_finite 4364791058101442755 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611073736261612640 false 8394917088965728 52 eq_refl), (bits_val 4364791058101442755 false 5306618806802627 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 115) with 115%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_116 : exp_t_ok 116.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611119319831255903 _ _ _ eq_refl) | split; [exact (bits_finite 13587823851967368028 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611119319831255903 false 8440500658608991 52 eq_refl), (bits_val 13587823851967368028 true 4967375817952092 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 116) with 116%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_117 : exp_t_ok 117.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611165150915174697 _ _ _ eq_refl) | split; [exact (bits_finite 13589530681406002326 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611165150915174697 false 8486331742527785 52 eq_refl), (bits_val 13589530681406002326 true 6674205256586390 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 117) with 117%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_118 : exp_t_ok 118.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611211230857347062 _ _ _ eq_refl) | split; [exact (bits_finite 4360503177631091855 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611211230857347062 false 8532411684700150 52 eq_refl), (bits_val 4360503177631091855 false 5522337963822223 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 118) with 118%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_119 : exp_t_ok 119.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611257561009048707 _ _ _ eq_refl) | split; [exact (bits_finite 4364785334270856674 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611257561009048707 false 8578741836401795 52 eq_refl), (bits_val 4364785334270856674 false 5300894976216546 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 119) with 119%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_120 : exp_t_ok 120.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611304142728892634 _ _ _ eq_refl) | split; [exact (bits_finite 13591472399984634003 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611304142728892634 false 8625323556245722 52 eq_refl), (bits_val 13591472399984634003 true 8615923835218067 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 120) with 120%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_121 : exp_t_ok 121.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611350977382868977 _ _ _ eq_refl) | split; [exact (bits_finite 13590900450404707724 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611350977382868977 false 8672158210222065 52 eq_refl), (bits_val 13590900450404707724 true 8043974255291788 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 121) with 121%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_122 : exp_t_ok 122.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611398066344385063 _ _ _ eq_refl) | split; [exact (bits_finite 4367867066664138416 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611398066344385063 false 8719247171738151 52 eq_refl), (bits_val 4367867066664138416 false 8382627369498288 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 122) with 122%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_123 : exp_t_ok 123.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611445410994305687 _ _ _ eq_refl) | split; [exact (bits_finite 4365010197099155011 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611445410994305687 false 8766591821658775 52 eq_refl), (bits_val 4365010197099155011 false 5525757804514883 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 123) with 123%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_124 : exp_t_ok 124.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611493012720993600 _ _ _ eq_refl) | split; [exact (bits_finite 4366754277802680715 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611493012720993600 false 8814193548346688 52 eq_refl), (bits_val 4366754277802680715 false 7269838508040587 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 124) with 124%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_125 : exp_t_ok 125.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611540872920350228 _ _ _ eq_refl) | split; [exact (bits_finite 13591224939947898122 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611540872920350228 false 8862053747703316 52 eq_refl), (bits_val 13591224939947898122 true 8368463798482186 106 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 125) with 125%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_126 : exp_t_ok 126.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611588992995856600 _ _ _ eq_refl) | split; [exact (bits_finite 4361534289538814750 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611588992995856600 false 8910173823209688 52 eq_refl), (bits_val 4361534289538814750 false 6553449871545118 107 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 126) with 126%Z.
  interval with (i_prec 160).
Qed.
Lemma exp_t_ok_127 : exp_t_ok 127.
Proof.
  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].
  split; [exact (bits_finite 4611637374358614513 _ _ _ eq_refl) | split; [exact (bits_finite 4351299075965286887 _ _ _ eq_refl) | ]].
  rewrite (bits_val 4611637374358614513 false 8958555185967601 52 eq_refl), (bits_val 4351299075965286887 false 5325435552758247 109 eq_refl); cbn [cond_Zopp].
  split; [apply (val_grid _ _ 120); lia | split; [apply (val_grid _ _ 120); lia | ]].
  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].
  rewrite INR_IZR_INZ; change (Z.of_nat 127) with 127%Z.
  interval with (i_prec 160).
Qed.

Theorem exp_table_ok j : (j < 128)%nat -> exp_t_ok j.
Proof.
  intros H.
  destruct j as [|j]; [exact exp_t_ok_0 | ].
  destruct j as [|j]; [exact exp_t_ok_1 | ].
  destruct j as [|j]; [exact exp_t_ok_2 | ].
  destruct j as [|j]; [exact exp_t_ok_3 | ].
  destruct j as [|j]; [exact exp_t_ok_4 | ].
  destruct j as [|j]; [exact exp_t_ok_5 | ].
  destruct j as [|j]; [exact exp_t_ok_6 | ].
  destruct j as [|j]; [exact exp_t_ok_7 | ].
  destruct j as [|j]; [exact exp_t_ok_8 | ].
  destruct j as [|j]; [exact exp_t_ok_9 | ].
  destruct j as [|j]; [exact exp_t_ok_10 | ].
  destruct j as [|j]; [exact exp_t_ok_11 | ].
  destruct j as [|j]; [exact exp_t_ok_12 | ].
  destruct j as [|j]; [exact exp_t_ok_13 | ].
  destruct j as [|j]; [exact exp_t_ok_14 | ].
  destruct j as [|j]; [exact exp_t_ok_15 | ].
  destruct j as [|j]; [exact exp_t_ok_16 | ].
  destruct j as [|j]; [exact exp_t_ok_17 | ].
  destruct j as [|j]; [exact exp_t_ok_18 | ].
  destruct j as [|j]; [exact exp_t_ok_19 | ].
  destruct j as [|j]; [exact exp_t_ok_20 | ].
  destruct j as [|j]; [exact exp_t_ok_21 | ].
  destruct j as [|j]; [exact exp_t_ok_22 | ].
  destruct j as [|j]; [exact exp_t_ok_23 | ].
  destruct j as [|j]; [exact exp_t_ok_24 | ].
  destruct j as [|j]; [exact exp_t_ok_25 | ].
  destruct j as [|j]; [exact exp_t_ok_26 | ].
  destruct j as [|j]; [exact exp_t_ok_27 | ].
  destruct j as [|j]; [exact exp_t_ok_28 | ].
  destruct j as [|j]; [exact exp_t_ok_29 | ].
  destruct j as [|j]; [exact exp_t_ok_30 | ].
  destruct j as [|j]; [exact exp_t_ok_31 | ].
  destruct j as [|j]; [exact exp_t_ok_32 | ].
  destruct j as [|j]; [exact exp_t_ok_33 | ].
  destruct j as [|j]; [exact exp_t_ok_34 | ].
  destruct j as [|j]; [exact exp_t_ok_35 | ].
  destruct j as [|j]; [exact exp_t_ok_36 | ].
  destruct j as [|j]; [exact exp_t_ok_37 | ].
  destruct j as [|j]; [exact exp_t_ok_38 | ].
  destruct j as [|j]; [exact exp_t_ok_39 | ].
  destruct j as [|j]; [exact exp_t_ok_40 | ].
  destruct j as [|j]; [exact exp_t_ok_41 | ].
  destruct j as [|j]; [exact exp_t_ok_42 | ].
  destruct j as [|j]; [exact exp_t_ok_43 | ].
  destruct j as [|j]; [exact exp_t_ok_44 | ].
  destruct j as [|j]; [exact exp_t_ok_45 | ].
  destruct j as [|j]; [exact exp_t_ok_46 | ].
  destruct j as [|j]; [exact exp_t_ok_47 | ].
  destruct j as [|j]; [exact exp_t_ok_48 | ].
  destruct j as [|j]; [exact exp_t_ok_49 | ].
  destruct j as [|j]; [exact exp_t_ok_50 | ].
  destruct j as [|j]; [exact exp_t_ok_51 | ].
  destruct j as [|j]; [exact exp_t_ok_52 | ].
  destruct j as [|j]; [exact exp_t_ok_53 | ].
  destruct j as [|j]; [exact exp_t_ok_54 | ].
  destruct j as [|j]; [exact exp_t_ok_55 | ].
  destruct j as [|j]; [exact exp_t_ok_56 | ].
  destruct j as [|j]; [exact exp_t_ok_57 | ].
  destruct j as [|j]; [exact exp_t_ok_58 | ].
  destruct j as [|j]; [exact exp_t_ok_59 | ].
  destruct j as [|j]; [exact exp_t_ok_60 | ].
  destruct j as [|j]; [exact exp_t_ok_61 | ].
  destruct j as [|j]; [exact exp_t_ok_62 | ].
  destruct j as [|j]; [exact exp_t_ok_63 | ].
  destruct j as [|j]; [exact exp_t_ok_64 | ].
  destruct j as [|j]; [exact exp_t_ok_65 | ].
  destruct j as [|j]; [exact exp_t_ok_66 | ].
  destruct j as [|j]; [exact exp_t_ok_67 | ].
  destruct j as [|j]; [exact exp_t_ok_68 | ].
  destruct j as [|j]; [exact exp_t_ok_69 | ].
  destruct j as [|j]; [exact exp_t_ok_70 | ].
  destruct j as [|j]; [exact exp_t_ok_71 | ].
  destruct j as [|j]; [exact exp_t_ok_72 | ].
  destruct j as [|j]; [exact exp_t_ok_73 | ].
  destruct j as [|j]; [exact exp_t_ok_74 | ].
  destruct j as [|j]; [exact exp_t_ok_75 | ].
  destruct j as [|j]; [exact exp_t_ok_76 | ].
  destruct j as [|j]; [exact exp_t_ok_77 | ].
  destruct j as [|j]; [exact exp_t_ok_78 | ].
  destruct j as [|j]; [exact exp_t_ok_79 | ].
  destruct j as [|j]; [exact exp_t_ok_80 | ].
  destruct j as [|j]; [exact exp_t_ok_81 | ].
  destruct j as [|j]; [exact exp_t_ok_82 | ].
  destruct j as [|j]; [exact exp_t_ok_83 | ].
  destruct j as [|j]; [exact exp_t_ok_84 | ].
  destruct j as [|j]; [exact exp_t_ok_85 | ].
  destruct j as [|j]; [exact exp_t_ok_86 | ].
  destruct j as [|j]; [exact exp_t_ok_87 | ].
  destruct j as [|j]; [exact exp_t_ok_88 | ].
  destruct j as [|j]; [exact exp_t_ok_89 | ].
  destruct j as [|j]; [exact exp_t_ok_90 | ].
  destruct j as [|j]; [exact exp_t_ok_91 | ].
  destruct j as [|j]; [exact exp_t_ok_92 | ].
  destruct j as [|j]; [exact exp_t_ok_93 | ].
  destruct j as [|j]; [exact exp_t_ok_94 | ].
  destruct j as [|j]; [exact exp_t_ok_95 | ].
  destruct j as [|j]; [exact exp_t_ok_96 | ].
  destruct j as [|j]; [exact exp_t_ok_97 | ].
  destruct j as [|j]; [exact exp_t_ok_98 | ].
  destruct j as [|j]; [exact exp_t_ok_99 | ].
  destruct j as [|j]; [exact exp_t_ok_100 | ].
  destruct j as [|j]; [exact exp_t_ok_101 | ].
  destruct j as [|j]; [exact exp_t_ok_102 | ].
  destruct j as [|j]; [exact exp_t_ok_103 | ].
  destruct j as [|j]; [exact exp_t_ok_104 | ].
  destruct j as [|j]; [exact exp_t_ok_105 | ].
  destruct j as [|j]; [exact exp_t_ok_106 | ].
  destruct j as [|j]; [exact exp_t_ok_107 | ].
  destruct j as [|j]; [exact exp_t_ok_108 | ].
  destruct j as [|j]; [exact exp_t_ok_109 | ].
  destruct j as [|j]; [exact exp_t_ok_110 | ].
  destruct j as [|j]; [exact exp_t_ok_111 | ].
  destruct j as [|j]; [exact exp_t_ok_112 | ].
  destruct j as [|j]; [exact exp_t_ok_113 | ].
  destruct j as [|j]; [exact exp_t_ok_114 | ].
  destruct j as [|j]; [exact exp_t_ok_115 | ].
  destruct j as [|j]; [exact exp_t_ok_116 | ].
  destruct j as [|j]; [exact exp_t_ok_117 | ].
  destruct j as [|j]; [exact exp_t_ok_118 | ].
  destruct j as [|j]; [exact exp_t_ok_119 | ].
  destruct j as [|j]; [exact exp_t_ok_120 | ].
  destruct j as [|j]; [exact exp_t_ok_121 | ].
  destruct j as [|j]; [exact exp_t_ok_122 | ].
  destruct j as [|j]; [exact exp_t_ok_123 | ].
  destruct j as [|j]; [exact exp_t_ok_124 | ].
  destruct j as [|j]; [exact exp_t_ok_125 | ].
  destruct j as [|j]; [exact exp_t_ok_126 | ].
  destruct j as [|j]; [exact exp_t_ok_127 | ].
  lia.
Qed.

(** The accurate path's [T_j = 2^(j/128)] as a 128-bit significand [m], value
    [m·2^-127], top bit set, within [2^-127] relatively ([eT] in
    formal/exp/accurate_y.g). *)
Definition exp_tq_bits : list Z := [
  170141183460469231731687303715884105728%Z;
  171065033261874822595940777772823543072%Z;
  171993899476345128343537119045365325557%Z;
  172927809342507031348432869633015363432%Z;
  173866790246890464404407762706616159231%Z;
  174810869724731509663126252247200298628%Z;
  175760075460779858320016513849272112514%Z;
  176714435290110654726396343327124732509%Z;
  177673977198940748734846910156470796722%Z;
  178638729325449380214104983772752463190%Z;
  179608719960603319799715833212640078166%Z;
  180583977548986490077366315890632763559%Z;
  181564530689634091527204551507873002851%Z;
  182550408136871257689552875062520019860%Z;
  183541638801156264145238352458220470466%Z;
  184538251749928316037303918111582190741%Z;
  185540276208459938995127072211809418384%Z;
  186547741560713998456965993119841707198%Z;
  187560677350205372522678836423290891574%Z;
  188579113280867303604824886494904384726%Z;
  189603079217922454283560100755503568070%Z;
  190632605188758692908688464665597913127%Z;
  191667721383809634630928502058329737186%Z;
  192708458157439963683905328040784845583%Z;
  193754846028835562878586879676558002648%Z;
  194806915682898476412852524570078383438%Z;
  195864697971146732240617263178179563239%Z;
  196928223912619050387439363498877599725%Z;
  197997524694784463742817675621853945428%Z;
  199072631674456878003441270051244360225%Z;
  200153576378714597586492652124699894469%Z;
  201240390505824844477730872587051456433%Z;
  202333105926173297125496651828617737974%Z;
  203431754683198676638992456051419475698%Z;
  204536368994332407697200624579210771631%Z;
  205646981251943381723616489017548850871%Z;
  206763624024287850031595310903942987551%Z;
  207886330056464474795546182466874386911%Z;
  209015132271374565854457196561826421515%Z;
  210150063770687531506308632151678761712%Z;
  211291157835811571604829080310840425937%Z;
  212438447928869641423777836334709202017%Z;
  213591967693680714908500014151756667305%Z;
  214751750956746376089903232366178353393%Z;
  215917831728242767592250934017081204392%Z;
  217090244203017925323262016382739148704%Z;
  218269022761594528592954069621697274351%Z;
  219454201971178095066472785476732527375%Z;
  220645816586670650115817656573116837915%Z;
  221843901551689900295908625206017671769%Z;
  223048491999593940831844565543762752175%Z;
  224259623254511527166487128046501415028%Z;
  225477330832377940780667298486584212083%Z;
  226701650441976479662361810971034597682%Z;
  227932617985985603966127115501601423481%Z;
  229170269562031767569914772679449736778%Z;
  230414641463747966403128794248390520516%Z;
  231665770181838034587427457757525115372%Z;
  232923692405146719600324412745563983923%Z;
  234188445021735567841111407232729062005%Z;
  235460065119964652149012666518444531086%Z;
  236738589989580172994793847874596794888%Z;
  238024057122807965239291598376410960284%Z;
  239316504215452942525508109785451692896%Z;
  240615969168004511545033772477625056927%Z;
  241922490086747988594625185854181211894%Z;
  243236105284882051014780519171304462938%Z;
  244556853283642256279124695835041726414%Z;
  245884772813430661681348285520943998370%Z;
  247219902814951577745341549758707930481%Z;
  248562282440353488664034043970094072716%Z;
  249911951054377173253295806948050327903%Z;
  251268948235510060089083770641341984634%Z;
  252633313777146850678831930883129301358%Z;
  254005087688756444701891394347232966737%Z;
  255384310197055201538632048615235212163%Z;
  256771021747186572493626710141645653941%Z;
  258165263003907138305156637890219514760%Z;
  259567074852779086721109736845575993922%Z;
  260976498401369165110195123590922154132%Z;
  262393574980454143267275523703833468727%Z;
  263818346145232821762527785947461763669%Z;
  265250853676544621376087229448197252990%Z;
  266691139582094789352819215975011778785%Z;
  268139246097686258405896919356168825214%Z;
  269595215688458194592953438000777772607%Z;
  271059091050131270384724885347089774301%Z;
  272530915110259699443314648811757761933%Z;
  274010731029490069825493413672447559405%Z;
  275498582202827012525810618890372253821%Z;
  276994512260905742474736593352467469570%Z;
  278498565071271509308586591312165905405%Z;
  280010784739665995430604214776763400232%Z;
  281531215611320699086308220161760740299%Z;
  283059902272257340381039430905991933019%Z;
  284596889550595328373589423552789887474%Z;
  286142222517866327586855861304318312414%Z;
  287695946490335962484656888293481580335%Z;
  289258107030332698673154974806083447724%Z;
  290828749947583939795795156590342846649%Z;
  292407921300559379302259911706322512484%Z;
  293995667397821646484689171099722683577%Z;
  295592034799384286388315402930842134617%Z;
  297197070318077113418726618223830257616%Z;
  298810821020918978684200823256618578890%Z;
  300433334230497991328960233165493184947%Z;
  302064657526359234331778836797853273837%Z;
  303704838746400015464149074837288087259%Z;
  305353925988272694323178906376946299117%Z;
  307011967610795126576555873154767988912%Z;
  308679012235368766780286440496262334430%Z;
  310355108747404471354503449921217179046%Z;
  312040306297756043528438546211487503611%Z;
  313734654304161562292686563119818614262%Z;
  315438202452692537625151724391204911890%Z;
  317151000699210934486567834085183572369%Z;
  318873099270834108312233122392550783251%Z;
  320604548667407694958601846839678481396%Z;
  322345399662986498296635927316317633099%Z;
  324095703307323418878347657038424943700%Z;
  325855510927366467338765757798166302659%Z;
  327624874128763906432638651434630882064%Z;
  329403844797377565843557752703282034411%Z;
  331192475100804374142846841702545253207%Z;
  332990817489906152516528174760363655117%Z;
  334798924700347715120949007381709906663%Z;
  336616849754143321171240736068313607683%Z;
  338444645961211524111694060679677685513%Z
].
Definition exp_tq (j : nat) : Z := nth j exp_tq_bits 0%Z.

Definition exp_tq_ok (j : nat) : Prop :=
  (2 ^ 127 <= exp_tq j < 2 ^ 128)%Z /\
  Rabs ((IZR (exp_tq j) / 2 ^ 127 - exp (INR j * ln 2 / 128)) / exp (INR j * ln 2 / 128)) <= / 2 ^ 127.

Lemma exp_tq_ok_0 : exp_tq_ok 0.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 0) with 0%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_1 : exp_tq_ok 1.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 1) with 1%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_2 : exp_tq_ok 2.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 2) with 2%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_3 : exp_tq_ok 3.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 3) with 3%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_4 : exp_tq_ok 4.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 4) with 4%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_5 : exp_tq_ok 5.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 5) with 5%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_6 : exp_tq_ok 6.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 6) with 6%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_7 : exp_tq_ok 7.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 7) with 7%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_8 : exp_tq_ok 8.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 8) with 8%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_9 : exp_tq_ok 9.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 9) with 9%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_10 : exp_tq_ok 10.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 10) with 10%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_11 : exp_tq_ok 11.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 11) with 11%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_12 : exp_tq_ok 12.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 12) with 12%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_13 : exp_tq_ok 13.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 13) with 13%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_14 : exp_tq_ok 14.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 14) with 14%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_15 : exp_tq_ok 15.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 15) with 15%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_16 : exp_tq_ok 16.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 16) with 16%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_17 : exp_tq_ok 17.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 17) with 17%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_18 : exp_tq_ok 18.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 18) with 18%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_19 : exp_tq_ok 19.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 19) with 19%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_20 : exp_tq_ok 20.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 20) with 20%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_21 : exp_tq_ok 21.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 21) with 21%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_22 : exp_tq_ok 22.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 22) with 22%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_23 : exp_tq_ok 23.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 23) with 23%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_24 : exp_tq_ok 24.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 24) with 24%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_25 : exp_tq_ok 25.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 25) with 25%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_26 : exp_tq_ok 26.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 26) with 26%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_27 : exp_tq_ok 27.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 27) with 27%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_28 : exp_tq_ok 28.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 28) with 28%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_29 : exp_tq_ok 29.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 29) with 29%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_30 : exp_tq_ok 30.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 30) with 30%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_31 : exp_tq_ok 31.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 31) with 31%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_32 : exp_tq_ok 32.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 32) with 32%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_33 : exp_tq_ok 33.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 33) with 33%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_34 : exp_tq_ok 34.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 34) with 34%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_35 : exp_tq_ok 35.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 35) with 35%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_36 : exp_tq_ok 36.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 36) with 36%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_37 : exp_tq_ok 37.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 37) with 37%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_38 : exp_tq_ok 38.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 38) with 38%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_39 : exp_tq_ok 39.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 39) with 39%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_40 : exp_tq_ok 40.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 40) with 40%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_41 : exp_tq_ok 41.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 41) with 41%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_42 : exp_tq_ok 42.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 42) with 42%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_43 : exp_tq_ok 43.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 43) with 43%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_44 : exp_tq_ok 44.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 44) with 44%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_45 : exp_tq_ok 45.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 45) with 45%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_46 : exp_tq_ok 46.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 46) with 46%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_47 : exp_tq_ok 47.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 47) with 47%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_48 : exp_tq_ok 48.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 48) with 48%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_49 : exp_tq_ok 49.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 49) with 49%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_50 : exp_tq_ok 50.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 50) with 50%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_51 : exp_tq_ok 51.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 51) with 51%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_52 : exp_tq_ok 52.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 52) with 52%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_53 : exp_tq_ok 53.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 53) with 53%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_54 : exp_tq_ok 54.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 54) with 54%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_55 : exp_tq_ok 55.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 55) with 55%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_56 : exp_tq_ok 56.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 56) with 56%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_57 : exp_tq_ok 57.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 57) with 57%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_58 : exp_tq_ok 58.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 58) with 58%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_59 : exp_tq_ok 59.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 59) with 59%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_60 : exp_tq_ok 60.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 60) with 60%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_61 : exp_tq_ok 61.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 61) with 61%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_62 : exp_tq_ok 62.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 62) with 62%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_63 : exp_tq_ok 63.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 63) with 63%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_64 : exp_tq_ok 64.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 64) with 64%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_65 : exp_tq_ok 65.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 65) with 65%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_66 : exp_tq_ok 66.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 66) with 66%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_67 : exp_tq_ok 67.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 67) with 67%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_68 : exp_tq_ok 68.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 68) with 68%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_69 : exp_tq_ok 69.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 69) with 69%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_70 : exp_tq_ok 70.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 70) with 70%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_71 : exp_tq_ok 71.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 71) with 71%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_72 : exp_tq_ok 72.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 72) with 72%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_73 : exp_tq_ok 73.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 73) with 73%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_74 : exp_tq_ok 74.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 74) with 74%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_75 : exp_tq_ok 75.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 75) with 75%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_76 : exp_tq_ok 76.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 76) with 76%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_77 : exp_tq_ok 77.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 77) with 77%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_78 : exp_tq_ok 78.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 78) with 78%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_79 : exp_tq_ok 79.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 79) with 79%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_80 : exp_tq_ok 80.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 80) with 80%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_81 : exp_tq_ok 81.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 81) with 81%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_82 : exp_tq_ok 82.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 82) with 82%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_83 : exp_tq_ok 83.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 83) with 83%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_84 : exp_tq_ok 84.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 84) with 84%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_85 : exp_tq_ok 85.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 85) with 85%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_86 : exp_tq_ok 86.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 86) with 86%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_87 : exp_tq_ok 87.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 87) with 87%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_88 : exp_tq_ok 88.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 88) with 88%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_89 : exp_tq_ok 89.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 89) with 89%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_90 : exp_tq_ok 90.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 90) with 90%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_91 : exp_tq_ok 91.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 91) with 91%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_92 : exp_tq_ok 92.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 92) with 92%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_93 : exp_tq_ok 93.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 93) with 93%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_94 : exp_tq_ok 94.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 94) with 94%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_95 : exp_tq_ok 95.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 95) with 95%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_96 : exp_tq_ok 96.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 96) with 96%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_97 : exp_tq_ok 97.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 97) with 97%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_98 : exp_tq_ok 98.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 98) with 98%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_99 : exp_tq_ok 99.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 99) with 99%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_100 : exp_tq_ok 100.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 100) with 100%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_101 : exp_tq_ok 101.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 101) with 101%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_102 : exp_tq_ok 102.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 102) with 102%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_103 : exp_tq_ok 103.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 103) with 103%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_104 : exp_tq_ok 104.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 104) with 104%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_105 : exp_tq_ok 105.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 105) with 105%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_106 : exp_tq_ok 106.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 106) with 106%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_107 : exp_tq_ok 107.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 107) with 107%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_108 : exp_tq_ok 108.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 108) with 108%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_109 : exp_tq_ok 109.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 109) with 109%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_110 : exp_tq_ok 110.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 110) with 110%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_111 : exp_tq_ok 111.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 111) with 111%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_112 : exp_tq_ok 112.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 112) with 112%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_113 : exp_tq_ok 113.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 113) with 113%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_114 : exp_tq_ok 114.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 114) with 114%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_115 : exp_tq_ok 115.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 115) with 115%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_116 : exp_tq_ok 116.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 116) with 116%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_117 : exp_tq_ok 117.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 117) with 117%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_118 : exp_tq_ok 118.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 118) with 118%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_119 : exp_tq_ok 119.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 119) with 119%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_120 : exp_tq_ok 120.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 120) with 120%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_121 : exp_tq_ok 121.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 121) with 121%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_122 : exp_tq_ok 122.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 122) with 122%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_123 : exp_tq_ok 123.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 123) with 123%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_124 : exp_tq_ok 124.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 124) with 124%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_125 : exp_tq_ok 125.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 125) with 125%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_126 : exp_tq_ok 126.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 126) with 126%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_tq_ok_127 : exp_tq_ok 127.
Proof.
  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 127) with 127%Z.
  interval with (i_prec 200).
Qed.

Theorem exp_tq_table_ok j : (j < 128)%nat -> exp_tq_ok j.
Proof.
  intros H.
  destruct j as [|j]; [exact exp_tq_ok_0 | ].
  destruct j as [|j]; [exact exp_tq_ok_1 | ].
  destruct j as [|j]; [exact exp_tq_ok_2 | ].
  destruct j as [|j]; [exact exp_tq_ok_3 | ].
  destruct j as [|j]; [exact exp_tq_ok_4 | ].
  destruct j as [|j]; [exact exp_tq_ok_5 | ].
  destruct j as [|j]; [exact exp_tq_ok_6 | ].
  destruct j as [|j]; [exact exp_tq_ok_7 | ].
  destruct j as [|j]; [exact exp_tq_ok_8 | ].
  destruct j as [|j]; [exact exp_tq_ok_9 | ].
  destruct j as [|j]; [exact exp_tq_ok_10 | ].
  destruct j as [|j]; [exact exp_tq_ok_11 | ].
  destruct j as [|j]; [exact exp_tq_ok_12 | ].
  destruct j as [|j]; [exact exp_tq_ok_13 | ].
  destruct j as [|j]; [exact exp_tq_ok_14 | ].
  destruct j as [|j]; [exact exp_tq_ok_15 | ].
  destruct j as [|j]; [exact exp_tq_ok_16 | ].
  destruct j as [|j]; [exact exp_tq_ok_17 | ].
  destruct j as [|j]; [exact exp_tq_ok_18 | ].
  destruct j as [|j]; [exact exp_tq_ok_19 | ].
  destruct j as [|j]; [exact exp_tq_ok_20 | ].
  destruct j as [|j]; [exact exp_tq_ok_21 | ].
  destruct j as [|j]; [exact exp_tq_ok_22 | ].
  destruct j as [|j]; [exact exp_tq_ok_23 | ].
  destruct j as [|j]; [exact exp_tq_ok_24 | ].
  destruct j as [|j]; [exact exp_tq_ok_25 | ].
  destruct j as [|j]; [exact exp_tq_ok_26 | ].
  destruct j as [|j]; [exact exp_tq_ok_27 | ].
  destruct j as [|j]; [exact exp_tq_ok_28 | ].
  destruct j as [|j]; [exact exp_tq_ok_29 | ].
  destruct j as [|j]; [exact exp_tq_ok_30 | ].
  destruct j as [|j]; [exact exp_tq_ok_31 | ].
  destruct j as [|j]; [exact exp_tq_ok_32 | ].
  destruct j as [|j]; [exact exp_tq_ok_33 | ].
  destruct j as [|j]; [exact exp_tq_ok_34 | ].
  destruct j as [|j]; [exact exp_tq_ok_35 | ].
  destruct j as [|j]; [exact exp_tq_ok_36 | ].
  destruct j as [|j]; [exact exp_tq_ok_37 | ].
  destruct j as [|j]; [exact exp_tq_ok_38 | ].
  destruct j as [|j]; [exact exp_tq_ok_39 | ].
  destruct j as [|j]; [exact exp_tq_ok_40 | ].
  destruct j as [|j]; [exact exp_tq_ok_41 | ].
  destruct j as [|j]; [exact exp_tq_ok_42 | ].
  destruct j as [|j]; [exact exp_tq_ok_43 | ].
  destruct j as [|j]; [exact exp_tq_ok_44 | ].
  destruct j as [|j]; [exact exp_tq_ok_45 | ].
  destruct j as [|j]; [exact exp_tq_ok_46 | ].
  destruct j as [|j]; [exact exp_tq_ok_47 | ].
  destruct j as [|j]; [exact exp_tq_ok_48 | ].
  destruct j as [|j]; [exact exp_tq_ok_49 | ].
  destruct j as [|j]; [exact exp_tq_ok_50 | ].
  destruct j as [|j]; [exact exp_tq_ok_51 | ].
  destruct j as [|j]; [exact exp_tq_ok_52 | ].
  destruct j as [|j]; [exact exp_tq_ok_53 | ].
  destruct j as [|j]; [exact exp_tq_ok_54 | ].
  destruct j as [|j]; [exact exp_tq_ok_55 | ].
  destruct j as [|j]; [exact exp_tq_ok_56 | ].
  destruct j as [|j]; [exact exp_tq_ok_57 | ].
  destruct j as [|j]; [exact exp_tq_ok_58 | ].
  destruct j as [|j]; [exact exp_tq_ok_59 | ].
  destruct j as [|j]; [exact exp_tq_ok_60 | ].
  destruct j as [|j]; [exact exp_tq_ok_61 | ].
  destruct j as [|j]; [exact exp_tq_ok_62 | ].
  destruct j as [|j]; [exact exp_tq_ok_63 | ].
  destruct j as [|j]; [exact exp_tq_ok_64 | ].
  destruct j as [|j]; [exact exp_tq_ok_65 | ].
  destruct j as [|j]; [exact exp_tq_ok_66 | ].
  destruct j as [|j]; [exact exp_tq_ok_67 | ].
  destruct j as [|j]; [exact exp_tq_ok_68 | ].
  destruct j as [|j]; [exact exp_tq_ok_69 | ].
  destruct j as [|j]; [exact exp_tq_ok_70 | ].
  destruct j as [|j]; [exact exp_tq_ok_71 | ].
  destruct j as [|j]; [exact exp_tq_ok_72 | ].
  destruct j as [|j]; [exact exp_tq_ok_73 | ].
  destruct j as [|j]; [exact exp_tq_ok_74 | ].
  destruct j as [|j]; [exact exp_tq_ok_75 | ].
  destruct j as [|j]; [exact exp_tq_ok_76 | ].
  destruct j as [|j]; [exact exp_tq_ok_77 | ].
  destruct j as [|j]; [exact exp_tq_ok_78 | ].
  destruct j as [|j]; [exact exp_tq_ok_79 | ].
  destruct j as [|j]; [exact exp_tq_ok_80 | ].
  destruct j as [|j]; [exact exp_tq_ok_81 | ].
  destruct j as [|j]; [exact exp_tq_ok_82 | ].
  destruct j as [|j]; [exact exp_tq_ok_83 | ].
  destruct j as [|j]; [exact exp_tq_ok_84 | ].
  destruct j as [|j]; [exact exp_tq_ok_85 | ].
  destruct j as [|j]; [exact exp_tq_ok_86 | ].
  destruct j as [|j]; [exact exp_tq_ok_87 | ].
  destruct j as [|j]; [exact exp_tq_ok_88 | ].
  destruct j as [|j]; [exact exp_tq_ok_89 | ].
  destruct j as [|j]; [exact exp_tq_ok_90 | ].
  destruct j as [|j]; [exact exp_tq_ok_91 | ].
  destruct j as [|j]; [exact exp_tq_ok_92 | ].
  destruct j as [|j]; [exact exp_tq_ok_93 | ].
  destruct j as [|j]; [exact exp_tq_ok_94 | ].
  destruct j as [|j]; [exact exp_tq_ok_95 | ].
  destruct j as [|j]; [exact exp_tq_ok_96 | ].
  destruct j as [|j]; [exact exp_tq_ok_97 | ].
  destruct j as [|j]; [exact exp_tq_ok_98 | ].
  destruct j as [|j]; [exact exp_tq_ok_99 | ].
  destruct j as [|j]; [exact exp_tq_ok_100 | ].
  destruct j as [|j]; [exact exp_tq_ok_101 | ].
  destruct j as [|j]; [exact exp_tq_ok_102 | ].
  destruct j as [|j]; [exact exp_tq_ok_103 | ].
  destruct j as [|j]; [exact exp_tq_ok_104 | ].
  destruct j as [|j]; [exact exp_tq_ok_105 | ].
  destruct j as [|j]; [exact exp_tq_ok_106 | ].
  destruct j as [|j]; [exact exp_tq_ok_107 | ].
  destruct j as [|j]; [exact exp_tq_ok_108 | ].
  destruct j as [|j]; [exact exp_tq_ok_109 | ].
  destruct j as [|j]; [exact exp_tq_ok_110 | ].
  destruct j as [|j]; [exact exp_tq_ok_111 | ].
  destruct j as [|j]; [exact exp_tq_ok_112 | ].
  destruct j as [|j]; [exact exp_tq_ok_113 | ].
  destruct j as [|j]; [exact exp_tq_ok_114 | ].
  destruct j as [|j]; [exact exp_tq_ok_115 | ].
  destruct j as [|j]; [exact exp_tq_ok_116 | ].
  destruct j as [|j]; [exact exp_tq_ok_117 | ].
  destruct j as [|j]; [exact exp_tq_ok_118 | ].
  destruct j as [|j]; [exact exp_tq_ok_119 | ].
  destruct j as [|j]; [exact exp_tq_ok_120 | ].
  destruct j as [|j]; [exact exp_tq_ok_121 | ].
  destruct j as [|j]; [exact exp_tq_ok_122 | ].
  destruct j as [|j]; [exact exp_tq_ok_123 | ].
  destruct j as [|j]; [exact exp_tq_ok_124 | ].
  destruct j as [|j]; [exact exp_tq_ok_125 | ].
  destruct j as [|j]; [exact exp_tq_ok_126 | ].
  destruct j as [|j]; [exact exp_tq_ok_127 | ].
  lia.
Qed.

(** [1/k], [k = 1..12], as a 128-bit significand [m] and exponent [-s]: value
    [m·2^-s], top bit set, within [2^-127] relatively ([k] in
    formal/exp/accurate_level_*.g). *)
Definition exp_recip_bits : list (Z * nat) := [
  (170141183460469231731687303715884105728%Z, 127%nat);
  (170141183460469231731687303715884105728%Z, 128%nat);
  (226854911280625642308916404954512140971%Z, 129%nat);
  (170141183460469231731687303715884105728%Z, 129%nat);
  (272225893536750770770699685945414569165%Z, 130%nat);
  (226854911280625642308916404954512140971%Z, 130%nat);
  (194447066811964836264785489961010406546%Z, 130%nat);
  (170141183460469231731687303715884105728%Z, 130%nat);
  (302473215040834189745221873272682854628%Z, 131%nat);
  (272225893536750770770699685945414569165%Z, 131%nat);
  (247478085033409791609726987223104153786%Z, 131%nat);
  (226854911280625642308916404954512140971%Z, 131%nat)
].
Definition exp_recip (k : nat) : Z * nat := nth (k - 1) exp_recip_bits (0%Z, 0%nat).

Definition exp_recip_ok (k : nat) : Prop :=
  (2 ^ 127 <= fst (exp_recip k) < 2 ^ 128)%Z /\
  Rabs (IZR (fst (exp_recip k)) / 2 ^ snd (exp_recip k) * INR k - 1) <= / 2 ^ 127.

Lemma exp_recip_ok_1 : exp_recip_ok 1.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 1) with 1%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_2 : exp_recip_ok 2.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 2) with 2%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_3 : exp_recip_ok 3.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 3) with 3%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_4 : exp_recip_ok 4.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 4) with 4%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_5 : exp_recip_ok 5.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 5) with 5%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_6 : exp_recip_ok 6.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 6) with 6%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_7 : exp_recip_ok 7.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 7) with 7%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_8 : exp_recip_ok 8.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 8) with 8%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_9 : exp_recip_ok 9.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 9) with 9%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_10 : exp_recip_ok 10.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 10) with 10%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_11 : exp_recip_ok 11.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 11) with 11%Z.
  interval with (i_prec 200).
Qed.
Lemma exp_recip_ok_12 : exp_recip_ok 12.
Proof.
  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].
  split; [lia | ].
  rewrite INR_IZR_INZ; change (Z.of_nat 12) with 12%Z.
  interval with (i_prec 200).
Qed.

Theorem exp_recip_table_ok k : (1 <= k <= 12)%nat -> exp_recip_ok k.
Proof.
  intros H.
  destruct k as [|k]; [lia | ].
  destruct k as [|k]; [exact exp_recip_ok_1 | ].
  destruct k as [|k]; [exact exp_recip_ok_2 | ].
  destruct k as [|k]; [exact exp_recip_ok_3 | ].
  destruct k as [|k]; [exact exp_recip_ok_4 | ].
  destruct k as [|k]; [exact exp_recip_ok_5 | ].
  destruct k as [|k]; [exact exp_recip_ok_6 | ].
  destruct k as [|k]; [exact exp_recip_ok_7 | ].
  destruct k as [|k]; [exact exp_recip_ok_8 | ].
  destruct k as [|k]; [exact exp_recip_ok_9 | ].
  destruct k as [|k]; [exact exp_recip_ok_10 | ].
  destruct k as [|k]; [exact exp_recip_ok_11 | ].
  destruct k as [|k]; [exact exp_recip_ok_12 | ].
  lia.
Qed.

(** The table segments of atan2 approximate [atan]: for [k = 1..64], with the
    segment's words, [|atan (k/64 + t) - (c0 + c1 + (cH + cL) t + t^2 G(t))|] is
    within the budget of [compose_<kk>.g] for every [|t| <= 0.0078126], and
    [atan (k/64 + t)] stays above [amin_<kk>]. Written by generators/atan2_proofs.py;
    do not edit. Each is proved by [interval] (bisection and Taylor models in
    [t]); Sollya's report is not an input. *)
From Coq Require Import Reals ZArith Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinSegment AsinSeriesSmall.
Import ListNotations.
Open Scope R_scope.

Lemma atan_le x y : x <= y -> atan x <= atan y.
Proof.
  intros H. destruct (Rle_lt_or_eq_dec x y H) as [L | E]; [apply Rlt_le, atan_increasing, L | rewrite E; apply Rle_refl].
Qed.

Lemma approx_01 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (9006466354344603) * bpow radix2 (-59) -> r1 = IZR (-318910881914869) * bpow radix2 (-109) -> rH = IZR (281406274007041) * bpow radix2 (-48) -> rL = IZR (-281406274007041) * bpow radix2 (-108) -> q0 = IZR (-281337588072453) * bpow radix2 (-54) -> q1 = IZR (-93687637131279) * bpow radix2 (-48) -> q2 = IZR (2249052912683959) * bpow radix2 (-57) -> q3 = IZR (3589700583778591) * bpow radix2 (-54) -> q4 = IZR (-2246674543185411) * bpow radix2 (-57) -> q5 = IZR (-638981608443631) * bpow radix2 (-52) -> q6 = IZR (4493728000047647) * bpow radix2 (-58) -> q7 = IZR (993762747007023) * bpow radix2 (-53) -> q8 = IZR (-3281081413173985) * bpow radix2 (-54) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 1 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13343168 * bpow radix2 (-101)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_01_num : IZR 1048540 * bpow radix2 (-27) <= atan (IZR 1 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_01 t : Rabs t <= 0.0078126 -> IZR 1048540 * bpow radix2 (-27) <= atan (IZR 1 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_01_num). apply atan_le. lra.
Qed.

Lemma approx_02 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (9004268940523045) * bpow radix2 (-58) -> r1 = IZR (-1542686839481419) * bpow radix2 (-110) -> rH = IZR (1124801467909119) * bpow radix2 (-50) -> rL = IZR (1124801467909119) * bpow radix2 (-110) -> q0 = IZR (-561852050311677) * bpow radix2 (-54) -> q1 = IZR (-186553152314869) * bpow radix2 (-49) -> q2 = IZR (2240834699373475) * bpow radix2 (-56) -> q3 = IZR (7100685917721701) * bpow radix2 (-55) -> q4 = IZR (-2231365338848543) * bpow radix2 (-56) -> q5 = IZR (-1251814315611373) * bpow radix2 (-53) -> q6 = IZR (8860729811190767) * bpow radix2 (-58) -> q7 = IZR (237910379149741) * bpow radix2 (-51) -> q8 = IZR (6446163112088107) * bpow radix2 (-54) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 2 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14982287 * bpow radix2 (-100)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_02_num : IZR 786283 * bpow radix2 (-25) <= atan (IZR 2 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_02 t : Rabs t <= 0.0078126 -> IZR 786283 * bpow radix2 (-25) <= atan (IZR 2 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_02_num). apply atan_le. lra.
Qed.

Lemma approx_03 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3375229075746069) * bpow radix2 (-56) -> r1 = IZR (-6877415025733893) * bpow radix2 (-115) -> rH = IZR (2246862859160725) * bpow radix2 (-51) -> rL = IZR (-5564496299640233) * bpow radix2 (-107) -> q0 = IZR (-6725810185960289) * bpow radix2 (-57) -> q1 = IZR (-5926067754050057) * bpow radix2 (-54) -> q2 = IZR (6681636873532033) * bpow radix2 (-57) -> q3 = IZR (3485342084430069) * bpow radix2 (-54) -> q4 = IZR (-827277083440457) * bpow radix2 (-54) -> q5 = IZR (-2417741191248767) * bpow radix2 (-54) -> q6 = IZR (6432679964552911) * bpow radix2 (-57) -> q7 = IZR (7274553898129947) * bpow radix2 (-56) -> q8 = IZR (1456085792123487) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 3 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12312434 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_03_num : IZR 655024 * bpow radix2 (-24) <= atan (IZR 3 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_03 t : Rabs t <= 0.0078126 -> IZR 655024 * bpow radix2 (-24) <= atan (IZR 3 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_03_num). apply atan_le. lra.
Qed.

Lemma approx_04 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4497749271019253) * bpow radix2 (-56) -> r1 = IZR (-8043260531588893) * bpow radix2 (-112) -> rH = IZR (280379743338241) * bpow radix2 (-48) -> rL = IZR (-280379743338241) * bpow radix2 (-104) -> q0 = IZR (-8937240690376927) * bpow radix2 (-57) -> q1 = IZR (-5865426445305739) * bpow radix2 (-54) -> q2 = IZR (8833185548119467) * bpow radix2 (-57) -> q3 = IZR (424447134355683) * bpow radix2 (-51) -> q4 = IZR (-4342256994236001) * bpow radix2 (-56) -> q5 = IZR (-71878620170311) * bpow radix2 (-49) -> q6 = IZR (8491581784845575) * bpow radix2 (-57) -> q7 = IZR (3310770793864807) * bpow radix2 (-55) -> q8 = IZR (5496213676697) * bpow radix2 (-50) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 4 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13505914 * bpow radix2 (-102)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_04_num : IZR 916588 * bpow radix2 (-24) <= atan (IZR 4 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_04 t : Rabs t <= 0.0078126 -> IZR 916588 * bpow radix2 (-24) <= atan (IZR 4 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_04_num). apply atan_le. lra.
Qed.

Lemma approx_05 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5618088049137053) * bpow radix2 (-56) -> r1 = IZR (7534739114031175) * bpow radix2 (-110) -> rH = IZR (8952557182096361) * bpow radix2 (-53) -> rL = IZR (-3925486498790299) * bpow radix2 (-108) -> q0 = IZR (-5561404121855541) * bpow radix2 (-56) -> q1 = IZR (-5788214763143219) * bpow radix2 (-54) -> q2 = IZR (5460598880592529) * bpow radix2 (-56) -> q3 = IZR (102570370853755) * bpow radix2 (-49) -> q4 = IZR (-5317452106799999) * bpow radix2 (-56) -> q5 = IZR (-2153283642573957) * bpow radix2 (-54) -> q6 = IZR (5173935332094699) * bpow radix2 (-56) -> q7 = IZR (744739081449859) * bpow radix2 (-53) -> q8 = IZR (-4583221480556721) * bpow radix2 (-50) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 5 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9444130 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_05_num : IZR 588853 * bpow radix2 (-23) <= atan (IZR 5 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_05 t : Rabs t <= 0.0078126 -> IZR 588853 * bpow radix2 (-23) <= atan (IZR 5 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_05_num). apply atan_le. lra.
Qed.

Lemma approx_06 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6735711948697871) * bpow radix2 (-56) -> r1 = IZR (-1019713979254707) * bpow radix2 (-107) -> rH = IZR (2232181035056819) * bpow radix2 (-51) -> rL = IZR (-5231674300914419) * bpow radix2 (-107) -> q0 = IZR (-6638199554399369) * bpow radix2 (-56) -> q1 = IZR (-5694985441098135) * bpow radix2 (-54) -> q2 = IZR (6465701632158165) * bpow radix2 (-56) -> q3 = IZR (6293738842806671) * bpow radix2 (-55) -> q4 = IZR (-1555643992597111) * bpow radix2 (-54) -> q5 = IZR (-7921374778086837) * bpow radix2 (-56) -> q6 = IZR (1508067532765085) * bpow radix2 (-54) -> q7 = IZR (5102437881521477) * bpow radix2 (-56) -> q8 = IZR (-1685120352180915) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 6 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14034219 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_06_num : IZR 719127 * bpow radix2 (-23) <= atan (IZR 6 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_06 t : Rabs t <= 0.0078126 -> IZR 719127 * bpow radix2 (-23) <= atan (IZR 6 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_06_num). apply atan_le. lra.
Qed.

Lemma approx_07 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (7850095310473155) * bpow radix2 (-56) -> r1 = IZR (8861579086944647) * bpow radix2 (-110) -> rH = IZR (4450360452040905) * bpow radix2 (-52) -> rL = IZR (6797230221671851) * bpow radix2 (-108) -> q0 = IZR (-7696063623698241) * bpow radix2 (-56) -> q1 = IZR (-5586398805212817) * bpow radix2 (-54) -> q2 = IZR (7425278236432933) * bpow radix2 (-56) -> q3 = IZR (2991199962317161) * bpow radix2 (-54) -> q4 = IZR (-880871315629739) * bpow radix2 (-53) -> q5 = IZR (-446223210752155) * bpow radix2 (-52) -> q6 = IZR (6656604118331663) * bpow radix2 (-56) -> q7 = IZR (2120199273569437) * bpow radix2 (-55) -> q8 = IZR (-4794672692954223) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 7 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9947964 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_07_num : IZR 849054 * bpow radix2 (-23) <= atan (IZR 7 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_07 t : Rabs t <= 0.0078126 -> IZR 849054 * bpow radix2 (-23) <= atan (IZR 7 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_07_num). apply atan_le. lra.
Qed.

Lemma approx_08 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4480360856819639) * bpow radix2 (-55) -> r1 = IZR (-8113805363383319) * bpow radix2 (-111) -> rH = IZR (277144592453569) * bpow radix2 (-48) -> rL = IZR (-277144592453569) * bpow radix2 (-102) -> q0 = IZR (-8732186543767835) * bpow radix2 (-56) -> q1 = IZR (-5463214145331671) * bpow radix2 (-54) -> q2 = IZR (8333296128850629) * bpow radix2 (-56) -> q3 = IZR (5634488478990681) * bpow radix2 (-55) -> q4 = IZR (-3890822488316401) * bpow radix2 (-55) -> q5 = IZR (-1570897632920293) * bpow radix2 (-54) -> q6 = IZR (3538020854539143) * bpow radix2 (-55) -> q7 = IZR (3241447238991003) * bpow radix2 (-56) -> q8 = IZR (5217418034259967) * bpow radix2 (-51) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 8 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11342246 * bpow radix2 (-97)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_08_num : IZR 978574 * bpow radix2 (-23) <= atan (IZR 8 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_08 t : Rabs t <= 0.0078126 -> IZR 978574 * bpow radix2 (-23) <= atan (IZR 8 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_08_num). apply atan_le. lra.
Qed.

Lemma approx_09 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5033542673512231) * bpow radix2 (-55) -> r1 = IZR (-1919842952590307) * bpow radix2 (-109) -> rH = IZR (4416266237421487) * bpow radix2 (-52) -> rL = IZR (1798420918949961) * bpow radix2 (-106) -> q0 = IZR (-1217988677402335) * bpow radix2 (-53) -> q1 = IZR (-1331569990592205) * bpow radix2 (-52) -> q2 = IZR (4592189375243179) * bpow radix2 (-55) -> q3 = IZR (5254385813433751) * bpow radix2 (-55) -> q4 = IZR (-8419419197104381) * bpow radix2 (-56) -> q5 = IZR (-5370381666193917) * bpow radix2 (-56) -> q6 = IZR (7573791757976131) * bpow radix2 (-56) -> q7 = IZR (1121693243182513) * bpow radix2 (-55) -> q8 = IZR (-4940539387106739) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 9 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10025210 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_09_num : IZR 553813 * bpow radix2 (-22) <= atan (IZR 9 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_09 t : Rabs t <= 0.0078126 -> IZR 553813 * bpow radix2 (-22) <= atan (IZR 9 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_09_num). apply atan_le. lra.
Qed.

Lemma approx_10 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1396086538344603) * bpow radix2 (-53) -> r1 = IZR (6221290409633819) * bpow radix2 (-109) -> rH = IZR (2198134422510671) * bpow radix2 (-51) -> rL = IZR (1253623537838117) * bpow radix2 (-105) -> q0 = IZR (-335273124501151) * bpow radix2 (-51) -> q1 = IZR (-1294130822351567) * bpow radix2 (-52) -> q2 = IZR (2493464544769251) * bpow radix2 (-54) -> q3 = IZR (2423383208383533) * bpow radix2 (-54) -> q4 = IZR (-1119372510211067) * bpow radix2 (-53) -> q5 = IZR (-8834910187494991) * bpow radix2 (-57) -> q6 = IZR (996852611950679) * bpow radix2 (-53) -> q7 = IZR (5143492910506691) * bpow radix2 (-58) -> q8 = IZR (-6839955651239147) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 10 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14261815 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_10_num : IZR 618077 * bpow radix2 (-22) <= atan (IZR 10 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_10 t : Rabs t <= 0.0078126 -> IZR 618077 * bpow radix2 (-22) <= atan (IZR 10 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_10_num). apply atan_le. lra.
Qed.

Lemma approx_11 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3066265453158709) * bpow radix2 (-54) -> r1 = IZR (-4596693781778237) * bpow radix2 (-110) -> rH = IZR (8748752228460779) * bpow radix2 (-53) -> rL = IZR (-3868161690855095) * bpow radix2 (-106) -> q0 = IZR (-5842183133826311) * bpow radix2 (-55) -> q1 = IZR (-5014938297614675) * bpow radix2 (-54) -> q2 = IZR (2674453490972731) * bpow radix2 (-54) -> q3 = IZR (2208254196833407) * bpow radix2 (-54) -> q4 = IZR (-4692466639080915) * bpow radix2 (-55) -> q5 = IZR (-860601178091087) * bpow radix2 (-54) -> q6 = IZR (7980265484940121) * bpow radix2 (-56) -> q7 = IZR (2240710524066713) * bpow radix2 (-59) -> q8 = IZR (-1972381584112781) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 11 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16428930 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_11_num : IZR 682050 * bpow radix2 (-22) <= atan (IZR 11 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_11 t : Rabs t <= 0.0078126 -> IZR 682050 * bpow radix2 (-22) <= atan (IZR 11 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_11_num). apply atan_le. lra.
Qed.

Lemma approx_12 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3338931834137985) * bpow radix2 (-54) -> r1 = IZR (2713424416751845) * bpow radix2 (-109) -> rH = IZR (4350647187195649) * bpow radix2 (-52) -> rL = IZR (-4894478085595105) * bpow radix2 (-109) -> q0 = IZR (-6304334037294827) * bpow radix2 (-55) -> q1 = IZR (-4842574405167347) * bpow radix2 (-54) -> q2 = IZR (5676548947574939) * bpow radix2 (-55) -> q3 = IZR (992150847238819) * bpow radix2 (-53) -> q4 = IZR (-4853906944194515) * bpow radix2 (-55) -> q5 = IZR (-4924975024838261) * bpow radix2 (-57) -> q6 = IZR (964033442286411) * bpow radix2 (-53) -> q7 = IZR (-5577731898527895) * bpow radix2 (-59) -> q8 = IZR (1437651861114777) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 12 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12145559 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_12_num : IZR 745704 * bpow radix2 (-22) <= atan (IZR 12 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_12 t : Rabs t <= 0.0078126 -> IZR 745704 * bpow radix2 (-22) <= atan (IZR 12 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_12_num). apply atan_le. lra.
Qed.

Lemma approx_13 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3610059409343251) * bpow radix2 (-54) -> r1 = IZR (4075893695322695) * bpow radix2 (-110) -> rH = IZR (8650290304201431) * bpow radix2 (-53) -> rL = IZR (2297733362053505) * bpow radix2 (-112) -> q0 = IZR (-3374931551275775) * bpow radix2 (-54) -> q1 = IZR (-4660524108587131) * bpow radix2 (-54) -> q2 = IZR (373042025332689) * bpow radix2 (-51) -> q3 = IZR (7016136643532211) * bpow radix2 (-56) -> q4 = IZR (-620250737668569) * bpow radix2 (-52) -> q5 = IZR (-2988377169941793) * bpow radix2 (-57) -> q6 = IZR (7442866831435031) * bpow radix2 (-56) -> q7 = IZR (-776303799805443) * bpow radix2 (-55) -> q8 = IZR (3051740535379715) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 13 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12834142 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_13_num : IZR 809014 * bpow radix2 (-22) <= atan (IZR 13 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_13 t : Rabs t <= 0.0078126 -> IZR 809014 * bpow radix2 (-22) <= atan (IZR 13 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_13_num). apply atan_le. lra.
Qed.

Lemma approx_14 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3879539424440401) * bpow radix2 (-54) -> r1 = IZR (4920386791728555) * bpow radix2 (-113) -> rH = IZR (4297936643455161) * bpow radix2 (-52) -> rL = IZR (2535111067038005) * bpow radix2 (-106) -> q0 = IZR (-3588957346258923) * bpow radix2 (-54) -> q1 = IZR (-2234955375791293) * bpow radix2 (-53) -> q2 = IZR (3112242473267141) * bpow radix2 (-54) -> q3 = IZR (189991316790621) * bpow radix2 (-51) -> q4 = IZR (-5017828309562461) * bpow radix2 (-55) -> q5 = IZR (-2211324384051107) * bpow radix2 (-58) -> q6 = IZR (7381747551193545) * bpow radix2 (-56) -> q7 = IZR (-4700068710827499) * bpow radix2 (-57) -> q8 = IZR (73646732880635) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 14 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12451798 * bpow radix2 (-100)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_14_num : IZR 871952 * bpow radix2 (-22) <= atan (IZR 14 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_14 t : Rabs t <= 0.0078126 -> IZR 871952 * bpow radix2 (-22) <= atan (IZR 14 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_14_num). apply atan_le. lra.
Qed.

Lemma approx_15 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4147267389893531) * bpow radix2 (-54) -> r1 = IZR (3995928228408511) * bpow radix2 (-108) -> rH = IZR (4269091431082979) * bpow radix2 (-52) -> rL = IZR (-5361378496457725) * bpow radix2 (-107) -> q0 = IZR (-7587739456310409) * bpow radix2 (-55) -> q1 = IZR (-8543752873678553) * bpow radix2 (-55) -> q2 = IZR (6443576612950217) * bpow radix2 (-55) -> q3 = IZR (1284400993394621) * bpow radix2 (-54) -> q4 = IZR (-5023221323153543) * bpow radix2 (-55) -> q5 = IZR (5563198311700309) * bpow radix2 (-60) -> q6 = IZR (3484880403387809) * bpow radix2 (-55) -> q7 = IZR (-376873249359707) * bpow radix2 (-53) -> q8 = IZR (2103396006319135) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 15 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 8950851 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_15_num : IZR 934494 * bpow radix2 (-22) <= atan (IZR 15 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_15 t : Rabs t <= 0.0078126 -> IZR 934494 * bpow radix2 (-22) <= atan (IZR 15 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_15_num). apply atan_le. lra.
Qed.

Lemma approx_16 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (8826286527774941) * bpow radix2 (-55) -> r1 = IZR (6943889398673341) * bpow radix2 (-109) -> rH = IZR (4238682002231055) * bpow radix2 (-52) -> rL = IZR (4238682002231055) * bpow radix2 (-108) -> q0 = IZR (-3989347766805699) * bpow radix2 (-54) -> q1 = IZR (-4067570272037183) * bpow radix2 (-54) -> q2 = IZR (3312953162771673) * bpow radix2 (-54) -> q3 = IZR (8398011468095751) * bpow radix2 (-57) -> q4 = IZR (-4980768998397751) * bpow radix2 (-55) -> q5 = IZR (4780950832887209) * bpow radix2 (-58) -> q6 = IZR (3337930558025369) * bpow radix2 (-55) -> q7 = IZR (-7251804897516987) * bpow radix2 (-57) -> q8 = IZR (-1945753261953285) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 16 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16255197 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_16_num : IZR 996616 * bpow radix2 (-22) <= atan (IZR 16 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_16 t : Rabs t <= 0.0078126 -> IZR 996616 * bpow radix2 (-22) <= atan (IZR 16 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_16_num). apply atan_le. lra.
Qed.

Lemma approx_17 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2338535804514737) * bpow radix2 (-53) -> r1 = IZR (6243332922325093) * bpow radix2 (-108) -> rH = IZR (4206783141096819) * bpow radix2 (-52) -> rL = IZR (309141046257359) * bpow radix2 (-104) -> q0 = IZR (-4175124339806923) * bpow radix2 (-54) -> q1 = IZR (-1929068561645403) * bpow radix2 (-53) -> q2 = IZR (6771783093866819) * bpow radix2 (-55) -> q3 = IZR (6545218315677847) * bpow radix2 (-57) -> q4 = IZR (-4893652862460237) * bpow radix2 (-55) -> q5 = IZR (7917898724680017) * bpow radix2 (-58) -> q6 = IZR (3097217383227697) * bpow radix2 (-55) -> q7 = IZR (-4101170408258213) * bpow radix2 (-56) -> q8 = IZR (-5620890705437541) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 17 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11757993 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_17_num : IZR 529147 * bpow radix2 (-21) <= atan (IZR 17 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_17 t : Rabs t <= 0.0078126 -> IZR 529147 * bpow radix2 (-21) <= atan (IZR 17 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_17_num). apply atan_le. lra.
Qed.

Lemma approx_18 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (617370215349807) * bpow radix2 (-51) -> r1 = IZR (5361925026946041) * bpow radix2 (-109) -> rH = IZR (4173471509889039) * bpow radix2 (-52) -> rL = IZR (-3113801009331275) * bpow radix2 (-106) -> q0 = IZR (-8701971365415697) * bpow radix2 (-55) -> q1 = IZR (-7289414056124321) * bpow radix2 (-55) -> q2 = IZR (6881842725139331) * bpow radix2 (-55) -> q3 = IZR (4732897261015489) * bpow radix2 (-57) -> q4 = IZR (-74461945570835) * bpow radix2 (-49) -> q5 = IZR (2692097012190501) * bpow radix2 (-56) -> q6 = IZR (5257517316827139) * bpow radix2 (-56) -> q7 = IZR (-8844567937328877) * bpow radix2 (-57) -> q8 = IZR (1972358009248669) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 18 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16565249 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_18_num : IZR 559755 * bpow radix2 (-21) <= atan (IZR 18 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_18 t : Rabs t <= 0.0078126 -> IZR 559755 * bpow radix2 (-21) <= atan (IZR 18 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_18_num). apply atan_le. lra.
Qed.

Lemma approx_19 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2599363870980003) * bpow radix2 (-53) -> r1 = IZR (-4635325526572161) * bpow radix2 (-108) -> rH = IZR (4138825235294941) * bpow radix2 (-52) -> rL = IZR (-6806427437731133) * bpow radix2 (-108) -> q0 = IZR (-4516770460954587) * bpow radix2 (-54) -> q1 = IZR (-3428385396229841) * bpow radix2 (-54) -> q2 = IZR (1739255201607401) * bpow radix2 (-53) -> q3 = IZR (5951303960482239) * bpow radix2 (-58) -> q4 = IZR (-4600630950987483) * bpow radix2 (-55) -> q5 = IZR (6653662703469329) * bpow radix2 (-57) -> q6 = IZR (2590797231680787) * bpow radix2 (-55) -> q7 = IZR (-146009608486677) * bpow radix2 (-51) -> q8 = IZR (-6089474562234827) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 19 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12756919 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_19_num : IZR 590121 * bpow radix2 (-21) <= atan (IZR 19 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_19 t : Rabs t <= 0.0078126 -> IZR 590121 * bpow radix2 (-21) <= atan (IZR 19 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_19_num). apply atan_le. lra.
Qed.

Lemma approx_20 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1364072180349683) * bpow radix2 (-52) -> r1 = IZR (-893304486415963) * bpow radix2 (-106) -> rH = IZR (4102923503938957) * bpow radix2 (-52) -> rL = IZR (1891191302596863) * bpow radix2 (-105) -> q0 = IZR (-2336184201531079) * bpow radix2 (-53) -> q1 = IZR (-6420488206532863) * bpow radix2 (-55) -> q2 = IZR (3499261380796319) * bpow radix2 (-54) -> q3 = IZR (5145968686663909) * bpow radix2 (-59) -> q4 = IZR (-2201601359030169) * bpow radix2 (-54) -> q5 = IZR (242462426235029) * bpow radix2 (-52) -> q6 = IZR (8896434096725391) * bpow radix2 (-57) -> q7 = IZR (-1203119726495773) * bpow radix2 (-54) -> q8 = IZR (-646930935969893) * bpow radix2 (-44) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 20 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10844138 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_20_num : IZR 620235 * bpow radix2 (-21) <= atan (IZR 20 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_20 t : Rabs t <= 0.0078126 -> IZR 620235 * bpow radix2 (-21) <= atan (IZR 20 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_20_num). apply atan_le. lra.
Qed.

Lemma approx_21 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2855784344016773) * bpow radix2 (-53) -> r1 = IZR (-3073075376216541) * bpow radix2 (-107) -> rH = IZR (8131692340184947) * bpow radix2 (-53) -> rL = IZR (-5189512640928577) * bpow radix2 (-107) -> q0 = IZR (-2408859269386945) * bpow radix2 (-53) -> q1 = IZR (-5982627108419169) * bpow radix2 (-55) -> q2 = IZR (7007791797738207) * bpow radix2 (-55) -> q3 = IZR (-2586033764512605) * bpow radix2 (-60) -> q4 = IZR (-2088932883041643) * bpow radix2 (-54) -> q5 = IZR (8694916824546489) * bpow radix2 (-57) -> q6 = IZR (7883934901389715) * bpow radix2 (-57) -> q7 = IZR (-4836331643590271) * bpow radix2 (-56) -> q8 = IZR (-7652058164418691) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 21 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16036929 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_21_num : IZR 650087 * bpow radix2 (-21) <= atan (IZR 21 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_21 t : Rabs t <= 0.0078126 -> IZR 650087 * bpow radix2 (-21) <= atan (IZR 21 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_21_num). apply atan_le. lra.
Qed.

Lemma approx_22 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2982248335337125) * bpow radix2 (-53) -> r1 = IZR (-2580769616961601) * bpow radix2 (-108) -> rH = IZR (8055346757078407) * bpow radix2 (-53) -> rL = IZR (-407093940116023) * bpow radix2 (-104) -> q0 = IZR (-619100886133537) * bpow radix2 (-51) -> q1 = IZR (-1386287886039071) * bpow radix2 (-53) -> q2 = IZR (6986475523796789) * bpow radix2 (-55) -> q3 = IZR (-1843989191660965) * bpow radix2 (-57) -> q4 = IZR (-3929253790802219) * bpow radix2 (-55) -> q5 = IZR (4730484166933267) * bpow radix2 (-56) -> q6 = IZR (3236642943021219) * bpow radix2 (-56) -> q7 = IZR (-4759898096445231) * bpow radix2 (-56) -> q8 = IZR (-7260141835146259) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 22 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15217794 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_22_num : IZR 679669 * bpow radix2 (-21) <= atan (IZR 22 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_22 t : Rabs t <= 0.0078126 -> IZR 679669 * bpow radix2 (-21) <= atan (IZR 22 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_22_num). apply atan_le. lra.
Qed.

Lemma approx_23 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3107503353423857) * bpow radix2 (-53) -> r1 = IZR (-29078389616927) * bpow radix2 (-100) -> rH = IZR (7976970410252779) * bpow radix2 (-53) -> rL = IZR (2781033629355705) * bpow radix2 (-108) -> q0 = IZR (-5077665056818201) * bpow radix2 (-54) -> q1 = IZR (-638739635067481) * bpow radix2 (-52) -> q2 = IZR (1734097999226759) * bpow radix2 (-53) -> q3 = IZR (-1633927876525819) * bpow radix2 (-56) -> q4 = IZR (-7323951815864959) * bpow radix2 (-56) -> q5 = IZR (5029607247199689) * bpow radix2 (-56) -> q6 = IZR (6327169748409017) * bpow radix2 (-58) -> q7 = IZR (-2318151742174125) * bpow radix2 (-55) -> q8 = IZR (6850960756819683) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 23 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14352560 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_23_num : IZR 708974 * bpow radix2 (-21) <= atan (IZR 23 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_23 t : Rabs t <= 0.0078126 -> IZR 708974 * bpow radix2 (-21) <= atan (IZR 23 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_23_num). apply atan_le. lra.
Qed.

Lemma approx_24 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6463037827768049) * bpow radix2 (-54) -> r1 = IZR (-998860627303715) * bpow radix2 (-105) -> rH = IZR (246772582321671) * bpow radix2 (-48) -> rL = IZR (246772582321671) * bpow radix2 (-102) -> q0 = IZR (-1298091391938653) * bpow radix2 (-52) -> q1 = IZR (-4678661211736271) * bpow radix2 (-55) -> q2 = IZR (6859495889840357) * bpow radix2 (-55) -> q3 = IZR (-4588715158483875) * bpow radix2 (-57) -> q4 = IZR (-845152898014713) * bpow radix2 (-53) -> q5 = IZR (2623706505387263) * bpow radix2 (-55) -> q6 = IZR (5642481600487947) * bpow radix2 (-58) -> q7 = IZR (-8861351132807291) * bpow radix2 (-57) -> q8 = IZR (7408523509139957) * bpow radix2 (-52) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 24 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15317172 * bpow radix2 (-98)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_24_num : IZR 737994 * bpow radix2 (-21) <= atan (IZR 24 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_24 t : Rabs t <= 0.0078126 -> IZR 737994 * bpow radix2 (-21) <= atan (IZR 24 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_24_num). apply atan_le. lra.
Qed.

Lemma approx_25 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6708534022747127) * bpow radix2 (-54) -> r1 = IZR (3182279481725517) * bpow radix2 (-107) -> rH = IZR (7814761310616205) * bpow radix2 (-53) -> rL = IZR (-8745816857388839) * bpow radix2 (-109) -> q0 = IZR (-2648510505610237) * bpow radix2 (-53) -> q1 = IZR (-8505991720611995) * bpow radix2 (-56) -> q2 = IZR (6757845398777691) * bpow radix2 (-55) -> q3 = IZR (-5802094127488669) * bpow radix2 (-57) -> q4 = IZR (-193092242444363) * bpow radix2 (-51) -> q5 = IZR (2693872762797419) * bpow radix2 (-55) -> q6 = IZR (1336167297970227) * bpow radix2 (-56) -> q7 = IZR (-8243868174858839) * bpow radix2 (-57) -> q8 = IZR (-907817553530397) * bpow radix2 (-44) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 25 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15227411 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_25_num : IZR 766722 * bpow radix2 (-21) <= atan (IZR 25 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_25 t : Rabs t <= 0.0078126 -> IZR 766722 * bpow radix2 (-21) <= atan (IZR 25 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_25_num). apply atan_le. lra.
Qed.

Lemma approx_26 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6951444184439589) * bpow radix2 (-54) -> r1 = IZR (964965140697589) * bpow radix2 (-105) -> rH = IZR (966405284666259) * bpow radix2 (-50) -> rL = IZR (-664403633208053) * bpow radix2 (-106) -> q0 = IZR (-5391780029118709) * bpow radix2 (-54) -> q1 = IZR (-1917200954322005) * bpow radix2 (-54) -> q2 = IZR (3316785222468131) * bpow radix2 (-54) -> q3 = IZR (-3452553152482011) * bpow radix2 (-56) -> q4 = IZR (-87270331773621) * bpow radix2 (-50) -> q5 = IZR (5455500829226657) * bpow radix2 (-56) -> q6 = IZR (8357210590262413) * bpow radix2 (-61) -> q7 = IZR (-7594624232188771) * bpow radix2 (-57) -> q8 = IZR (5112205657473649) * bpow radix2 (-53) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 26 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10137939 * bpow radix2 (-99)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_26_num : IZR 795152 * bpow radix2 (-21) <= atan (IZR 26 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_26 t : Rabs t <= 0.0078126 -> IZR 795152 * bpow radix2 (-21) <= atan (IZR 26 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_26_num). apply atan_le. lra.
Qed.

Lemma approx_27 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (898965254548835) * bpow radix2 (-51) -> r1 = IZR (7290627678866039) * bpow radix2 (-108) -> rH = IZR (3823159393514933) * bpow radix2 (-52) -> rL = IZR (-813914792760015) * bpow radix2 (-107) -> q0 = IZR (-1369206099895089) * bpow radix2 (-52) -> q1 = IZR (-1712112832708065) * bpow radix2 (-54) -> q2 = IZR (6488842625048553) * bpow radix2 (-55) -> q3 = IZR (-3948176204883101) * bpow radix2 (-56) -> q4 = IZR (-2493993216881061) * bpow radix2 (-55) -> q5 = IZR (5456383927407223) * bpow radix2 (-56) -> q6 = IZR (-5087492116083681) * bpow radix2 (-64) -> q7 = IZR (-3458458616360705) * bpow radix2 (-56) -> q8 = IZR (-795541399259437) * bpow radix2 (-45) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 27 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13354619 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_27_num : IZR 823278 * bpow radix2 (-21) <= atan (IZR 27 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_27 t : Rabs t <= 0.0078126 -> IZR 823278 * bpow radix2 (-21) <= atan (IZR 27 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_27_num). apply atan_le. lra.
Qed.

Lemma approx_28 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (7429326044406781) * bpow radix2 (-54) -> r1 = IZR (-5152226046687231) * bpow radix2 (-108) -> rH = IZR (3780070506907695) * bpow radix2 (-52) -> rL = IZR (3780070506907695) * bpow radix2 (-112) -> q0 = IZR (-5552365859326713) * bpow radix2 (-54) -> q1 = IZR (-3023677145563087) * bpow radix2 (-55) -> q2 = IZR (790730910035853) * bpow radix2 (-52) -> q3 = IZR (-4387901790488431) * bpow radix2 (-56) -> q4 = IZR (-8787887707757059) * bpow radix2 (-57) -> q5 = IZR (5396699825714501) * bpow radix2 (-56) -> q6 = IZR (-639320468011779) * bpow radix2 (-57) -> q7 = IZR (-3075987586214209) * bpow radix2 (-56) -> q8 = IZR (-5433639501116469) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 28 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11390225 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_28_num : IZR 851095 * bpow radix2 (-21) <= atan (IZR 28 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_28 t : Rabs t <= 0.0078126 -> IZR 851095 * bpow radix2 (-21) <= atan (IZR 28 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_28_num). apply atan_le. lra.
Qed.

Lemma approx_29 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1916054828324635) * bpow radix2 (-52) -> r1 = IZR (118223786158401) * bpow radix2 (-102) -> rH = IZR (1868213902542997) * bpow radix2 (-51) -> rL = IZR (-5560855444288139) * bpow radix2 (-107) -> q0 = IZR (-175582590800071) * bpow radix2 (-49) -> q1 = IZR (-5267660043842457) * bpow radix2 (-56) -> q2 = IZR (3073378987415369) * bpow radix2 (-54) -> q3 = IZR (-4772336163764373) * bpow radix2 (-56) -> q4 = IZR (-7618793713356627) * bpow radix2 (-57) -> q5 = IZR (5283154439110605) * bpow radix2 (-56) -> q6 = IZR (-5760520606679521) * bpow radix2 (-58) -> q7 = IZR (-5268393089322895) * bpow radix2 (-57) -> q8 = IZR (4777922186621111) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 29 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9829017 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_29_num : IZR 878598 * bpow radix2 (-21) <= atan (IZR 29 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_29 t : Rabs t <= 0.0078126 -> IZR 878598 * bpow radix2 (-21) <= atan (IZR 29 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_29_num). apply atan_le. lra.
Qed.

Lemma approx_30 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (493523091909791) * bpow radix2 (-50) -> r1 = IZR (-2023597936005901) * bpow radix2 (-106) -> rH = IZR (923075664216851) * bpow radix2 (-50) -> rL = IZR (8884603268087191) * bpow radix2 (-107) -> q0 = IZR (-5675917615040365) * bpow radix2 (-54) -> q1 = IZR (-4511246182707645) * bpow radix2 (-56) -> q2 = IZR (1488428395408071) * bpow radix2 (-53) -> q3 = IZR (-318914852226441) * bpow radix2 (-52) -> q4 = IZR (-3239935669922181) * bpow radix2 (-56) -> q5 = IZR (5122681172489107) * bpow radix2 (-56) -> q6 = IZR (-3390570345496317) * bpow radix2 (-57) -> q7 = IZR (-2277296439480859) * bpow radix2 (-56) -> q8 = IZR (3451703339069841) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 30 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14425111 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_30_num : IZR 905784 * bpow radix2 (-21) <= atan (IZR 30 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_30 t : Rabs t <= 0.0078126 -> IZR 905784 * bpow radix2 (-21) <= atan (IZR 30 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_30_num). apply atan_le. lra.
Qed.

Lemma approx_31 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (8125748538512209) * bpow radix2 (-54) -> r1 = IZR (-7367802790408621) * bpow radix2 (-108) -> rH = IZR (1823882150851251) * bpow radix2 (-51) -> rL = IZR (-7110290572459173) * bpow radix2 (-107) -> q0 = IZR (-5724472513013853) * bpow radix2 (-54) -> q1 = IZR (-7559452352944883) * bpow radix2 (-57) -> q2 = IZR (2874399047264529) * bpow radix2 (-54) -> q3 = IZR (-5380445776367535) * bpow radix2 (-56) -> q4 = IZR (-5380572752810803) * bpow radix2 (-57) -> q5 = IZR (4922223630145143) * bpow radix2 (-56) -> q6 = IZR (-3350011511939673) * bpow radix2 (-57) -> q7 = IZR (-7537874579384055) * bpow radix2 (-58) -> q8 = IZR (-1986677716946009) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 31 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16730336 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_31_num : IZR 932649 * bpow radix2 (-21) <= atan (IZR 31 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_31 t : Rabs t <= 0.0078126 -> IZR 932649 * bpow radix2 (-21) <= atan (IZR 31 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_31_num). apply atan_le. lra.
Qed.

Lemma approx_32 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (8352332796509007) * bpow radix2 (-54) -> r1 = IZR (3683087214424817) * bpow radix2 (-107) -> rH = IZR (3602879701896397) * bpow radix2 (-52) -> rL = IZR (-3602879701896397) * bpow radix2 (-106) -> q0 = IZR (-5764607523034235) * bpow radix2 (-54) -> q1 = IZR (-6148914691236517) * bpow radix2 (-57) -> q2 = IZR (5534023222165295) * bpow radix2 (-55) -> q3 = IZR (-2803905099208917) * bpow radix2 (-55) -> q4 = IZR (-8657696624647703) * bpow radix2 (-58) -> q5 = IZR (2344317790266149) * bpow radix2 (-55) -> q6 = IZR (-7393138750766963) * bpow radix2 (-58) -> q7 = IZR (-3018913302485285) * bpow radix2 (-57) -> q8 = IZR (-7667738632846753) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 32 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16106542 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_32_num : IZR 959190 * bpow radix2 (-21) <= atan (IZR 32 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_32 t : Rabs t <= 0.0078126 -> IZR 959190 * bpow radix2 (-21) <= atan (IZR 32 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_32_num). apply atan_le. lra.
Qed.

Lemma approx_33 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2144025658644109) * bpow radix2 (-52) -> r1 = IZR (4755653033669685) * bpow radix2 (-108) -> rH = IZR (1778856709133033) * bpow radix2 (-51) -> rL = IZR (-8255006915820481) * bpow radix2 (-108) -> q0 = IZR (-5796637021699465) * bpow radix2 (-54) -> q1 = IZR (-4793101683345109) * bpow radix2 (-57) -> q2 = IZR (5311313746328417) * bpow radix2 (-55) -> q3 = IZR (-5787120438528409) * bpow radix2 (-56) -> q4 = IZR (-6662498974432421) * bpow radix2 (-58) -> q5 = IZR (4428528435466205) * bpow radix2 (-56) -> q6 = IZR (-3721093674278759) * bpow radix2 (-57) -> q7 = IZR (-4578702448844611) * bpow radix2 (-58) -> q8 = IZR (-2197858101003017) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 33 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9220836 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_33_num : IZR 985404 * bpow radix2 (-21) <= atan (IZR 33 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_33 t : Rabs t <= 0.0078126 -> IZR 985404 * bpow radix2 (-21) <= atan (IZR 33 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_33_num). apply atan_le. lra.
Qed.

Lemma approx_34 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1099630300004995) * bpow radix2 (-51) -> r1 = IZR (-7381652317153827) * bpow radix2 (-109) -> rH = IZR (7024655016644917) * bpow radix2 (-53) -> rL = IZR (-5844732494317841) * bpow radix2 (-108) -> q0 = IZR (-5820887020647121) * bpow radix2 (-54) -> q1 = IZR (-6987533149167423) * bpow radix2 (-58) -> q2 = IZR (5082495575409119) * bpow radix2 (-55) -> q3 = IZR (-2960519118719919) * bpow radix2 (-55) -> q4 = IZR (-4785714675494981) * bpow radix2 (-58) -> q5 = IZR (8296357785766811) * bpow radix2 (-57) -> q6 = IZR (-8018989994838369) * bpow radix2 (-58) -> q7 = IZR (-6536169415181149) * bpow radix2 (-59) -> q8 = IZR (-8613675049484091) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 34 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9034108 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_34_num : IZR 1011290 * bpow radix2 (-21) <= atan (IZR 34 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_34 t : Rabs t <= 0.0078126 -> IZR 1011290 * bpow radix2 (-21) <= atan (IZR 34 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_34_num). apply atan_le. lra.
Qed.

Lemma approx_35 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1126892529805571) * bpow radix2 (-51) -> r1 = IZR (-7655664478967187) * bpow radix2 (-107) -> rH = IZR (6933562891828435) * bpow radix2 (-53) -> rL = IZR (2021160667198035) * bpow radix2 (-107) -> q0 = IZR (-729711561628251) * bpow radix2 (-51) -> q1 = IZR (-4504438987504111) * bpow radix2 (-58) -> q2 = IZR (4849286379602573) * bpow radix2 (-55) -> q3 = IZR (-1503108318712293) * bpow radix2 (-54) -> q4 = IZR (-3034853543951981) * bpow radix2 (-58) -> q5 = IZR (7706877603771653) * bpow radix2 (-57) -> q6 = IZR (-5112489470836329) * bpow radix2 (-57) -> q7 = IZR (-4073639017193319) * bpow radix2 (-59) -> q8 = IZR (4428542440416261) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 35 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9265605 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_35_num : IZR 1036845 * bpow radix2 (-21) <= atan (IZR 35 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_35 t : Rabs t <= 0.0078126 -> IZR 1036845 * bpow radix2 (-21) <= atan (IZR 35 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_35_num). apply atan_le. lra.
Qed.

Lemma approx_36 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (288449622815501) * bpow radix2 (-49) -> r1 = IZR (-4131572507845875) * bpow radix2 (-107) -> rH = IZR (1710566030573957) * bpow radix2 (-51) -> rL = IZR (-4490235830256637) * bpow radix2 (-107) -> q0 = IZR (-5847394858223141) * bpow radix2 (-54) -> q1 = IZR (-8554843428142263) * bpow radix2 (-60) -> q2 = IZR (4613288655488437) * bpow radix2 (-55) -> q3 = IZR (-6064323191286957) * bpow radix2 (-56) -> q4 = IZR (-5661154166475689) * bpow radix2 (-60) -> q5 = IZR (1774842144659339) * bpow radix2 (-55) -> q6 = IZR (-8143642725898769) * bpow radix2 (-58) -> q7 = IZR (-7478171908968949) * bpow radix2 (-61) -> q8 = IZR (-5925552829856813) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 36 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12425053 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_36_num : IZR 531034 * bpow radix2 (-20) <= atan (IZR 36 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_36 t : Rabs t <= 0.0078126 -> IZR 531034 * bpow radix2 (-20) <= atan (IZR 36 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_36_num). apply atan_le. lra.
Qed.

Lemma approx_37 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2360695180861933) * bpow radix2 (-52) -> r1 = IZR (7165491839057999) * bpow radix2 (-110) -> rH = IZR (1687716749653207) * bpow radix2 (-51) -> rL = IZR (-5893823336679559) * bpow radix2 (-107) -> q0 = IZR (-5850339635028427) * bpow radix2 (-54) -> q1 = IZR (6952492835708733) * bpow radix2 (-64) -> q2 = IZR (8751970073840769) * bpow radix2 (-56) -> q3 = IZR (-6079818507953281) * bpow radix2 (-56) -> q4 = IZR (4507130101438497) * bpow radix2 (-64) -> q5 = IZR (6483541365042885) * bpow radix2 (-57) -> q6 = IZR (-4237171188045039) * bpow radix2 (-57) -> q7 = IZR (1437481205722437) * bpow radix2 (-63) -> q8 = IZR (-4967534171440961) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 37 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10416515 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_37_num : IZR 543480 * bpow radix2 (-20) <= atan (IZR 37 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_37 t : Rabs t <= 0.0078126 -> IZR 543480 * bpow radix2 (-20) <= atan (IZR 37 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_37_num). apply atan_le. lra.
Qed.

Lemma approx_38 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4826158583239337) * bpow radix2 (-53) -> r1 = IZR (-5275108390268469) * bpow radix2 (-110) -> rH = IZR (6659474394840993) * bpow radix2 (-53) -> rL = IZR (6542413321494179) * bpow radix2 (-107) -> q0 = IZR (-730859283765943) * bpow radix2 (-51) -> q1 = IZR (559320976477335) * bpow radix2 (-56) -> q2 = IZR (8277471317776061) * bpow radix2 (-56) -> q3 = IZR (-3031036428003845) * bpow radix2 (-55) -> q4 = IZR (5685145852983205) * bpow radix2 (-60) -> q5 = IZR (2934012244146397) * bpow radix2 (-56) -> q6 = IZR (-509042573933859) * bpow radix2 (-54) -> q7 = IZR (3598239205639151) * bpow radix2 (-60) -> q8 = IZR (-5897746217380899) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 38 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12365232 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_38_num : IZR 555760 * bpow radix2 (-20) <= atan (IZR 38 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_38 t : Rabs t <= 0.0078126 -> IZR 555760 * bpow radix2 (-20) <= atan (IZR 38 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_38_num). apply atan_le. lra.
Qed.

Lemma approx_39 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4929499468561427) * bpow radix2 (-53) -> r1 = IZR (7989175705977601) * bpow radix2 (-107) -> rH = IZR (3284091877106917) * bpow radix2 (-52) -> rL = IZR (-3761952902193763) * bpow radix2 (-106) -> q0 = IZR (-5837346145813683) * bpow radix2 (-54) -> q1 = IZR (8495168439207807) * bpow radix2 (-59) -> q2 = IZR (487847169275227) * bpow radix2 (-52) -> q3 = IZR (-1503559686127293) * bpow radix2 (-54) -> q4 = IZR (5276633738839465) * bpow radix2 (-59) -> q5 = IZR (5260349862807499) * bpow radix2 (-57) -> q6 = IZR (-4744789663640323) * bpow radix2 (-57) -> q7 = IZR (6537209214242657) * bpow radix2 (-60) -> q8 = IZR (-953343060868799) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 39 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16054169 * bpow radix2 (-97)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_39_num : IZR 567873 * bpow radix2 (-20) <= atan (IZR 39 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_39 t : Rabs t <= 0.0078126 -> IZR 567873 * bpow radix2 (-20) <= atan (IZR 39 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_39_num). apply atan_le. lra.
Qed.

Lemma approx_40 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1257853834215341) * bpow radix2 (-51) -> r1 = IZR (-7081813339694735) * bpow radix2 (-110) -> rH = IZR (404817944033303) * bpow radix2 (-49) -> rL = IZR (404817944033303) * bpow radix2 (-104) -> q0 = IZR (-2911050384059707) * bpow radix2 (-53) -> q1 = IZR (383778927037085) * bpow radix2 (-54) -> q2 = IZR (1834612235458035) * bpow radix2 (-54) -> q3 = IZR (-2969714468968177) * bpow radix2 (-55) -> q4 = IZR (7447658995577753) * bpow radix2 (-59) -> q5 = IZR (4666967038120577) * bpow radix2 (-57) -> q6 = IZR (-1221720184244365) * bpow radix2 (-55) -> q7 = IZR (2239608164166231) * bpow radix2 (-58) -> q8 = IZR (3019358535788795) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 40 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12640955 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_40_num : IZR 579821 * bpow radix2 (-20) <= atan (IZR 40 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_40 t : Rabs t <= 0.0078126 -> IZR 579821 * bpow radix2 (-20) <= atan (IZR 40 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_40_num). apply atan_le. lra.
Qed.

Lemma approx_41 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2565954951597877) * bpow radix2 (-52) -> r1 = IZR (3976995022836007) * bpow radix2 (-108) -> rH = IZR (6386271100470677) * bpow radix2 (-53) -> rL = IZR (3434803524008033) * bpow radix2 (-106) -> q0 = IZR (-5801480134199431) * bpow radix2 (-54) -> q1 = IZR (7917375923837233) * bpow radix2 (-58) -> q2 = IZR (6878142175618719) * bpow radix2 (-56) -> q3 = IZR (-2920341689377327) * bpow radix2 (-55) -> q4 = IZR (4681630843285057) * bpow radix2 (-58) -> q5 = IZR (4093275074875525) * bpow radix2 (-57) -> q6 = IZR (-5281914005588973) * bpow radix2 (-57) -> q7 = IZR (2738973266020311) * bpow radix2 (-58) -> q8 = IZR (2786498339006241) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 41 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11676517 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_41_num : IZR 591602 * bpow radix2 (-20) <= atan (IZR 41 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_41 t : Rabs t <= 0.0078126 -> IZR 591602 * bpow radix2 (-20) <= atan (IZR 41 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_41_num). apply atan_le. lra.
Qed.

Lemma approx_42 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5230988195040817) * bpow radix2 (-53) -> r1 = IZR (-4677819351613575) * bpow radix2 (-108) -> rH = IZR (1573954272500815) * bpow radix2 (-51) -> rL = IZR (-4525118533439843) * bpow radix2 (-109) -> q0 = IZR (-5775821275743605) * bpow radix2 (-54) -> q1 = IZR (4790123665751325) * bpow radix2 (-57) -> q2 = IZR (3213194418142491) * bpow radix2 (-55) -> q3 = IZR (-5720941479141221) * bpow radix2 (-56) -> q4 = IZR (344773820477665) * bpow radix2 (-54) -> q5 = IZR (7087356645010595) * bpow radix2 (-58) -> q6 = IZR (-8675153754544911) * bpow radix2 (-58) -> q7 = IZR (3124767869098841) * bpow radix2 (-58) -> q8 = IZR (5367896419992839) * bpow radix2 (-51) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 42 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11213689 * bpow radix2 (-97)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_42_num : IZR 603219 * bpow radix2 (-20) <= atan (IZR 42 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_42 t : Rabs t <= 0.0078126 -> IZR 603219 * bpow radix2 (-20) <= atan (IZR 42 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_42_num). apply atan_le. lra.
Qed.

Lemma approx_43 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2664328235017701) * bpow radix2 (-52) -> r1 = IZR (7983960339566477) * bpow radix2 (-107) -> rH = IZR (775725150282151) * bpow radix2 (-50) -> rL = IZR (5066454887780299) * bpow radix2 (-107) -> q0 = IZR (-5745454973460669) * bpow radix2 (-54) -> q1 = IZR (2782852794833527) * bpow radix2 (-56) -> q2 = IZR (2992359193270437) * bpow radix2 (-55) -> q3 = IZR (-2791509758311451) * bpow radix2 (-55) -> q4 = IZR (3116916035350447) * bpow radix2 (-57) -> q5 = IZR (6043292466209347) * bpow radix2 (-58) -> q6 = IZR (-5976981787885793) * bpow radix2 (-58) -> q7 = IZR (6897504421173529) * bpow radix2 (-59) -> q8 = IZR (-237741604862667) * bpow radix2 (-42) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 43 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15945278 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_43_num : IZR 614671 * bpow radix2 (-20) <= atan (IZR 43 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_43 t : Rabs t <= 0.0078126 -> IZR 614671 * bpow radix2 (-20) <= atan (IZR 43 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_43_num). apply atan_le. lra.
Qed.

Lemma approx_44 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5424922135246779) * bpow radix2 (-53) -> r1 = IZR (2393673788786817) * bpow radix2 (-106) -> rH = IZR (6116294454147729) * bpow radix2 (-53) -> rL = IZR (5686242500340467) * bpow radix2 (-107) -> q0 = IZR (-356919039764589) * bpow radix2 (-50) -> q1 = IZR (3143389225056385) * bpow radix2 (-56) -> q2 = IZR (5554445672279183) * bpow radix2 (-56) -> q3 = IZR (-5429592801591725) * bpow radix2 (-56) -> q4 = IZR (6840479409890417) * bpow radix2 (-58) -> q5 = IZR (5059596498737373) * bpow radix2 (-58) -> q6 = IZR (-6077728306568013) * bpow radix2 (-58) -> q7 = IZR (3645068698396973) * bpow radix2 (-58) -> q8 = IZR (-2736780305404849) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 44 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11472105 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_44_num : IZR 625959 * bpow radix2 (-20) <= atan (IZR 44 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_44 t : Rabs t <= 0.0078126 -> IZR 625959 * bpow radix2 (-20) <= atan (IZR 44 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_44_num). apply atan_le. lra.
Qed.

Lemma approx_45 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2759896834116493) * bpow radix2 (-52) -> r1 = IZR (-2559807369011107) * bpow radix2 (-106) -> rH = IZR (6027362873291799) * bpow radix2 (-53) -> rL = IZR (285659623480901) * bpow radix2 (-103) -> q0 = IZR (-44311604198355) * bpow radix2 (-47) -> q1 = IZR (6954838502954825) * bpow radix2 (-57) -> q2 = IZR (2568341244587069) * bpow radix2 (-55) -> q3 = IZR (-5263182235488377) * bpow radix2 (-56) -> q4 = IZR (7343102366755073) * bpow radix2 (-58) -> q5 = IZR (8279875258256983) * bpow radix2 (-59) -> q6 = IZR (-8169307651020941) * bpow radix2 (-58) -> q7 = IZR (7583654290696219) * bpow radix2 (-59) -> q8 = IZR (3823066227029299) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 45 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16022867 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_45_num : IZR 637085 * bpow radix2 (-20) <= atan (IZR 45 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_45 t : Rabs t <= 0.0078126 -> IZR 637085 * bpow radix2 (-20) <= atan (IZR 45 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_45_num). apply atan_le. lra.
Qed.

Lemma approx_46 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1403320135034301) * bpow radix2 (-51) -> r1 = IZR (542027902248015) * bpow radix2 (-104) -> rH = IZR (5939067634806681) * bpow radix2 (-53) -> rL = IZR (2493944416959837) * bpow radix2 (-107) -> q0 = IZR (-1407325749909117) * bpow radix2 (-52) -> q1 = IZR (1892877233245623) * bpow radix2 (-55) -> q2 = IZR (295771877511113) * bpow radix2 (-52) -> q3 = IZR (-1271536212403493) * bpow radix2 (-54) -> q4 = IZR (7748559052467941) * bpow radix2 (-58) -> q5 = IZR (1643308086575517) * bpow radix2 (-57) -> q6 = IZR (-3034947253550369) * bpow radix2 (-57) -> q7 = IZR (7633834445944817) * bpow radix2 (-59) -> q8 = IZR (-216775008803303) * bpow radix2 (-44) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 46 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14538222 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_46_num : IZR 648049 * bpow radix2 (-20) <= atan (IZR 46 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_46 t : Rabs t <= 0.0078126 -> IZR 648049 * bpow radix2 (-20) <= atan (IZR 46 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_46_num). apply atan_le. lra.
Qed.

Lemma approx_47 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2852696570506667) * bpow radix2 (-52) -> r1 = IZR (-1107045047070521) * bpow radix2 (-105) -> rH = IZR (5851465209741333) * bpow radix2 (-53) -> rL = IZR (-7617190551352731) * bpow radix2 (-108) -> q0 = IZR (-697906714944565) * bpow radix2 (-51) -> q1 = IZR (4069258420407729) * bpow radix2 (-56) -> q2 = IZR (8684383974053163) * bpow radix2 (-57) -> q3 = IZR (-4900667896697289) * bpow radix2 (-56) -> q4 = IZR (4032220387557805) * bpow radix2 (-57) -> q5 = IZR (5001378802156627) * bpow radix2 (-59) -> q6 = IZR (-5628594514241257) * bpow radix2 (-58) -> q7 = IZR (7714426666903937) * bpow radix2 (-59) -> q8 = IZR (-1381315358198893) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 47 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11578571 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_47_num : IZR 658852 * bpow radix2 (-20) <= atan (IZR 47 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_47 t : Rabs t <= 0.0078126 -> IZR 658852 * bpow radix2 (-20) <= atan (IZR 47 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_47_num). apply atan_le. lra.
Qed.

Lemma approx_48 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5796142707547873) * bpow radix2 (-53) -> r1 = IZR (642335192798347) * bpow radix2 (-105) -> rH = IZR (5764607523034235) * bpow radix2 (-53) -> rL = IZR (-1080863910568919) * bpow radix2 (-106) -> q0 = IZR (-5534023222112865) * bpow radix2 (-54) -> q1 = IZR (1082208985657627) * bpow radix2 (-54) -> q2 = IZR (7933575690373767) * bpow radix2 (-57) -> q3 = IZR (-4708766067387939) * bpow radix2 (-56) -> q4 = IZR (2074541692033757) * bpow radix2 (-56) -> q5 = IZR (3564380599619171) * bpow radix2 (-59) -> q6 = IZR (-1915835285462679) * bpow radix2 (-56) -> q7 = IZR (7599180013937521) * bpow radix2 (-59) -> q8 = IZR (970273959659403) * bpow radix2 (-44) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 48 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16267606 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_48_num : IZR 669496 * bpow radix2 (-20) <= atan (IZR 48 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_48 t : Rabs t <= 0.0078126 -> IZR 669496 * bpow radix2 (-20) <= atan (IZR 48 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_48_num). apply atan_le. lra.
Qed.

Lemma approx_49 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1471385313327873) * bpow radix2 (-51) -> r1 = IZR (1452246280494683) * bpow radix2 (-105) -> rH = IZR (5678542119042497) * bpow radix2 (-53) -> rL = IZR (4946542549009675) * bpow radix2 (-110) -> q0 = IZR (-5481886435375487) * bpow radix2 (-54) -> q1 = IZR (4565423304325889) * bpow radix2 (-56) -> q2 = IZR (1803283242495351) * bpow radix2 (-55) -> q3 = IZR (-4512281408205493) * bpow radix2 (-56) -> q4 = IZR (4228407446179617) * bpow radix2 (-57) -> q5 = IZR (1130232226538717) * bpow radix2 (-58) -> q6 = IZR (-3294681340475809) * bpow radix2 (-57) -> q7 = IZR (7475232200825229) * bpow radix2 (-59) -> q8 = IZR (2908251418782171) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 49 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12190212 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_49_num : IZR 679982 * bpow radix2 (-20) <= atan (IZR 49 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_49 t : Rabs t <= 0.0078126 -> IZR 679982 * bpow radix2 (-20) <= atan (IZR 49 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_49_num). apply atan_le. lra.
Qed.

Lemma approx_50 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5973601501644319) * bpow radix2 (-53) -> r1 = IZR (-1247796094473347) * bpow radix2 (-105) -> rH = IZR (1398328083210245) * bpow radix2 (-51) -> rL = IZR (-289497610977121) * bpow radix2 (-104) -> q0 = IZR (-1356776793897145) * bpow radix2 (-52) -> q1 = IZR (1194994805786361) * bpow radix2 (-54) -> q2 = IZR (3261819544195039) * bpow radix2 (-56) -> q3 = IZR (-539110692148819) * bpow radix2 (-53) -> q4 = IZR (8547595698387151) * bpow radix2 (-58) -> q5 = IZR (8691274806480263) * bpow radix2 (-62) -> q6 = IZR (-341669665657215) * bpow radix2 (-55) -> q7 = IZR (3579529746466387) * bpow radix2 (-58) -> q8 = IZR (-3038013475173807) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 50 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12732299 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_50_num : IZR 690311 * bpow radix2 (-20) <= atan (IZR 50 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_50 t : Rabs t <= 0.0078126 -> IZR 690311 * bpow radix2 (-20) <= atan (IZR 50 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_50_num). apply atan_le. lra.
Qed.

Lemma approx_51 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6060336821252027) * bpow radix2 (-53) -> r1 = IZR (-385226849933973) * bpow radix2 (-104) -> rH = IZR (688619683205523) * bpow radix2 (-50) -> rL = IZR (4013361591182189) * bpow radix2 (-106) -> q0 = IZR (-2684968966382353) * bpow radix2 (-53) -> q1 = IZR (4973476699341763) * bpow radix2 (-56) -> q2 = IZR (5865429184784175) * bpow radix2 (-57) -> q3 = IZR (-8224167544656023) * bpow radix2 (-57) -> q4 = IZR (1072231494973869) * bpow radix2 (-55) -> q5 = IZR (2414586273186287) * bpow radix2 (-65) -> q6 = IZR (-7873084848312895) * bpow radix2 (-59) -> q7 = IZR (6918327659366737) * bpow radix2 (-59) -> q8 = IZR (-3292311223734987) * bpow radix2 (-53) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 51 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13683936 * bpow radix2 (-100)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_51_num : IZR 700485 * bpow radix2 (-20) <= atan (IZR 51 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_51 t : Rabs t <= 0.0078126 -> IZR 700485 * bpow radix2 (-20) <= atan (IZR 51 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_51_num). apply atan_le. lra.
Qed.

Lemma approx_52 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (768220145570659) * bpow radix2 (-50) -> r1 = IZR (2253204903621605) * bpow radix2 (-108) -> rH = IZR (2712756481427875) * bpow radix2 (-52) -> rL = IZR (8562137644506731) * bpow radix2 (-107) -> q0 = IZR (-2655309873585873) * bpow radix2 (-53) -> q1 = IZR (5146895663261957) * bpow radix2 (-56) -> q2 = IZR (5238615828165271) * bpow radix2 (-57) -> q3 = IZR (-7822441636681259) * bpow radix2 (-57) -> q4 = IZR (1069257584260849) * bpow radix2 (-55) -> q5 = IZR (-7127654002238925) * bpow radix2 (-62) -> q6 = IZR (-5048230466988991) * bpow radix2 (-58) -> q7 = IZR (6433231581616853) * bpow radix2 (-59) -> q8 = IZR (5565162350788601) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 52 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11663217 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_52_num : IZR 710506 * bpow radix2 (-20) <= atan (IZR 52 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_52 t : Rabs t <= 0.0078126 -> IZR 710506 * bpow radix2 (-20) <= atan (IZR 52 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_52_num). apply atan_le. lra.
Qed.

Lemma approx_53 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3114944504446407) * bpow radix2 (-52) -> r1 = IZR (-5268332329494721) * bpow radix2 (-109) -> rH = IZR (667876324174857) * bpow radix2 (-50) -> rL = IZR (3328946053309053) * bpow radix2 (-106) -> q0 = IZR (-1312345541839893) * bpow radix2 (-52) -> q1 = IZR (2650608203293385) * bpow radix2 (-55) -> q2 = IZR (4643113581740843) * bpow radix2 (-57) -> q3 = IZR (-7422975366863135) * bpow radix2 (-57) -> q4 = IZR (4241193961993313) * bpow radix2 (-57) -> q5 = IZR (-6823344078719893) * bpow radix2 (-61) -> q6 = IZR (-8415898924360067) * bpow radix2 (-61) -> q7 = IZR (6111656105948003) * bpow radix2 (-59) -> q8 = IZR (-110487388830921) * bpow radix2 (-41) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 53 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14815452 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_53_num : IZR 720375 * bpow radix2 (-20) <= atan (IZR 53 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_53 t : Rabs t <= 0.0078126 -> IZR 720375 * bpow radix2 (-20) <= atan (IZR 53 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_53_num). apply atan_le. lra.
Qed.

Lemma approx_54 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6312735300378759) * bpow radix2 (-53) -> r1 = IZR (-3225107953901021) * bpow radix2 (-107) -> rH = IZR (2630739314562115) * bpow radix2 (-52) -> rL = IZR (3175384563280053) * bpow radix2 (-106) -> q0 = IZR (-2593221640366991) * bpow radix2 (-53) -> q1 = IZR (5437413763658655) * bpow radix2 (-56) -> q2 = IZR (8157324818227897) * bpow radix2 (-58) -> q3 = IZR (-1756964767034003) * bpow radix2 (-55) -> q4 = IZR (8369320334277773) * bpow radix2 (-58) -> q5 = IZR (-2413557268014829) * bpow radix2 (-59) -> q6 = IZR (-3212029812708333) * bpow radix2 (-59) -> q7 = IZR (2890722755552297) * bpow radix2 (-58) -> q8 = IZR (-3626703077478287) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 54 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15191324 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_54_num : IZR 730094 * bpow radix2 (-20) <= atan (IZR 54 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_54 t : Rabs t <= 0.0078126 -> IZR 730094 * bpow radix2 (-20) <= atan (IZR 54 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_54_num). apply atan_le. lra.
Qed.

Lemma approx_55 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6394315400756633) * bpow radix2 (-53) -> r1 = IZR (-3729664518677127) * bpow radix2 (-106) -> rH = IZR (2590471011614879) * bpow radix2 (-52) -> rL = IZR (-2204683092404655) * bpow radix2 (-105) -> q0 = IZR (-1280502452027015) * bpow radix2 (-52) -> q1 = IZR (1389113001163849) * bpow radix2 (-54) -> q2 = IZR (3544849814781553) * bpow radix2 (-57) -> q3 = IZR (-3319454223197253) * bpow radix2 (-56) -> q4 = IZR (2055063399683967) * bpow radix2 (-56) -> q5 = IZR (-6042229856357037) * bpow radix2 (-60) -> q6 = IZR (-2898052765663245) * bpow radix2 (-60) -> q7 = IZR (5287884802235469) * bpow radix2 (-59) -> q8 = IZR (-336925577819375) * bpow radix2 (-43) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 55 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11244851 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_55_num : IZR 739664 * bpow radix2 (-20) <= atan (IZR 55 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_55 t : Rabs t <= 0.0078126 -> IZR 739664 * bpow radix2 (-20) <= atan (IZR 55 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_55_num). apply atan_le. lra.
Qed.

Lemma approx_56 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1618661259219341) * bpow radix2 (-51) -> r1 = IZR (-3485067776454523) * bpow radix2 (-107) -> rH = IZR (637677823344495) * bpow radix2 (-50) -> rL = IZR (637677823344495) * bpow radix2 (-106) -> q0 = IZR (-5056277254129801) * bpow radix2 (-54) -> q1 = IZR (5659280399059735) * bpow radix2 (-56) -> q2 = IZR (6082263185647287) * bpow radix2 (-58) -> q3 = IZR (-6257682525482809) * bpow radix2 (-57) -> q4 = IZR (251270444150211) * bpow radix2 (-53) -> q5 = IZR (-883936010651981) * bpow radix2 (-57) -> q6 = IZR (-154925292062993) * bpow radix2 (-54) -> q7 = IZR (615355225880723) * bpow radix2 (-56) -> q8 = IZR (4242324216567599) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 56 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 8866442 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_56_num : IZR 749089 * bpow radix2 (-20) <= atan (IZR 56 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_56 t : Rabs t <= 0.0078126 -> IZR 749089 * bpow radix2 (-20) <= atan (IZR 56 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_56_num). apply atan_le. lra.
Qed.

Lemma approx_57 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6553740252974607) * bpow radix2 (-53) -> r1 = IZR (6670350873560225) * bpow radix2 (-111) -> rH = IZR (2511469581172165) * bpow radix2 (-52) -> rL = IZR (-6062844535798429) * bpow radix2 (-109) -> q0 = IZR (-77959845406025) * bpow radix2 (-48) -> q1 = IZR (2873414702847027) * bpow radix2 (-55) -> q2 = IZR (1283425584900245) * bpow radix2 (-56) -> q3 = IZR (-2942751041576119) * bpow radix2 (-56) -> q4 = IZR (3917568612317011) * bpow radix2 (-57) -> q5 = IZR (-3964688447590669) * bpow radix2 (-59) -> q6 = IZR (-7850325956591667) * bpow radix2 (-61) -> q7 = IZR (4556088360790335) * bpow radix2 (-59) -> q8 = IZR (-8148421172663551) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 57 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 8532759 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_57_num : IZR 758368 * bpow radix2 (-20) <= atan (IZR 57 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_57 t : Rabs t <= 0.0078126 -> IZR 758368 * bpow radix2 (-20) <= atan (IZR 57 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_57_num). apply atan_le. lra.
Qed.

Lemma approx_58 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3315808682809519) * bpow radix2 (-52) -> r1 = IZR (88074782900445) * bpow radix2 (-101) -> rH = IZR (2472753897280101) * bpow radix2 (-52) -> rL = IZR (-8905777708172863) * bpow radix2 (-107) -> q0 = IZR (-4921642073299589) * bpow radix2 (-54) -> q1 = IZR (2910003722190807) * bpow radix2 (-55) -> q2 = IZR (1060628741604921) * bpow radix2 (-56) -> q3 = IZR (-5523468235605677) * bpow radix2 (-57) -> q4 = IZR (237764910998749) * bpow radix2 (-53) -> q5 = IZR (-2157569637752401) * bpow radix2 (-58) -> q6 = IZR (-4969222514043155) * bpow radix2 (-59) -> q7 = IZR (2038766272625775) * bpow radix2 (-58) -> q8 = IZR (2186792260710917) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 58 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9166071 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_58_num : IZR 767505 * bpow radix2 (-20) <= atan (IZR 58 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_58 t : Rabs t <= 0.0078126 -> IZR 767505 * bpow radix2 (-20) <= atan (IZR 58 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_58_num). apply atan_le. lra.
Qed.

Lemma approx_59 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6708292921303187) * bpow radix2 (-53) -> r1 = IZR (6017086479350441) * bpow radix2 (-107) -> rH = IZR (4869141896188347) * bpow radix2 (-53) -> rL = IZR (-1181028436001739) * bpow radix2 (-105) -> q0 = IZR (-4853076362678421) * bpow radix2 (-54) -> q1 = IZR (5879698203918865) * bpow radix2 (-56) -> q2 = IZR (3407042859837839) * bpow radix2 (-58) -> q3 = IZR (-161640027717981) * bpow radix2 (-52) -> q4 = IZR (7364460258173261) * bpow radix2 (-58) -> q5 = IZR (-2297091435814071) * bpow radix2 (-58) -> q6 = IZR (-5698730589349745) * bpow radix2 (-63) -> q7 = IZR (465405117343777) * bpow radix2 (-56) -> q8 = IZR (-5721541022356329) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 59 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11987651 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_59_num : IZR 776501 * bpow radix2 (-20) <= atan (IZR 59 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_59 t : Rabs t <= 0.0078126 -> IZR 776501 * bpow radix2 (-20) <= atan (IZR 59 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_59_num). apply atan_le. lra.
Qed.

Lemma approx_60 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6783783656589901) * bpow radix2 (-53) -> r1 = IZR (-7871825351784727) * bpow radix2 (-108) -> rH = IZR (37451971953185) * bpow radix2 (-46) -> rL = IZR (-37451971953185) * bpow radix2 (-100) -> q0 = IZR (-4783885980880845) * bpow radix2 (-54) -> q1 = IZR (5926758441362935) * bpow radix2 (-56) -> q2 = IZR (1312750866824413) * bpow radix2 (-57) -> q3 = IZR (-2416628405195775) * bpow radix2 (-56) -> q4 = IZR (7107035779100169) * bpow radix2 (-58) -> q5 = IZR (-1202159481498727) * bpow radix2 (-57) -> q6 = IZR (7037624326953111) * bpow radix2 (-61) -> q7 = IZR (207176116309279) * bpow radix2 (-55) -> q8 = IZR (-44926650711967) * bpow radix2 (-40) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 60 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12050180 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_60_num : IZR 785358 * bpow radix2 (-20) <= atan (IZR 60 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_60 t : Rabs t <= 0.0078126 -> IZR 785358 * bpow radix2 (-20) <= atan (IZR 60 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_60_num). apply atan_le. lra.
Qed.

Lemma approx_61 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6858106460750533) * bpow radix2 (-53) -> r1 = IZR (6393035194153155) * bpow radix2 (-109) -> rH = IZR (1179911991410359) * bpow radix2 (-51) -> rL = IZR (-4562940904282247) * bpow radix2 (-107) -> q0 = IZR (-4714214061114025) * bpow radix2 (-54) -> q1 = IZR (5962016228531315) * bpow radix2 (-56) -> q2 = IZR (7584033889396647) * bpow radix2 (-60) -> q3 = IZR (-2253173584693165) * bpow radix2 (-56) -> q4 = IZR (6839527772339453) * bpow radix2 (-58) -> q5 = IZR (-4965076712447507) * bpow radix2 (-59) -> q6 = IZR (1276203680615483) * bpow radix2 (-58) -> q7 = IZR (5857031551486921) * bpow radix2 (-60) -> q8 = IZR (-6380410888668435) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 61 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13370265 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_61_num : IZR 794078 * bpow radix2 (-20) <= atan (IZR 61 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_61 t : Rabs t <= 0.0078126 -> IZR 794078 * bpow radix2 (-20) <= atan (IZR 61 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_61_num). apply atan_le. lra.
Qed.

Lemma approx_62 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (866409792601663) * bpow radix2 (-50) -> r1 = IZR (-6011693072611867) * bpow radix2 (-107) -> rH = IZR (580816878895137) * bpow radix2 (-50) -> rL = IZR (17583323482177) * bpow radix2 (-100) -> q0 = IZR (-580524275933477) * bpow radix2 (-51) -> q1 = IZR (5986269602965151) * bpow radix2 (-56) -> q2 = IZR (4866422712132945) * bpow radix2 (-60) -> q3 = IZR (-8384308669062711) * bpow radix2 (-58) -> q4 = IZR (6564992914809907) * bpow radix2 (-58) -> q5 = IZR (-2534876834896963) * bpow radix2 (-58) -> q6 = IZR (-3422911588050723) * bpow radix2 (-62) -> q7 = IZR (5311698167737637) * bpow radix2 (-60) -> q8 = IZR (-3109551456668981) * bpow radix2 (-50) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 62 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13016496 * bpow radix2 (-97)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_62_num : IZR 802663 * bpow radix2 (-20) <= atan (IZR 62 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_62 t : Rabs t <= 0.0078126 -> IZR 802663 * bpow radix2 (-20) <= atan (IZR 62 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_62_num). apply atan_le. lra.
Qed.

Lemma approx_63 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3501658194468911) * bpow radix2 (-52) -> r1 = IZR (-8657016260407137) * bpow radix2 (-108) -> rH = IZR (4574518059196417) * bpow radix2 (-53) -> rL = IZR (4538779636858945) * bpow radix2 (-111) -> q0 = IZR (-4573950852989449) * bpow radix2 (-54) -> q1 = IZR (6000285582323089) * bpow radix2 (-56) -> q2 = IZR (4682269302910037) * bpow radix2 (-61) -> q3 = IZR (-7781895766283237) * bpow radix2 (-58) -> q4 = IZR (3142979220819661) * bpow radix2 (-57) -> q5 = IZR (-2564272605199071) * bpow radix2 (-58) -> q6 = IZR (-8042539094998977) * bpow radix2 (-62) -> q7 = IZR (4709295987195781) * bpow radix2 (-60) -> q8 = IZR (5000908992608685) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 63 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10484480 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_63_num : IZR 811115 * bpow radix2 (-20) <= atan (IZR 63 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_63 t : Rabs t <= 0.0078126 -> IZR 811115 * bpow radix2 (-20) <= atan (IZR 63 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_63_num). apply atan_le. lra.
Qed.

Lemma approx_64 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (884279719003555) * bpow radix2 (-50) -> r1 = IZR (4967757600021511) * bpow radix2 (-107) -> rH = IZR (1) * bpow radix2 (-1) -> rL = 0 -> q0 = IZR (-1) * bpow radix2 (-2) -> q1 = IZR (6004799503160661) * bpow radix2 (-56) -> q2 = IZR (1669622273244265) * bpow radix2 (-124) -> q3 = IZR (-7205759403661701) * bpow radix2 (-58) -> q4 = IZR (6004799503160659) * bpow radix2 (-58) -> q5 = IZR (-643372296146765) * bpow radix2 (-56) -> q6 = IZR (2311434041383767) * bpow radix2 (-93) -> q7 = IZR (8256992271041247) * bpow radix2 (-61) -> q8 = IZR (-7205764053143631) * bpow radix2 (-61) -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR 64 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14883246 * bpow radix2 (-105)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_64_num : IZR 819436 * bpow radix2 (-20) <= atan (IZR 64 / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_64 t : Rabs t <= 0.0078126 -> IZR 819436 * bpow radix2 (-20) <= atan (IZR 64 / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_64_num). apply atan_le. lra.
Qed.

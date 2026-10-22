(** The table segments of asin approximate [asin]: for [k = 1..45], with the
    segment's words, [|asin (k/64 + t) - (c0 + c1 + (cH + cL) t + t^2 G(t))|] is
    within the budget of [compose_<kk>.g] for every [|t| <= 0.0078126]. Written by
    generators/asin_approx.py; do not edit.

    Each is proved by [sin] monotonicity ([asin_within]), the bounds on [sin] at
    the polynomial's two ends by [interval]; Sollya's report is not an input. *)
From Coq Require Import Reals ZArith Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinSegment AsinSeriesSmall AsinWithin.
Import ListNotations.
Open Scope R_scope.

(** The series branch: [asin z] is [z + z^3 P(z^2)], [P]'s coefficients the table
    POLY0's, to [3/16 2^-54 z^3] on [[2^-28, 0.0078126]] (the relative accuracy of
    Sollya's fit and the series' truncation, which [series_compose.g] budgets as
    [2^-54 (1 + 2^-23)] of [asin z - z >= z^3/6]). *)
Lemma approx_series z : / 2 ^ 28 <= z <= 0.0078126 ->
  Rabs (asin z - (z + z * z * z * (q0r + z * z * (q1r + z * z * (q2r + z * z * q3r)))))
    <= 3 / 16 / 2 ^ 54 * (z * z * z).
Proof.
  intros Hz. unfold q0r, q1r, q2r, q3r. bpow_num.
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect z, i_taylor z, i_prec 240, i_degree 14, i_depth 60).
Qed.

Lemma approx_01 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1125945724861011) * bpow radix2 (-56) -> r1 = IZR (4838732281543223) * bpow radix2 (-114) -> rH = IZR (1126037370967041) * bpow radix2 (-50) -> rL = IZR (6772720625608905) * bpow radix2 (-106) -> q0 = IZR (4505249398272039) * bpow radix2 (-59) -> q1 = IZR (6011399929709017) * bpow radix2 (-55) -> q2 = IZR (3381137750625937) * bpow radix2 (-59) -> q3 = IZR (2710414339854473) * bpow radix2 (-55) -> q4 = IZR (705090610717565) * bpow radix2 (-57) -> q5 = IZR (6472263933108925) * bpow radix2 (-57) -> q6 = IZR (5159111431375361) * bpow radix2 (-60) -> q7 = IZR (4389957216634859) * bpow radix2 (-57) -> q8 = IZR (-769501581422205) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 1 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12941186 * bpow radix2 (-98)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_02 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (563041619679033) * bpow radix2 (-54) -> r1 = IZR (8283258175087593) * bpow radix2 (-113) -> rH = IZR (4505800262550625) * bpow radix2 (-52) -> rL = IZR (-8498763825352503) * bpow radix2 (-111) -> q0 = IZR (4510204759385963) * bpow radix2 (-58) -> q1 = IZR (6031241555073311) * bpow radix2 (-55) -> q2 = IZR (6782953122433409) * bpow radix2 (-59) -> q3 = IZR (2735277006179843) * bpow radix2 (-55) -> q4 = IZR (5674578463174089) * bpow radix2 (-59) -> q5 = IZR (6588663934042381) * bpow radix2 (-57) -> q6 = IZR (2450422438503577) * bpow radix2 (-58) -> q7 = IZR (4554878066920787) * bpow radix2 (-57) -> q8 = IZR (5171806696599027) * bpow radix2 (-52) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 2 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10765043 * bpow radix2 (-98)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_03 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6757875791540393) * bpow radix2 (-57) -> r1 = IZR (3381170071236069) * bpow radix2 (-111) -> rH = IZR (4508555598381145) * bpow radix2 (-52) -> rL = IZR (4568242766441471) * bpow radix2 (-106) -> q0 = IZR (211803933175723) * bpow radix2 (-53) -> q1 = IZR (3032222950245231) * bpow radix2 (-54) -> q2 = IZR (5113185997534887) * bpow radix2 (-58) -> q3 = IZR (1388523334125217) * bpow radix2 (-54) -> q4 = IZR (4298567617008109) * bpow radix2 (-58) -> q5 = IZR (848155880411463) * bpow radix2 (-54) -> q6 = IZR (59035705554335) * bpow radix2 (-52) -> q7 = IZR (2369686360596989) * bpow radix2 (-56) -> q8 = IZR (1570493318319017) * bpow radix2 (-51) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 3 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12954495 * bpow radix2 (-99)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_04 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4506536824354329) * bpow radix2 (-56) -> r1 = IZR (4928985476488941) * bpow radix2 (-110) -> rH = IZR (1128105393592573) * bpow radix2 (-50) -> rL = IZR (-6800162284299809) * bpow radix2 (-106) -> q0 = IZR (4530117345250175) * bpow radix2 (-57) -> q1 = IZR (6111217124572785) * bpow radix2 (-55) -> q2 = IZR (858301356307651) * bpow radix2 (-55) -> q3 = IZR (709057022684735) * bpow radix2 (-53) -> q4 = IZR (5811956754621423) * bpow radix2 (-58) -> q5 = IZR (7065931195228945) * bpow radix2 (-57) -> q6 = IZR (2629417887522087) * bpow radix2 (-57) -> q7 = IZR (1280965164106671) * bpow radix2 (-55) -> q8 = IZR (-7551129699268327) * bpow radix2 (-52) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 4 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15983639 * bpow radix2 (-98)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_05 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5635241943295741) * bpow radix2 (-56) -> r1 = IZR (2522832324115641) * bpow radix2 (-109) -> rH = IZR (4517406758996121) * bpow radix2 (-52) -> rL = IZR (-5097144788332017) * bpow radix2 (-108) -> q0 = IZR (5681435177121135) * bpow radix2 (-57) -> q1 = IZR (771480561511315) * bpow radix2 (-52) -> q2 = IZR (8662247121360415) * bpow radix2 (-58) -> q3 = IZR (5827084061175837) * bpow radix2 (-56) -> q4 = IZR (3698232099254743) * bpow radix2 (-57) -> q5 = IZR (14524256662937) * bpow radix2 (-48) -> q6 = IZR (6486473084075553) * bpow radix2 (-58) -> q7 = IZR (5506244840117563) * bpow radix2 (-57) -> q8 = IZR (5637488977063009) * bpow radix2 (-50) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 5 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11763624 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_06 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3382667194790551) * bpow radix2 (-55) -> r1 = IZR (4076271803792779) * bpow radix2 (-111) -> rH = IZR (4523522259223879) * bpow radix2 (-52) -> rL = IZR (-4357064405925269) * bpow radix2 (-105) -> q0 = IZR (53480066118903) * bpow radix2 (-50) -> q1 = IZR (780838237402825) * bpow radix2 (-52) -> q2 = IZR (5256156230207593) * bpow radix2 (-57) -> q3 = IZR (3009939830227179) * bpow radix2 (-55) -> q4 = IZR (4536248364932311) * bpow radix2 (-57) -> q5 = IZR (7904282598378947) * bpow radix2 (-57) -> q6 = IZR (8114613892451433) * bpow radix2 (-58) -> q7 = IZR (6065208514334213) * bpow radix2 (-57) -> q8 = IZR (2847113355957759) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 6 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11868761 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_07 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (7897098401290029) * bpow radix2 (-56) -> r1 = IZR (519994820247555) * bpow radix2 (-106) -> rH = IZR (566347723721473) * bpow radix2 (-49) -> rL = IZR (6185128859481527) * bpow radix2 (-108) -> q0 = IZR (4012434379674345) * bpow radix2 (-56) -> q1 = IZR (1584068131677005) * bpow radix2 (-53) -> q2 = IZR (6214448053513121) * bpow radix2 (-57) -> q3 = IZR (6253245849272579) * bpow radix2 (-56) -> q4 = IZR (2715595832258703) * bpow radix2 (-56) -> q5 = IZR (8479263250366673) * bpow radix2 (-57) -> q6 = IZR (5051912482551943) * bpow radix2 (-57) -> q7 = IZR (1692639193815033) * bpow radix2 (-55) -> q8 = IZR (7118056182831249) * bpow radix2 (-54) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 7 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13628899 * bpow radix2 (-100)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_08 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2257705494990607) * bpow radix2 (-54) -> r1 = IZR (3350591885863445) * bpow radix2 (-111) -> rH = IZR (2269600879738189) * bpow radix2 (-51) -> rL = IZR (-5599664444214413) * bpow radix2 (-106) -> q0 = IZR (576406572631921) * bpow radix2 (-53) -> q1 = IZR (6441114716394799) * bpow radix2 (-55) -> q2 = IZR (7212561356226845) * bpow radix2 (-57) -> q3 = IZR (3265067867187775) * bpow radix2 (-55) -> q4 = IZR (6395433731352679) * bpow radix2 (-57) -> q5 = IZR (2293386867470157) * bpow radix2 (-55) -> q6 = IZR (745411088331103) * bpow radix2 (-54) -> q7 = IZR (959113422211695) * bpow radix2 (-54) -> q8 = IZR (1523183162926223) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 8 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12670436 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_09 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (158856212137569) * bpow radix2 (-50) -> r1 = IZR (-2169947621777645) * bpow radix2 (-107) -> rH = IZR (4548801375835321) * bpow radix2 (-52) -> rL = IZR (-7196522371567301) * bpow radix2 (-106) -> q0 = IZR (652580222286711) * bpow radix2 (-53) -> q1 = IZR (6561909193701257) * bpow radix2 (-55) -> q2 = IZR (2064391716093195) * bpow radix2 (-55) -> q3 = IZR (6854115320369491) * bpow radix2 (-56) -> q4 = IZR (465174986871869) * bpow radix2 (-53) -> q5 = IZR (5001092651520301) * bpow radix2 (-56) -> q6 = IZR (7213954632421331) * bpow radix2 (-57) -> q7 = IZR (8659056216241305) * bpow radix2 (-57) -> q8 = IZR (1359517317361463) * bpow radix2 (-62) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 9 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15624598 * bpow radix2 (-103)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_10 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5652661403718691) * bpow radix2 (-55) -> r1 = IZR (-610971616812469) * bpow radix2 (-107) -> rH = IZR (1139900692263115) * bpow radix2 (-50) -> rL = IZR (3887429065679749) * bpow radix2 (-108) -> q0 = IZR (2921066839032607) * bpow radix2 (-55) -> q1 = IZR (3349723894690445) * bpow radix2 (-54) -> q2 = IZR (584821581316745) * bpow radix2 (-53) -> q3 = IZR (3614720398617367) * bpow radix2 (-55) -> q4 = IZR (4294483681742503) * bpow radix2 (-56) -> q5 = IZR (2745881703779187) * bpow radix2 (-55) -> q6 = IZR (8565032463280933) * bpow radix2 (-57) -> q7 = IZR (4975253597752989) * bpow radix2 (-56) -> q8 = IZR (-2592746993424111) * bpow radix2 (-50) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 10 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11158999 * bpow radix2 (-97)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_11 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (388959412508115) * bpow radix2 (-51) -> r1 = IZR (-1784017606067161) * bpow radix2 (-107) -> rH = IZR (4571631137185043) * bpow radix2 (-52) -> rL = IZR (-8045827140788093) * bpow radix2 (-111) -> q0 = IZR (3238670008129077) * bpow radix2 (-55) -> q1 = IZR (3427323924897625) * bpow radix2 (-54) -> q2 = IZR (1314962795670395) * bpow radix2 (-54) -> q3 = IZR (7661152995987803) * bpow radix2 (-56) -> q4 = IZR (4925911566934313) * bpow radix2 (-56) -> q5 = IZR (6069959352126049) * bpow radix2 (-56) -> q6 = IZR (2503126283513649) * bpow radix2 (-55) -> q7 = IZR (2865473322349421) * bpow radix2 (-55) -> q8 = IZR (8130831088764329) * bpow radix2 (-54) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 11 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14215686 * bpow radix2 (-100)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_12 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1698905372991039) * bpow radix2 (-53) -> r1 = IZR (-5704001806564655) * bpow radix2 (-109) -> rH = IZR (4584914914302779) * bpow radix2 (-52) -> rL = IZR (1950688671142495) * bpow radix2 (-104) -> q0 = IZR (1781991221753307) * bpow radix2 (-54) -> q1 = IZR (7028564566951415) * bpow radix2 (-55) -> q2 = IZR (1469312501743905) * bpow radix2 (-54) -> q3 = IZR (8155192213350935) * bpow radix2 (-56) -> q4 = IZR (5625969837372671) * bpow radix2 (-56) -> q5 = IZR (6749209287842715) * bpow radix2 (-56) -> q6 = IZR (5864224426708327) * bpow radix2 (-56) -> q7 = IZR (6668196914247527) * bpow radix2 (-56) -> q8 = IZR (3749877629424639) * bpow radix2 (-51) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 12 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14861414 * bpow radix2 (-98)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_13 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3684816479997127) * bpow radix2 (-54) -> r1 = IZR (-371448447936983) * bpow radix2 (-105) -> rH = IZR (4599485963920735) * bpow radix2 (-52) -> rL = IZR (6066579618235403) * bpow radix2 (-106) -> q0 = IZR (7795818328458471) * bpow radix2 (-56) -> q1 = IZR (451400344340429) * bpow radix2 (-51) -> q2 = IZR (6535903764664947) * bpow radix2 (-56) -> q3 = IZR (8718537401278367) * bpow radix2 (-56) -> q4 = IZR (3203291313420643) * bpow radix2 (-55) -> q5 = IZR (7545907466955763) * bpow radix2 (-56) -> q6 = IZR (1701641438989519) * bpow radix2 (-54) -> q7 = IZR (3884724380411283) * bpow radix2 (-55) -> q8 = IZR (5017868095468731) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 13 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10386332 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_14 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (7945548093646923) * bpow radix2 (-55) -> r1 = IZR (-6601042896522177) * bpow radix2 (-109) -> rH = IZR (2307689900185971) * bpow radix2 (-51) -> rL = IZR (-5991750353204499) * bpow radix2 (-106) -> q0 = IZR (2120707846735005) * bpow radix2 (-54) -> q1 = IZR (3718773847578687) * bpow radix2 (-54) -> q2 = IZR (7241538279682043) * bpow radix2 (-56) -> q3 = IZR (4679687364319231) * bpow radix2 (-55) -> q4 = IZR (7281636677624775) * bpow radix2 (-56) -> q5 = IZR (8479893459712933) * bpow radix2 (-56) -> q6 = IZR (8072885025702265) * bpow radix2 (-56) -> q7 = IZR (1146303575732757) * bpow radix2 (-53) -> q8 = IZR (2404599983395017) * bpow radix2 (-51) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 14 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 8823123 * bpow radix2 (-98)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_15 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2130883665697869) * bpow radix2 (-53) -> r1 = IZR (8052597587383083) * bpow radix2 (-114) -> rH = IZR (2316317920626055) * bpow radix2 (-51) -> rL = IZR (-8763360667876271) * bpow radix2 (-106) -> q0 = IZR (4595536458384939) * bpow radix2 (-55) -> q1 = IZR (7675557618464065) * bpow radix2 (-55) -> q2 = IZR (8000572592974283) * bpow radix2 (-56) -> q3 = IZR (5043650887300247) * bpow radix2 (-55) -> q4 = IZR (4133710826304487) * bpow radix2 (-55) -> q5 = IZR (299226727192479) * bpow radix2 (-51) -> q6 = IZR (303885005635245) * bpow radix2 (-51) -> q7 = IZR (2705079352906485) * bpow radix2 (-54) -> q8 = IZR (-6832789283283419) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 15 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14415318 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_16 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4551882811606989) * bpow radix2 (-54) -> r1 = IZR (2136636549465025) * bpow radix2 (-108) -> rH = IZR (4651297694611163) * bpow radix2 (-52) -> rL = IZR (-1118956374265591) * bpow radix2 (-103) -> q0 = IZR (620173025948155) * bpow radix2 (-52) -> q1 = IZR (124034605189631) * bpow radix2 (-49) -> q2 = IZR (4410119295632043) * bpow radix2 (-55) -> q3 = IZR (1364196902115541) * bpow radix2 (-53) -> q4 = IZR (2345791433481071) * bpow radix2 (-54) -> q5 = IZR (5430623645062917) * bpow radix2 (-55) -> q6 = IZR (2785640742475551) * bpow radix2 (-54) -> q7 = IZR (1604778968818183) * bpow radix2 (-53) -> q8 = IZR (3154147363098467) * bpow radix2 (-58) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 16 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14127057 * bpow radix2 (-101)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_17 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4843209830191431) * bpow radix2 (-54) -> r1 = IZR (-3904450923473265) * bpow radix2 (-107) -> rH = IZR (4671413485200487) * bpow radix2 (-52) -> rL = IZR (4637348302410697) * bpow radix2 (-109) -> q0 = IZR (667520077738131) * bpow radix2 (-52) -> q1 = IZR (1028442373822595) * bpow radix2 (-52) -> q2 = IZR (4854361000795953) * bpow radix2 (-55) -> q3 = IZR (5925705947891195) * bpow radix2 (-55) -> q4 = IZR (2662889673219899) * bpow radix2 (-54) -> q5 = IZR (6186763561595531) * bpow radix2 (-55) -> q6 = IZR (6691953071521055) * bpow radix2 (-55) -> q7 = IZR (3824993744824487) * bpow radix2 (-54) -> q8 = IZR (-7620072313664745) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 17 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 16112528 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_18 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5135840888347691) * bpow radix2 (-54) -> r1 = IZR (2953370815032153) * bpow radix2 (-110) -> rH = IZR (4693036224830451) * bpow radix2 (-52) -> rL = IZR (-2423744871033107) * bpow radix2 (-105) -> q0 = IZR (179161510173803) * bpow radix2 (-50) -> q1 = IZR (4272911596004035) * bpow radix2 (-54) -> q2 = IZR (5337664691653425) * bpow radix2 (-55) -> q3 = IZR (6458177869149051) * bpow radix2 (-55) -> q4 = IZR (6049852129006355) * bpow radix2 (-55) -> q5 = IZR (442364892008963) * bpow radix2 (-51) -> q6 = IZR (3855120409237537) * bpow radix2 (-54) -> q7 = IZR (4590889623075055) * bpow radix2 (-54) -> q8 = IZR (3087798930790951) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 18 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12239946 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_19 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5429871964039857) * bpow radix2 (-54) -> r1 = IZR (-6490500646447493) * bpow radix2 (-108) -> rH = IZR (4716224232773905) * bpow radix2 (-52) -> rL = IZR (8176254165422927) * bpow radix2 (-106) -> q0 = IZR (3070912271514361) * bpow radix2 (-54) -> q1 = IZR (2223917754634905) * bpow radix2 (-53) -> q2 = IZR (733167929188207) * bpow radix2 (-52) -> q3 = IZR (3531681590723073) * bpow radix2 (-54) -> q4 = IZR (107499245619945) * bpow radix2 (-49) -> q5 = IZR (2032647331868163) * bpow radix2 (-53) -> q6 = IZR (1138864890473465) * bpow radix2 (-52) -> q7 = IZR (2760164288095821) * bpow radix2 (-53) -> q8 = IZR (4857085858731957) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 19 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9745167 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_20 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2862701429158229) * bpow radix2 (-53) -> r1 = IZR (954292783890387) * bpow radix2 (-105) -> rH = IZR (4741041613197763) * bpow radix2 (-52) -> rL = IZR (-891457182481707) * bpow radix2 (-108) -> q0 = IZR (6567676693607291) * bpow radix2 (-55) -> q1 = IZR (2320010468391147) * bpow radix2 (-53) -> q2 = IZR (6443488882525645) * bpow radix2 (-55) -> q3 = IZR (3876042378076121) * bpow radix2 (-54) -> q4 = IZR (1958876648417047) * bpow radix2 (-53) -> q5 = IZR (1172243004827131) * bpow radix2 (-52) -> q6 = IZR (2695183152357737) * bpow radix2 (-53) -> q7 = IZR (416559781958455) * bpow radix2 (-50) -> q8 = IZR (4630788634616861) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 20 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9436039 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_21 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3011268786730881) * bpow radix2 (-53) -> r1 = IZR (-7973071420247265) * bpow radix2 (-108) -> rH = IZR (2383779398926573) * bpow radix2 (-51) -> rL = IZR (-1051748032238729) * bpow radix2 (-105) -> q0 = IZR (3506210136423873) * bpow radix2 (-54) -> q1 = IZR (2425575966350845) * bpow radix2 (-53) -> q2 = IZR (884889248969855) * bpow radix2 (-52) -> q3 = IZR (4268583771725079) * bpow radix2 (-54) -> q4 = IZR (8939940363767059) * bpow radix2 (-55) -> q5 = IZR (5430313580872895) * bpow radix2 (-54) -> q6 = IZR (3244828538216955) * bpow radix2 (-53) -> q7 = IZR (8097917668160167) * bpow radix2 (-54) -> q8 = IZR (-2636307948376459) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 21 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11719431 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_22 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3160692363676727) * bpow radix2 (-53) -> r1 = IZR (4082759024613229) * bpow radix2 (-107) -> rH = IZR (1198963290937753) * bpow radix2 (-50) -> rL = IZR (-1699263973706287) * bpow radix2 (-104) -> q0 = IZR (3738959720133679) * bpow radix2 (-54) -> q1 = IZR (79424192182443) * bpow radix2 (-48) -> q2 = IZR (3890162609457145) * bpow radix2 (-54) -> q3 = IZR (4716928981621589) * bpow radix2 (-54) -> q4 = IZR (638854566837545) * bpow radix2 (-51) -> q5 = IZR (6314622548223211) * bpow radix2 (-54) -> q6 = IZR (7739894549740871) * bpow radix2 (-54) -> q7 = IZR (4944392643048417) * bpow radix2 (-53) -> q8 = IZR (-5636631413204235) * bpow radix2 (-50) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 22 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13488529 * bpow radix2 (-96)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_23 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6622058009063315) * bpow radix2 (-54) -> r1 = IZR (-6538903309322899) * bpow radix2 (-108) -> rH = IZR (4826009737352117) * bpow radix2 (-52) -> rL = IZR (6141958890159565) * bpow radix2 (-111) -> q0 = IZR (995778852450563) * bpow radix2 (-52) -> q1 = IZR (1334550729326121) * bpow radix2 (-52) -> q2 = IZR (4278265659452911) * bpow radix2 (-54) -> q3 = IZR (2615086275350393) * bpow radix2 (-53) -> q4 = IZR (5857650728160687) * bpow radix2 (-54) -> q5 = IZR (3686744414966185) * bpow radix2 (-53) -> q6 = IZR (1154595129160855) * bpow radix2 (-51) -> q7 = IZR (759235480627909) * bpow radix2 (-50) -> q8 = IZR (7767999520138843) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 23 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 15225916 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_24 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6924676681523923) * bpow radix2 (-54) -> r1 = IZR (5604320021806189) * bpow radix2 (-112) -> rH = IZR (4858121998980315) * bpow radix2 (-52) -> rL = IZR (-72925177116655) * bpow radix2 (-100) -> q0 = IZR (8479631125492913) * bpow radix2 (-55) -> q1 = IZR (2809413140567349) * bpow radix2 (-53) -> q2 = IZR (4709348856472351) * bpow radix2 (-54) -> q3 = IZR (5819205790431609) * bpow radix2 (-54) -> q4 = IZR (3365792563037537) * bpow radix2 (-53) -> q5 = IZR (1080820367399499) * bpow radix2 (-51) -> q6 = IZR (2791775213866963) * bpow radix2 (-52) -> q7 = IZR (7485035877023839) * bpow radix2 (-53) -> q8 = IZR (8986060013205109) * bpow radix2 (-53) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 24 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10074174 * bpow radix2 (-101)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_25 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1807341534505351) * bpow radix2 (-52) -> r1 = IZR (933526249855901) * bpow radix2 (-105) -> rH = IZR (4892292803818435) * bpow radix2 (-52) -> rL = IZR (6960967058538587) * bpow radix2 (-108) -> q0 = IZR (4510324682287235) * bpow radix2 (-54) -> q1 = IZR (2963949924318609) * bpow radix2 (-53) -> q2 = IZR (5189828962856573) * bpow radix2 (-54) -> q3 = IZR (3248562644448439) * bpow radix2 (-53) -> q4 = IZR (7758703514837457) * bpow radix2 (-54) -> q5 = IZR (2545967047172755) * bpow radix2 (-52) -> q6 = IZR (6741866046690717) * bpow radix2 (-53) -> q7 = IZR (2319817733600743) * bpow radix2 (-51) -> q8 = IZR (7744582827795301) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 25 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14534809 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_26 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3768129260197193) * bpow radix2 (-53) -> r1 = IZR (8085781135683871) * bpow radix2 (-108) -> rH = IZR (2464317719541811) * bpow radix2 (-51) -> rL = IZR (-7142706471951485) * bpow radix2 (-108) -> q0 = IZR (2398026131764663) * bpow radix2 (-53) -> q1 = IZR (3134370098270537) * bpow radix2 (-53) -> q2 = IZR (2863624215254571) * bpow radix2 (-53) -> q3 = IZR (909968562658425) * bpow radix2 (-51) -> q4 = IZR (8971237795862965) * bpow radix2 (-54) -> q5 = IZR (6024445591820709) * bpow radix2 (-53) -> q6 = IZR (510375146503167) * bpow radix2 (-49) -> q7 = IZR (5791100654842779) * bpow radix2 (-52) -> q8 = IZR (3017847515141841) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 26 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12106302 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_27 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1961373352041025) * bpow radix2 (-52) -> r1 = IZR (2145145534618889) * bpow radix2 (-106) -> rH = IZR (1241818710238557) * bpow radix2 (-50) -> rL = IZR (-4175444700197533) * bpow radix2 (-105) -> q0 = IZR (2549287474062639) * bpow radix2 (-53) -> q1 = IZR (6645176519966189) * bpow radix2 (-54) -> q2 = IZR (6330512507322983) * bpow radix2 (-54) -> q3 = IZR (4093134128205551) * bpow radix2 (-53) -> q4 = IZR (2602318934884591) * bpow radix2 (-52) -> q5 = IZR (447584470790489) * bpow radix2 (-49) -> q6 = IZR (625941694968661) * bpow radix2 (-49) -> q7 = IZR (3629895130933553) * bpow radix2 (-51) -> q8 = IZR (868197057756901) * bpow radix2 (-45) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 27 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13156843 * bpow radix2 (-94)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_28 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (8157218589441695) * bpow radix2 (-54) -> r1 = IZR (-6965912755631907) * bpow radix2 (-109) -> rH = IZR (1252087249931759) * bpow radix2 (-50) -> rL = IZR (-3433888551477617) * bpow radix2 (-106) -> q0 = IZR (5419662685694957) * bpow radix2 (-54) -> q1 = IZR (3530822343199475) * bpow radix2 (-53) -> q2 = IZR (7010184244403459) * bpow radix2 (-54) -> q3 = IZR (4620044341553855) * bpow radix2 (-53) -> q4 = IZR (3030748456584179) * bpow radix2 (-52) -> q5 = IZR (4277366743175477) * bpow radix2 (-52) -> q6 = IZR (3071951335132633) * bpow radix2 (-51) -> q7 = IZR (4582581211862877) * bpow radix2 (-51) -> q8 = IZR (3221573680827911) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 28 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12595188 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_29 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (8471590926422123) * bpow radix2 (-54) -> r1 = IZR (-6051891562368379) * bpow radix2 (-110) -> rH = IZR (1263002646943313) * bpow radix2 (-50) -> rL = IZR (-6628627455915475) * bpow radix2 (-111) -> q0 = IZR (2880654885071323) * bpow radix2 (-53) -> q1 = IZR (7523301949328493) * bpow radix2 (-54) -> q2 = IZR (3889426850227687) * bpow radix2 (-53) -> q3 = IZR (5234949863044023) * bpow radix2 (-53) -> q4 = IZR (7087770110373689) * bpow radix2 (-53) -> q5 = IZR (5135988772845193) * bpow radix2 (-52) -> q6 = IZR (7596557121840873) * bpow radix2 (-52) -> q7 = IZR (5823523265258095) * bpow radix2 (-51) -> q8 = IZR (3600221697932263) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 29 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13903382 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_30 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2197194332665789) * bpow radix2 (-52) -> r1 = IZR (-4469080061197251) * bpow radix2 (-109) -> rH = IZR (2549214426231573) * bpow radix2 (-51) -> rL = IZR (7853668715149175) * bpow radix2 (-107) -> q0 = IZR (6125771837752967) * bpow radix2 (-54) -> q1 = IZR (8036167599586481) * bpow radix2 (-54) -> q2 = IZR (8651602853959893) * bpow radix2 (-54) -> q3 = IZR (5955533884745109) * bpow radix2 (-53) -> q4 = IZR (4161733697591853) * bpow radix2 (-52) -> q5 = IZR (1550111093413251) * bpow radix2 (-50) -> q6 = IZR (4729285214242525) * bpow radix2 (-51) -> q7 = IZR (465869293925453) * bpow radix2 (-47) -> q8 = IZR (1507774243268843) * bpow radix2 (-45) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 30 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11076033 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_31 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (4554477933135265) * bpow radix2 (-53) -> r1 = IZR (4097092193959195) * bpow radix2 (-107) -> rH = IZR (5147791825775151) * bpow radix2 (-52) -> rL = IZR (-3522066238407225) * bpow radix2 (-107) -> q0 = IZR (6515610196068835) * bpow radix2 (-54) -> q1 = IZR (4303648193713543) * bpow radix2 (-53) -> q2 = IZR (2411648710426553) * bpow radix2 (-52) -> q3 = IZR (212616380250563) * bpow radix2 (-48) -> q4 = IZR (613726681006329) * bpow radix2 (-49) -> q5 = IZR (1882094239733087) * bpow radix2 (-50) -> q6 = IZR (2972405951395771) * bpow radix2 (-50) -> q7 = IZR (2402073976672927) * bpow radix2 (-49) -> q8 = IZR (-8795911621375995) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 31 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11293207 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_32 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2358079250676147) * bpow radix2 (-52) -> r1 = IZR (-4348880303153491) * bpow radix2 (-106) -> rH = IZR (1300077228592327) * bpow radix2 (-50) -> rL = IZR (5427618362502125) * bpow radix2 (-106) -> q0 = IZR (3466872609579539) * bpow radix2 (-53) -> q1 = IZR (2311248406386359) * bpow radix2 (-52) -> q2 = IZR (1348228237051475) * bpow radix2 (-51) -> q3 = IZR (243965109564779) * bpow radix2 (-48) -> q4 = IZR (2910461382898369) * bpow radix2 (-51) -> q5 = IZR (4598038638091141) * bpow radix2 (-51) -> q6 = IZR (3733284131994545) * bpow radix2 (-50) -> q7 = IZR (6243166936059511) * bpow radix2 (-50) -> q8 = IZR (5569593202407149) * bpow radix2 (-47) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 32 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 8890353 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_33 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2439766260842537) * bpow radix2 (-52) -> r1 = IZR (3901760084309115) * bpow radix2 (-108) -> rH = IZR (2628106974626967) * bpow radix2 (-51) -> rL = IZR (1167323935010109) * bpow radix2 (-104) -> q0 = IZR (1845880256206237) * bpow radix2 (-52) -> q1 = IZR (1244885460114997) * bpow radix2 (-51) -> q2 = IZR (6048045941157083) * bpow radix2 (-53) -> q3 = IZR (4499693009503049) * bpow radix2 (-52) -> q4 = IZR (3468757479485465) * bpow radix2 (-51) -> q5 = IZR (2826346812666525) * bpow radix2 (-50) -> q6 = IZR (296416027059505) * bpow radix2 (-46) -> q7 = IZR (8176618898136695) * bpow radix2 (-50) -> q8 = IZR (7053658890318003) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 33 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 14513680 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_34 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (2522354940421451) * bpow radix2 (-52) -> r1 = IZR (1415560525278243) * bpow radix2 (-105) -> rH = IZR (5315768793841329) * bpow radix2 (-52) -> rL = IZR (-119640199650705) * bpow radix2 (-100) -> q0 = IZR (7868784282584171) * bpow radix2 (-54) -> q1 = IZR (2690311841152427) * bpow radix2 (-52) -> q2 = IZR (3402560059982075) * bpow radix2 (-52) -> q3 = IZR (2606180570145789) * bpow radix2 (-51) -> q4 = IZR (4157509379265079) * bpow radix2 (-51) -> q5 = IZR (6996741369689371) * bpow radix2 (-51) -> q6 = IZR (6064674193936963) * bpow radix2 (-50) -> q7 = IZR (5404690659381237) * bpow radix2 (-49) -> q8 = IZR (13105765839257) * bpow radix2 (-38) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 34 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 8923100 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_35 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5211809141631349) * bpow radix2 (-53) -> r1 = IZR (-6735066006823505) * bpow radix2 (-107) -> rH = IZR (2689633817288871) * bpow radix2 (-51) -> rL = IZR (1393391792459019) * bpow radix2 (-104) -> q0 = IZR (65577975343163) * bpow radix2 (-47) -> q1 = IZR (1458181117694705) * bpow radix2 (-51) -> q2 = IZR (7684402452482127) * bpow radix2 (-53) -> q3 = IZR (6069168205411905) * bpow radix2 (-52) -> q4 = IZR (5013204213616159) * bpow radix2 (-51) -> q5 = IZR (4361735350807281) * bpow radix2 (-50) -> q6 = IZR (1958776140481007) * bpow radix2 (-48) -> q7 = IZR (7210977038642177) * bpow radix2 (-49) -> q8 = IZR (-8815200010715801) * bpow radix2 (-49) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 35 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 11712097 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_36 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5380958630785485) * bpow radix2 (-53) -> r1 = IZR (4801279467242141) * bpow radix2 (-112) -> rH = IZR (5447042111371653) * bpow radix2 (-52) -> rL = IZR (4089041772631895) * bpow radix2 (-106) -> q0 = IZR (8964275017571635) * bpow radix2 (-54) -> q1 = IZR (6344240351060221) * bpow radix2 (-53) -> q2 = IZR (272221249513281) * bpow radix2 (-48) -> q3 = IZR (3552871733314005) * bpow radix2 (-51) -> q4 = IZR (1521083548800615) * bpow radix2 (-49) -> q5 = IZR (685067029789715) * bpow radix2 (-47) -> q6 = IZR (5094788835348309) * bpow radix2 (-49) -> q7 = IZR (1215081273387691) * bpow radix2 (-46) -> q8 = IZR (8650594972180409) * bpow radix2 (-48) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 36 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13461851 * bpow radix2 (-97)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_37 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5552297702795629) * bpow radix2 (-53) -> r1 = IZR (-6595883140376129) * bpow radix2 (-108) -> rH = IZR (5519467488403195) * bpow radix2 (-52) -> rL = IZR (4150199042690085) * bpow radix2 (-106) -> q0 = IZR (4792848922823163) * bpow radix2 (-53) -> q1 = IZR (6925331570741381) * bpow radix2 (-53) -> q2 = IZR (4958345772924727) * bpow radix2 (-52) -> q3 = IZR (4184138885586199) * bpow radix2 (-51) -> q4 = IZR (3717985797536125) * bpow radix2 (-50) -> q5 = IZR (3471914362413973) * bpow radix2 (-49) -> q6 = IZR (3349664926694743) * bpow radix2 (-48) -> q7 = IZR (6622172630820801) * bpow radix2 (-48) -> q8 = IZR (-692675871695181) * bpow radix2 (-45) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 37 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9899807 * bpow radix2 (-92)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_38 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (5725978216097047) * bpow radix2 (-53) -> r1 = IZR (-3109741566573729) * bpow radix2 (-106) -> rH = IZR (5596970123316373) * bpow radix2 (-52) -> rL = IZR (-8347570507691329) * bpow radix2 (-108) -> q0 = IZR (320791651110139) * bpow radix2 (-49) -> q1 = IZR (1897094136786609) * bpow radix2 (-51) -> q2 = IZR (5670525123030287) * bpow radix2 (-52) -> q3 = IZR (154956470145451) * bpow radix2 (-46) -> q4 = IZR (2289095161802765) * bpow radix2 (-49) -> q5 = IZR (1109601829024885) * bpow radix2 (-47) -> q6 = IZR (4446131623821647) * bpow radix2 (-48) -> q7 = IZR (2282453322514225) * bpow radix2 (-46) -> q8 = IZR (-5647811859201235) * bpow radix2 (-52) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 38 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10201604 * bpow radix2 (-92)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_39 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1475541566799565) * bpow radix2 (-51) -> r1 = IZR (-8299365322324107) * bpow radix2 (-107) -> rH = IZR (5680036569571777) * bpow radix2 (-52) -> rL = IZR (-978854697390233) * bpow radix2 (-103) -> q0 = IZR (5505775253456759) * bpow radix2 (-53) -> q1 = IZR (260892697762339) * bpow radix2 (-48) -> q2 = IZR (6517426295913093) * bpow radix2 (-52) -> q3 = IZR (5916220034362889) * bpow radix2 (-51) -> q4 = IZR (5683319550412733) * bpow radix2 (-50) -> q5 = IZR (5728884039449369) * bpow radix2 (-49) -> q6 = IZR (5964421482402675) * bpow radix2 (-48) -> q7 = IZR (1593208313829191) * bpow radix2 (-45) -> q8 = IZR (7673297956373999) * bpow radix2 (-46) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 39 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 12307886 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_40 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6081044240322575) * bpow radix2 (-53) -> r1 = IZR (-962511478968961) * bpow radix2 (-107) -> rH = IZR (5769224750464927) * bpow radix2 (-52) -> rL = IZR (189688914154421) * bpow radix2 (-103) -> q0 = IZR (2958576795110219) * bpow radix2 (-52) -> q1 = IZR (2306172681316683) * bpow radix2 (-51) -> q2 = IZR (7531630079337669) * bpow radix2 (-52) -> q3 = IZR (7110343985822305) * bpow radix2 (-51) -> q4 = IZR (7117441727771049) * bpow radix2 (-50) -> q5 = IZR (934001725518031) * bpow radix2 (-46) -> q6 = IZR (4052056845230451) * bpow radix2 (-47) -> q7 = IZR (1127407690999829) * bpow radix2 (-44) -> q8 = IZR (2416936059242791) * bpow radix2 (-44) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 40 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 9467725 * bpow radix2 (-95)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_41 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (3131406622968955) * bpow radix2 (-52) -> r1 = IZR (3847272647562203) * bpow radix2 (-106) -> rH = IZR (5865177785022393) * bpow radix2 (-52) -> rL = IZR (-6333963736564785) * bpow radix2 (-108) -> q0 = IZR (99574446867875) * bpow radix2 (-47) -> q1 = IZR (5120094626298279) * bpow radix2 (-52) -> q2 = IZR (4377719325211449) * bpow radix2 (-51) -> q3 = IZR (4306556712450301) * bpow radix2 (-50) -> q4 = IZR (8998859513042027) * bpow radix2 (-50) -> q5 = IZR (4928150865958043) * bpow radix2 (-48) -> q6 = IZR (1393823401754525) * bpow radix2 (-45) -> q7 = IZR (101205329381547) * bpow radix2 (-40) -> q8 = IZR (2744161264153755) * bpow radix2 (-43) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 41 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13876788 * bpow radix2 (-92)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_42 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (6447696042574859) * bpow radix2 (-53) -> r1 = IZR (2485953806529461) * bpow radix2 (-107) -> rH = IZR (2984320620957201) * bpow radix2 (-51) -> rL = IZR (-2859391599151177) * bpow radix2 (-106) -> q0 = IZR (3439903014207957) * bpow radix2 (-52) -> q1 = IZR (5712286330762385) * bpow radix2 (-52) -> q2 = IZR (1280547615789565) * bpow radix2 (-49) -> q3 = IZR (5261635984958169) * bpow radix2 (-50) -> q4 = IZR (2874111606524593) * bpow radix2 (-48) -> q5 = IZR (411324418929619) * bpow radix2 (-44) -> q6 = IZR (3802474628415) * bpow radix2 (-36) -> q7 = IZR (2363479769120063) * bpow radix2 (-44) -> q8 = IZR (4644975817658749) * bpow radix2 (-44) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 42 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10094270 * bpow radix2 (-92)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_43 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (829492570578767) * bpow radix2 (-50) -> r1 = IZR (-3707749679839481) * bpow radix2 (-106) -> rH = IZR (6080484871944967) * bpow radix2 (-52) -> rL = IZR (-580507558600809) * bpow radix2 (-103) -> q0 = IZR (1861759497951997) * bpow radix2 (-51) -> q1 = IZR (1601921296837511) * bpow radix2 (-50) -> q2 = IZR (3018055367916151) * bpow radix2 (-50) -> q3 = IZR (6488929709043133) * bpow radix2 (-50) -> q4 = IZR (3713767834617703) * bpow radix2 (-48) -> q5 = IZR (4453850836196419) * bpow radix2 (-47) -> q6 = IZR (5519489761216533) * bpow radix2 (-46) -> q7 = IZR (7021732080075739) * bpow radix2 (-45) -> q8 = IZR (1262807764190069) * bpow radix2 (-41) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 43 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 8389189 * bpow radix2 (-92)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_44 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1706956054352621) * bpow radix2 (-51) -> r1 = IZR (-2901122215271727) * bpow radix2 (-106) -> rH = IZR (3100865129740775) * bpow radix2 (-51) -> rL = IZR (4740118239254557) * bpow radix2 (-112) -> q0 = IZR (2021304677164357) * bpow radix2 (-51) -> q1 = IZR (3615208904073083) * bpow radix2 (-51) -> q2 = IZR (7169115738384441) * bpow radix2 (-51) -> q3 = IZR (1010621381371163) * bpow radix2 (-47) -> q4 = IZR (4858970293721621) * bpow radix2 (-48) -> q5 = IZR (3058982807610893) * bpow radix2 (-46) -> q6 = IZR (7961676447557205) * bpow radix2 (-46) -> q7 = IZR (5317145150283821) * bpow radix2 (-44) -> q8 = IZR (6929787242983981) * bpow radix2 (-43) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 44 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 10360842 * bpow radix2 (-93)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma approx_45 (r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8 t : R) :
  r0 = IZR (1755914788480429) * bpow radix2 (-51) -> r1 = IZR (3270501030173145) * bpow radix2 (-106) -> rH = IZR (3166793197699573) * bpow radix2 (-51) -> rL = IZR (5058499357955529) * bpow radix2 (-108) -> q0 = IZR (68810088795983) * bpow radix2 (-46) -> q1 = IZR (8211880192886553) * bpow radix2 (-52) -> q2 = IZR (2147240825692887) * bpow radix2 (-49) -> q3 = IZR (5094008790994567) * bpow radix2 (-49) -> q4 = IZR (3222698913457889) * bpow radix2 (-47) -> q5 = IZR (8541731814890713) * bpow radix2 (-47) -> q6 = IZR (2924764773140051) * bpow radix2 (-44) -> q7 = IZR (4112943213466937) * bpow radix2 (-43) -> q8 = IZR (1572447563680239) * bpow radix2 (-40) -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR 45 / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl [q0; q1; q2; q3; q4; q5; q6; q7; q8] t))) <= (IZR 13346058 * bpow radix2 (-92)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Ht.
  subst r0 r1 rH rL q0 q1 q2 q3 q4 q5 q6 q7 q8. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

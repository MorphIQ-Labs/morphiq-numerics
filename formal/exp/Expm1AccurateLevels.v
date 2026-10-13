(** Written by generators/expm1_certificates.py; do not edit. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Gappa Require Gappa_definitions Gappa_pred_bnd.
Require Import ExpAccurateLevels.
Require expm1_accurate_level_02 expm1_accurate_level_03 expm1_accurate_level_04 expm1_accurate_level_05 expm1_accurate_level_06 expm1_accurate_level_07 expm1_accurate_level_08 expm1_accurate_level_09 expm1_accurate_level_10 expm1_accurate_level_11 expm1_accurate_level_12 expm1_accurate_level_13 expm1_accurate_level_14 expm1_accurate_level_15 expm1_accurate_level_16 expm1_accurate_small.
Open Scope R_scope.
Theorem em_level_16 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.988121436 <= Xn <= 1.011916515 -> Rabs En <= 0 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/16*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/16*Xn)) <= 519 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_16.l1 x kk ma Xn En mb s) (519 / 2^135).
Qed.
Theorem em_level_15 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.988004026 <= Xn <= 1.012036297 -> Rabs En <= 519 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/15*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/15*Xn)) <= 520 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_15.l1 x kk ma Xn En mb s) (520 / 2^135).
Qed.
Theorem em_level_14 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.987870961 <= Xn <= 1.012172050 -> Rabs En <= 520 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/14*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/14*Xn)) <= 521 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_14.l1 x kk ma Xn En mb s) (521 / 2^135).
Qed.
Theorem em_level_13 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.987718886 <= Xn <= 1.012327197 -> Rabs En <= 521 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/13*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/13*Xn)) <= 521 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_13.l1 x kk ma Xn En mb s) (521 / 2^135).
Qed.
Theorem em_level_12 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.987543416 <= Xn <= 1.012506212 -> Rabs En <= 521 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/12*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/12*Xn)) <= 521 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_12.l1 x kk ma Xn En mb s) (521 / 2^135).
Qed.
Theorem em_level_11 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.987338701 <= Xn <= 1.012715063 -> Rabs En <= 521 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/11*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/11*Xn)) <= 521 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_11.l1 x kk ma Xn En mb s) (521 / 2^135).
Qed.
Theorem em_level_10 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.987096765 <= Xn <= 1.012961887 -> Rabs En <= 521 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/10*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/10*Xn)) <= 522 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_10.l1 x kk ma Xn En mb s) (522 / 2^135).
Qed.
Theorem em_level_09 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.986806441 <= Xn <= 1.013258075 -> Rabs En <= 522 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/9*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/9*Xn)) <= 522 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_09.l1 x kk ma Xn En mb s) (522 / 2^135).
Qed.
Theorem em_level_08 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.986451601 <= Xn <= 1.013620084 -> Rabs En <= 522 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/8*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/8*Xn)) <= 523 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_08.l1 x kk ma Xn En mb s) (523 / 2^135).
Qed.
Theorem em_level_07 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.986008051 <= Xn <= 1.014072594 -> Rabs En <= 523 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/7*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/7*Xn)) <= 523 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_07.l1 x kk ma Xn En mb s) (523 / 2^135).
Qed.
Theorem em_level_06 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.985437773 <= Xn <= 1.014654393 -> Rabs En <= 523 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/6*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/6*Xn)) <= 524 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_06.l1 x kk ma Xn En mb s) (524 / 2^135).
Qed.
Theorem em_level_05 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.984677402 <= Xn <= 1.015430125 -> Rabs En <= 524 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/5*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/5*Xn)) <= 526 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_05.l1 x kk ma Xn En mb s) (526 / 2^135).
Qed.
Theorem em_level_04 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.983612882 <= Xn <= 1.016516151 -> Rabs En <= 526 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/4*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/4*Xn)) <= 528 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_04.l1 x kk ma Xn En mb s) (528 / 2^135).
Qed.
Theorem em_level_03 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.982016103 <= Xn <= 1.018145188 -> Rabs En <= 528 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/3*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/3*Xn)) <= 531 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_03.l1 x kk ma Xn En mb s) (531 / 2^135).
Qed.
Theorem em_level_02 x kk ma Xn En mb s :
 Rabs x <= 0.0312501 -> 0.979354804 <= Xn <= 1.020860251 -> Rabs En <= 531 / 2^135 ->
 Rabs kk <= /2^127 -> -/2^127 <= ma <= 0 -> -/2^127 <= mb <= 0 -> Rabs s <= /2^126 ->
 Rabs (1 + (x * (1/2*(1+kk))) * (1+ma) * (Xn+En) * (1+mb) + s - (1+x/2*Xn)) <= 538 / 2^135.
Proof.
 intros Hx HX HE Hk Hma Hmb Hs.
 apply Rabs_le_inv in Hx. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hk. apply Rabs_le_inv in Hs.
 bridge (expm1_accurate_level_02.l1 x kk ma Xn En mb s) (538 / 2^135).
Qed.
Theorem em_accurate_small_certificate G E2 m :
 0.974032205 <= G <= 1.026290376 -> Rabs E2 <= 650 / 2^135 -> -/2^127 <= m <= 0 ->
 Rabs ((G+E2)*(1+m)/G-1) <= /2^123.
Proof.
 intros HG HE Hm. apply Rabs_le_inv in HE.
 bridge (expm1_accurate_small.l1 G E2 m) (/2^123).
Qed.

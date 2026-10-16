(** Exact index reduction and certified correction on 37 <= x < 64. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Bits.
From Binary64 Require Import IEEE64.
Require Import StageGappa ErfcxTableReduction NormalLogTableReduction NormalLogTableRows NormalLogTailApprox.
Open Scope R_scope.
Definition normal_log_table_row64 i d :=
 match i with
 | 0%Z => log_table_00_value64 d
 | 1%Z => log_table_01_value64 d
 | 2%Z => log_table_02_value64 d
 | 3%Z => log_table_03_value64 d
 | 4%Z => log_table_04_value64 d
 | 5%Z => log_table_05_value64 d
 | 6%Z => log_table_06_value64 d
 | 7%Z => log_table_07_value64 d
 | 8%Z => log_table_08_value64 d
 | 9%Z => log_table_09_value64 d
 | 10%Z => log_table_10_value64 d
 | 11%Z => log_table_11_value64 d
 | 12%Z => log_table_12_value64 d
 | 13%Z => log_table_13_value64 d
 | 14%Z => log_table_14_value64 d
 | 15%Z => log_table_15_value64 d
 | 16%Z => log_table_16_value64 d
 | 17%Z => log_table_17_value64 d
 | 18%Z => log_table_18_value64 d
 | 19%Z => log_table_19_value64 d
 | 20%Z => log_table_20_value64 d
 | 21%Z => log_table_21_value64 d
 | 22%Z => log_table_22_value64 d
 | 23%Z => log_table_23_value64 d
 | 24%Z => log_table_24_value64 d
 | 25%Z => log_table_25_value64 d
 | 26%Z => log_table_26_value64 d
 | _ => log_table_00_value64 d
 end.
Definition normal_log_table_correction64 x :=
 let '(i,c,d,e):=table_binade64 x in normal_log_table_row64 (i-214)%Z d.
Theorem normal_log_table_correction_words x : finite x -> 37<=B x<64 ->
 finite(normal_log_table_correction64 x) /\
 3<=B(normal_log_table_correction64 x)<=7 /\
 Rabs(B(normal_log_table_correction64 x)-(ln(B x)+ln(2*PI)/2+
 normal_log_tail_polynomial(/(B x*B x))))<=21*bpow radix2(-54).
Proof.
 intros Fx X;pose proof(normal_log_table_reduce_ieee x Fx X)as Reduction.
 unfold normal_log_table_correction64;destruct(table_binade64 x)as[[[i c]d]e].
 destruct Reduction as[E [I [Fc [Fd [Value [Center D]]]]]].
 rewrite E in Center,D;change(bpow radix2 (5-6))with(/2)in D.
 destruct(Z.eq_dec (i-214) 0)as[J0|N0].
 { assert(Ix : (i=214)%Z) by lia.
   rewrite Ix in Center;change(IZR(214-49-32*5))with 5 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=75/2+B d)by lra.
   rewrite J0;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_00_words d Fd D). }
 destruct(Z.eq_dec (i-214) 1)as[J1|N1].
 { assert(Ix : (i=215)%Z) by lia.
   rewrite Ix in Center;change(IZR(215-49-32*5))with 6 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=77/2+B d)by lra.
   rewrite J1;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_01_words d Fd D). }
 destruct(Z.eq_dec (i-214) 2)as[J2|N2].
 { assert(Ix : (i=216)%Z) by lia.
   rewrite Ix in Center;change(IZR(216-49-32*5))with 7 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=79/2+B d)by lra.
   rewrite J2;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_02_words d Fd D). }
 destruct(Z.eq_dec (i-214) 3)as[J3|N3].
 { assert(Ix : (i=217)%Z) by lia.
   rewrite Ix in Center;change(IZR(217-49-32*5))with 8 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=81/2+B d)by lra.
   rewrite J3;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_03_words d Fd D). }
 destruct(Z.eq_dec (i-214) 4)as[J4|N4].
 { assert(Ix : (i=218)%Z) by lia.
   rewrite Ix in Center;change(IZR(218-49-32*5))with 9 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=83/2+B d)by lra.
   rewrite J4;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_04_words d Fd D). }
 destruct(Z.eq_dec (i-214) 5)as[J5|N5].
 { assert(Ix : (i=219)%Z) by lia.
   rewrite Ix in Center;change(IZR(219-49-32*5))with 10 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=85/2+B d)by lra.
   rewrite J5;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_05_words d Fd D). }
 destruct(Z.eq_dec (i-214) 6)as[J6|N6].
 { assert(Ix : (i=220)%Z) by lia.
   rewrite Ix in Center;change(IZR(220-49-32*5))with 11 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=87/2+B d)by lra.
   rewrite J6;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_06_words d Fd D). }
 destruct(Z.eq_dec (i-214) 7)as[J7|N7].
 { assert(Ix : (i=221)%Z) by lia.
   rewrite Ix in Center;change(IZR(221-49-32*5))with 12 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=89/2+B d)by lra.
   rewrite J7;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_07_words d Fd D). }
 destruct(Z.eq_dec (i-214) 8)as[J8|N8].
 { assert(Ix : (i=222)%Z) by lia.
   rewrite Ix in Center;change(IZR(222-49-32*5))with 13 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=91/2+B d)by lra.
   rewrite J8;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_08_words d Fd D). }
 destruct(Z.eq_dec (i-214) 9)as[J9|N9].
 { assert(Ix : (i=223)%Z) by lia.
   rewrite Ix in Center;change(IZR(223-49-32*5))with 14 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=93/2+B d)by lra.
   rewrite J9;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_09_words d Fd D). }
 destruct(Z.eq_dec (i-214) 10)as[J10|N10].
 { assert(Ix : (i=224)%Z) by lia.
   rewrite Ix in Center;change(IZR(224-49-32*5))with 15 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=95/2+B d)by lra.
   rewrite J10;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_10_words d Fd D). }
 destruct(Z.eq_dec (i-214) 11)as[J11|N11].
 { assert(Ix : (i=225)%Z) by lia.
   rewrite Ix in Center;change(IZR(225-49-32*5))with 16 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=97/2+B d)by lra.
   rewrite J11;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_11_words d Fd D). }
 destruct(Z.eq_dec (i-214) 12)as[J12|N12].
 { assert(Ix : (i=226)%Z) by lia.
   rewrite Ix in Center;change(IZR(226-49-32*5))with 17 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=99/2+B d)by lra.
   rewrite J12;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_12_words d Fd D). }
 destruct(Z.eq_dec (i-214) 13)as[J13|N13].
 { assert(Ix : (i=227)%Z) by lia.
   rewrite Ix in Center;change(IZR(227-49-32*5))with 18 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=101/2+B d)by lra.
   rewrite J13;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_13_words d Fd D). }
 destruct(Z.eq_dec (i-214) 14)as[J14|N14].
 { assert(Ix : (i=228)%Z) by lia.
   rewrite Ix in Center;change(IZR(228-49-32*5))with 19 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=103/2+B d)by lra.
   rewrite J14;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_14_words d Fd D). }
 destruct(Z.eq_dec (i-214) 15)as[J15|N15].
 { assert(Ix : (i=229)%Z) by lia.
   rewrite Ix in Center;change(IZR(229-49-32*5))with 20 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=105/2+B d)by lra.
   rewrite J15;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_15_words d Fd D). }
 destruct(Z.eq_dec (i-214) 16)as[J16|N16].
 { assert(Ix : (i=230)%Z) by lia.
   rewrite Ix in Center;change(IZR(230-49-32*5))with 21 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=107/2+B d)by lra.
   rewrite J16;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_16_words d Fd D). }
 destruct(Z.eq_dec (i-214) 17)as[J17|N17].
 { assert(Ix : (i=231)%Z) by lia.
   rewrite Ix in Center;change(IZR(231-49-32*5))with 22 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=109/2+B d)by lra.
   rewrite J17;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_17_words d Fd D). }
 destruct(Z.eq_dec (i-214) 18)as[J18|N18].
 { assert(Ix : (i=232)%Z) by lia.
   rewrite Ix in Center;change(IZR(232-49-32*5))with 23 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=111/2+B d)by lra.
   rewrite J18;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_18_words d Fd D). }
 destruct(Z.eq_dec (i-214) 19)as[J19|N19].
 { assert(Ix : (i=233)%Z) by lia.
   rewrite Ix in Center;change(IZR(233-49-32*5))with 24 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=113/2+B d)by lra.
   rewrite J19;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_19_words d Fd D). }
 destruct(Z.eq_dec (i-214) 20)as[J20|N20].
 { assert(Ix : (i=234)%Z) by lia.
   rewrite Ix in Center;change(IZR(234-49-32*5))with 25 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=115/2+B d)by lra.
   rewrite J20;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_20_words d Fd D). }
 destruct(Z.eq_dec (i-214) 21)as[J21|N21].
 { assert(Ix : (i=235)%Z) by lia.
   rewrite Ix in Center;change(IZR(235-49-32*5))with 26 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=117/2+B d)by lra.
   rewrite J21;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_21_words d Fd D). }
 destruct(Z.eq_dec (i-214) 22)as[J22|N22].
 { assert(Ix : (i=236)%Z) by lia.
   rewrite Ix in Center;change(IZR(236-49-32*5))with 27 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=119/2+B d)by lra.
   rewrite J22;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_22_words d Fd D). }
 destruct(Z.eq_dec (i-214) 23)as[J23|N23].
 { assert(Ix : (i=237)%Z) by lia.
   rewrite Ix in Center;change(IZR(237-49-32*5))with 28 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=121/2+B d)by lra.
   rewrite J23;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_23_words d Fd D). }
 destruct(Z.eq_dec (i-214) 24)as[J24|N24].
 { assert(Ix : (i=238)%Z) by lia.
   rewrite Ix in Center;change(IZR(238-49-32*5))with 29 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=123/2+B d)by lra.
   rewrite J24;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_24_words d Fd D). }
 destruct(Z.eq_dec (i-214) 25)as[J25|N25].
 { assert(Ix : (i=239)%Z) by lia.
   rewrite Ix in Center;change(IZR(239-49-32*5))with 30 in Center.
   change(bpow radix2 5)with 32 in Center.
   assert(Xvalue : B x=125/2+B d)by lra.
   rewrite J25;cbn [normal_log_table_row64]. rewrite Xvalue.
   exact(log_table_25_words d Fd D). }
 assert(Ix : (i=240)%Z) by lia.
 rewrite Ix in Center;change(IZR(240-49-32*5))with 31 in Center.
 change(bpow radix2 5)with 32 in Center.
 assert(Xvalue : B x=127/2+B d)by lra.
 assert(J : (i-214=26)%Z)by lia.
 rewrite J;cbn [normal_log_table_row64]. rewrite Xvalue.
 exact(log_table_26_words d Fd D).
Qed.

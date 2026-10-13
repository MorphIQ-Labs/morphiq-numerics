(** Shared indexing of the Q256 erfcx Taylor centers. *)
From Coq Require Import Reals ZArith List.
From Q Require Import Q256 Q256Real.
Require Import ErfcxAccurateData.
Import ListNotations.
Open Scope R_scope.
Definition center_numerator i :=
  if Nat.ltb i 49 then (Z.of_nat i-16)%Z
  else (2^((Z.of_nat i-49)/32)*(65+2*((Z.of_nat i-49) mod 32)))%Z.
Definition center_denominator i := if Nat.ltb i 49 then 32%Z else 64%Z.
Definition accurate_center i := IZR(center_numerator i)/IZR(center_denominator i).
Definition q_center i := constant_q (nth i f_at_c_data ([],0%Z)).

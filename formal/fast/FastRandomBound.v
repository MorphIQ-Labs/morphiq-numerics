(** Absolute Box–Muller output error, including the logarithm near one. *)
From Coq Require Import Reals Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Open Scope R_scope.

Definition bm_unit : R := /2^53.
Definition bm_log_floor : R := /2^65.
Definition bm_radius_error : R := 3/4*(14*bm_unit+/2^38)+2/2^50.

Lemma bm_sqrt_compare x y : 0<=x -> 0<=y -> x*x<=y*y -> x<=y.
Proof.
 intros X Y P. destruct (Rle_dec x y);[assumption|].
 assert (0<(x-y)*(x+y)) by (apply Rmult_lt_0_compat;lra).
 nra.
Qed.

Lemma bm_log_ranges L a b : bm_unit<=L<=37 ->
 Rabs(a-L)<=bm_unit*L+bm_log_floor -> Rabs(b-L)<=bm_unit*L ->
 8/9*L<=a<=38 /\ 8/9*L<=b<=38.
Proof.
 intros Lr A B. apply Rabs_le_inv in A. apply Rabs_le_inv in B.
 unfold bm_unit,bm_log_floor in *. split;split;nra.
Qed.

Lemma bm_radius_difference L a b : bm_unit<=L<=37 ->
 Rabs(a-L)<=bm_unit*L+bm_log_floor -> Rabs(b-L)<=bm_unit*L ->
 Rabs(sqrt(2*a)-sqrt(2*b))<=3/4*(14*bm_unit+/2^38).
Proof.
 intros Lr A B. destruct (bm_log_ranges L a b Lr A B) as [[Al Au] [Bl Bu]].
 assert (Lp:0<L) by (unfold bm_unit in Lr; lra).
 assert (Ap:0<=2*a) by nra. assert (Bp:0<=2*b) by nra.
 pose proof (sqrt_pos L) as Sl. pose proof (sqrt_def L ltac:(lra)) as Sl2.
 pose proof (sqrt_pos (2*a)) as Sa. pose proof (sqrt_def (2*a) Ap) as Sa2.
 pose proof (sqrt_pos (2*b)) as Sb. pose proof (sqrt_def (2*b) Bp) as Sb2.
 assert (Sr : /2^27<=sqrt L<=7).
 { split;apply bm_sqrt_compare;try lra;unfold bm_unit in Lr;nra. }
 assert (LA : 4/3*sqrt L<=sqrt(2*a)).
 { apply bm_sqrt_compare;try lra;nra. }
 assert (LB : 4/3*sqrt L<=sqrt(2*b)).
 { apply bm_sqrt_compare;try lra;nra. }
 set (E := Rabs(sqrt(2*a)-sqrt(2*b))).
 assert (E0:0<=E) by apply Rabs_pos.
 assert (Identity : E*(sqrt(2*a)+sqrt(2*b))=2*Rabs(a-b)).
 { unfold E. rewrite <-Rabs_pos_eq with (x:=sqrt(2*a)+sqrt(2*b)) by lra.
   rewrite <-Rabs_mult.
   replace ((sqrt(2*a)-sqrt(2*b))*(sqrt(2*a)+sqrt(2*b))) with (2*(a-b)) by nra.
   rewrite Rabs_mult,Rabs_pos_eq by lra. reflexivity. }
 assert (D : Rabs(a-b)<=2*bm_unit*L+bm_log_floor).
 { replace (a-b) with ((a-L)-(b-L)) by ring.
   eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp. lra. }
 assert (Den : E*(8/3*sqrt L)<=E*(sqrt(2*a)+sqrt(2*b))).
 { apply Rmult_le_compat_l;[exact E0|lra]. }
 assert (Budget : 2*bm_unit*L+bm_log_floor <= (14*bm_unit+/2^38)*sqrt L).
 { unfold bm_unit,bm_log_floor in *. nra. }
 apply (Rmult_le_reg_r (sqrt L));[lra|]. nra.
Qed.

Lemma bm_rounded_radii L a b rf rs : bm_unit<=L<=37 ->
 Rabs(a-L)<=bm_unit*L+bm_log_floor -> Rabs(b-L)<=bm_unit*L ->
 Rabs(rf-sqrt(2*a))<=/2^50 -> Rabs(rs-sqrt(2*b))<=/2^50 ->
 Rabs(rf-rs)<=bm_radius_error.
Proof.
 intros Lr A B F S. pose proof (bm_radius_difference L a b Lr A B) as D.
 replace (rf-rs) with ((rf-sqrt(2*a))+(sqrt(2*a)-sqrt(2*b))-(rs-sqrt(2*b))) by ring.
 eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp.
 eapply Rle_trans;[apply Rplus_le_compat_r;apply Rabs_triang|].
 unfold bm_radius_error. lra.
Qed.

(** The private radius logarithm retains the tight bound near one and
    spends a separate absolute allowance only away from cancellation. *)
Definition bm_pair_log_error L a :=
 Rabs(a-L)<=bm_unit*L+bm_log_floor \/
 (/2^9<=L /\ Rabs(a-L)<=/2^48*L+/2^45).

Lemma bm_pair_log_ranges L a b : bm_unit<=L<=37 ->
 bm_pair_log_error L a -> Rabs(b-L)<=bm_unit*L ->
 8/9*L<=a<=38 /\ 8/9*L<=b<=38.
Proof.
 intros Lr [A|[Far A]] B.
 - exact (bm_log_ranges L a b Lr A B).
 - apply Rabs_le_inv in A. apply Rabs_le_inv in B.
   unfold bm_unit,bm_log_floor in *. split;split;nra.
Qed.

Lemma bm_far_radius_difference L a b : /2^9<=L<=37 ->
 Rabs(a-L)<=/2^48*L+/2^45 -> Rabs(b-L)<=bm_unit*L ->
 Rabs(sqrt(2*a)-sqrt(2*b))+2/2^50<=/2^40.
Proof.
 intros Lr A B.
 assert (General:bm_unit<=L<=37) by (unfold bm_unit;lra).
 destruct (bm_pair_log_ranges L a b General (or_intror(conj (proj1 Lr) A)) B) as [[Al Au] [Bl Bu]].
 assert (Ap:0<=2*a) by nra. assert (Bp:0<=2*b) by nra.
 pose proof (sqrt_pos L) as Sl. pose proof (sqrt_def L ltac:(lra)) as Sl2.
 pose proof (sqrt_pos (2*a)) as Sa. pose proof (sqrt_def (2*a) Ap) as Sa2.
 pose proof (sqrt_pos (2*b)) as Sb. pose proof (sqrt_def (2*b) Bp) as Sb2.
 assert (Sr:/32<=sqrt L<=7).
 { split;apply bm_sqrt_compare;try lra;nra. }
 assert (LA:4/3*sqrt L<=sqrt(2*a)) by (apply bm_sqrt_compare;try lra;nra).
 assert (LB:4/3*sqrt L<=sqrt(2*b)) by (apply bm_sqrt_compare;try lra;nra).
 set (E:=Rabs(sqrt(2*a)-sqrt(2*b))).
 assert (E0:0<=E) by apply Rabs_pos.
 assert (Identity:E*(sqrt(2*a)+sqrt(2*b))=2*Rabs(a-b)).
 { unfold E. rewrite <-Rabs_pos_eq with(x:=sqrt(2*a)+sqrt(2*b)) by lra.
   rewrite <-Rabs_mult. replace ((sqrt(2*a)-sqrt(2*b))*(sqrt(2*a)+sqrt(2*b))) with (2*(a-b)) by nra.
   rewrite Rabs_mult,Rabs_pos_eq by lra. reflexivity. }
 assert (D:Rabs(a-b)<=(/2^48+bm_unit)*L+/2^45).
 { replace (a-b) with ((a-L)-(b-L)) by ring.
   eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp;lra. }
 assert (Den:E*(8/3*sqrt L)<=E*(sqrt(2*a)+sqrt(2*b))).
 { apply Rmult_le_compat_l;[exact E0|lra]. }
 assert (Budget:(/2^48+bm_unit)*L+/2^45 <= (7*(/2^48+bm_unit)+32/2^45)*sqrt L).
 { unfold bm_unit in *. nra. }
 assert (EB:E<=3/4*(7*(/2^48+bm_unit)+32/2^45)).
 { apply (Rmult_le_reg_r (sqrt L));[lra|]. nra. }
 unfold bm_unit in EB. lra.
Qed.

Lemma bm_pair_rounded_radii L a b rf rs : bm_unit<=L<=37 ->
 bm_pair_log_error L a -> Rabs(b-L)<=bm_unit*L ->
 Rabs(rf-sqrt(2*a))<=/2^50 -> Rabs(rs-sqrt(2*b))<=/2^50 ->
 Rabs(rf-rs)<=bm_radius_error.
Proof.
 intros Lr [A|[Far A]] B F S.
 - exact (bm_rounded_radii L a b rf rs Lr A B F S).
 - pose proof (bm_far_radius_difference L a b ltac:(lra) A B) as D.
   replace (rf-rs) with ((rf-sqrt(2*a))+(sqrt(2*a)-sqrt(2*b))-(rs-sqrt(2*b))) by ring.
   eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp.
   eapply Rle_trans;[apply Rplus_le_compat_r;apply Rabs_triang|].
   unfold bm_radius_error,bm_unit. lra.
Qed.

Theorem bm_output_bound L a b rf rs cf cs exact_angle yf ys :
 bm_unit<=L<=37 ->
 bm_pair_log_error L a -> Rabs(b-L)<=bm_unit*L ->
 Rabs(rf-sqrt(2*a))<=/2^50 -> Rabs(rs-sqrt(2*b))<=/2^50 ->
 Rabs rs<=9 -> Rabs exact_angle<=1 ->
 Rabs(cf-exact_angle)<=/2^44 -> Rabs(cs-exact_angle)<=bm_unit ->
 Rabs(yf-rf*cf)<=/2^50 -> Rabs(ys-rs*cs)<=/2^50 ->
 Rabs(yf-ys)<=/2^38.
Proof.
 intros Lr A B F S R C Cf Cs Yf Ys.
 pose proof (bm_pair_rounded_radii L a b rf rs Lr A B F S) as Radius.
 assert (Af : Rabs cf<=1+/2^44).
 { replace cf with ((cf-exact_angle)+exact_angle) by ring.
   eapply Rle_trans;[apply Rabs_triang|]. lra. }
 assert (Angular : Rabs(cf-cs)<=/2^44+bm_unit).
 { replace (cf-cs) with ((cf-exact_angle)-(cs-exact_angle)) by ring.
   eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp. lra. }
 assert (P : Rabs(rf*cf-rs*cs)<=bm_radius_error*(1+/2^44)+9*(/2^44+bm_unit)).
 { replace (rf*cf-rs*cs) with ((rf-rs)*cf+rs*(cf-cs)) by ring.
   eapply Rle_trans;[apply Rabs_triang|]. rewrite !Rabs_mult.
   apply Rplus_le_compat;apply Rmult_le_compat;try apply Rabs_pos;assumption. }
 replace (yf-ys) with ((yf-rf*cf)+(rf*cf-rs*cs)-(ys-rs*cs)) by ring.
 eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp.
 eapply Rle_trans;[apply Rplus_le_compat_r;apply Rabs_triang|].
 eapply Rle_trans with (/2^50+(bm_radius_error*(1+/2^44)+9*(/2^44+bm_unit))+/2^50);[lra|].
 unfold bm_radius_error,bm_unit. interval with (i_prec 100).
Qed.

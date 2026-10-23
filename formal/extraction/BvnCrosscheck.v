(** The transcription of the bivariate normal's scalar kernel
    (formal/bivariate/BvnKernel.v), extracted to OCaml so
    formal/extraction/bvndriver.ml can run it on the bvn lines of the internal
    cross-check corpus and compare with the Rust code bit for bit. The
    library functions the kernel calls ([exp], [sin], [asin], [norm_cdf]) are
    functions on binary64 encodings supplied by the driver: the results the
    Rust recorded for each call it made. *)

From Coq Require Import ZArith List Extraction ExtrOcamlBasic.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
Require Import BvnKernel.
Import ListNotations.
Open Scope Z_scope.

Definition lib_of (e s a n : Z -> Z) : lib :=
  mk_lib (fun v => b64_of_bits (e (bits_of_b64 v)))
         (fun v => b64_of_bits (s (bits_of_b64 v)))
         (fun v => b64_of_bits (a (bits_of_b64 v)))
         (fun v => b64_of_bits (n (bits_of_b64 v))).

Definition regime_code (r : regime) : Z :=
  match r with Independent => 0 | Comonotone => 1 | Countermonotone => 2 | Low => 3 | High => 4 end.

(** [bivariate_norm_cdf] of the encodings. *)
Definition x_bvn_cdf (e s a n : Z -> Z) (x y rho : Z) : Z :=
  bits_of_b64 (bivariate_norm_cdf (lib_of e s a n) (b64_of_bits x) (b64_of_bits y) (b64_of_bits rho)).

(** The table [BivariateNormal::new] builds: its regime, [asr] and each node's
    [kw], [p] and [q], or [None] for an invalid correlation. *)
Definition x_bvn_table (e s a n : Z -> Z) (rho : Z) : option (Z * Z * list (Z * Z * Z)) :=
  match build_table (lib_of e s a n) (b64_of_bits rho) with
  | None => None
  | Some t =>
      Some (regime_code (t_regime t), bits_of_b64 (t_asr t),
            map (fun '(kw, p, q) => (bits_of_b64 kw, bits_of_b64 p, bits_of_b64 q)) (t_nodes t))
  end.

Extraction "bvncrosscheck.ml" x_bvn_cdf x_bvn_table.

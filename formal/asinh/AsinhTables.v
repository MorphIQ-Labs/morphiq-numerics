(** Constants of asinh's transcription, written by generators/asinh_constants.py; do
    not edit. docs/asinh.md gives the derivation. Binary64 values are encodings; a
    Q256 value is its limbs, least significant first, and an exponent. *)
From Coq Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(** The series below 2^-7 (src/asinh/tables.rs POLY0). *)
Definition asinh_poly0 : list Z := [0xbfc5555555555555; 0x3fb333333331dd9c; 0xbfa6db6c60bd59aa; 0x3f9eba3d3684b4e5].
Definition asinh_ln2 : Z * Z := (0x3fe62e42fefa39ef, 0x3c7abc9e3b39803f).
Definition asinh_inv_ln2 : Z := 0x3ff71547652b82fe.
(** ln 2 in Q256: limbs and exponent (src/asinh/tables.rs LN2_Q256). *)
Definition asinh_ln2_q256 : list Z * Z := ([0x8a0d175b8baafa2c; 0x40f343267298b62d; 0xc9e3b39803f2f6af; 0xb17217f7d1cf79ab], -256).
(** 1/n, n = 1..N, in Q256 (src/asinh/tables.rs EXP_STEPS). *)
Definition asinh_exp_steps : list (list Z * Z) := [
  ([0x0000000000000000; 0x0000000000000000; 0x0000000000000000; 0x8000000000000000], -255);
  ([0x0000000000000000; 0x0000000000000000; 0x0000000000000000; 0x8000000000000000], -256);
  ([0xaaaaaaaaaaaaaaab; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa], -257);
  ([0x0000000000000000; 0x0000000000000000; 0x0000000000000000; 0x8000000000000000], -257);
  ([0xcccccccccccccccd; 0xcccccccccccccccc; 0xcccccccccccccccc; 0xcccccccccccccccc], -258);
  ([0xaaaaaaaaaaaaaaab; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa], -258);
  ([0x9249249249249249; 0x4924924924924924; 0x2492492492492492; 0x9249249249249249], -258);
  ([0x0000000000000000; 0x0000000000000000; 0x0000000000000000; 0x8000000000000000], -258);
  ([0xe38e38e38e38e38e; 0x8e38e38e38e38e38; 0x38e38e38e38e38e3; 0xe38e38e38e38e38e], -259);
  ([0xcccccccccccccccd; 0xcccccccccccccccc; 0xcccccccccccccccc; 0xcccccccccccccccc], -259);
  ([0xe8ba2e8ba2e8ba2f; 0x2e8ba2e8ba2e8ba2; 0xa2e8ba2e8ba2e8ba; 0xba2e8ba2e8ba2e8b], -259);
  ([0xaaaaaaaaaaaaaaab; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa], -259);
  ([0x9d89d89d89d89d8a; 0x89d89d89d89d89d8; 0xd89d89d89d89d89d; 0x9d89d89d89d89d89], -259);
  ([0x9249249249249249; 0x4924924924924924; 0x2492492492492492; 0x9249249249249249], -259);
  ([0x8888888888888889; 0x8888888888888888; 0x8888888888888888; 0x8888888888888888], -259);
  ([0x0000000000000000; 0x0000000000000000; 0x0000000000000000; 0x8000000000000000], -259);
  ([0xf0f0f0f0f0f0f0f1; 0xf0f0f0f0f0f0f0f0; 0xf0f0f0f0f0f0f0f0; 0xf0f0f0f0f0f0f0f0], -260);
  ([0xe38e38e38e38e38e; 0x8e38e38e38e38e38; 0x38e38e38e38e38e3; 0xe38e38e38e38e38e], -260);
  ([0x435e50d79435e50d; 0x5e50d79435e50d79; 0x50d79435e50d7943; 0xd79435e50d79435e], -260);
  ([0xcccccccccccccccd; 0xcccccccccccccccc; 0xcccccccccccccccc; 0xcccccccccccccccc], -260);
  ([0xc30c30c30c30c30c; 0x0c30c30c30c30c30; 0x30c30c30c30c30c3; 0xc30c30c30c30c30c], -260);
  ([0xe8ba2e8ba2e8ba2f; 0x2e8ba2e8ba2e8ba2; 0xa2e8ba2e8ba2e8ba; 0xba2e8ba2e8ba2e8b], -260);
  ([0x42c8590b21642c86; 0x0b21642c8590b216; 0x2c8590b21642c859; 0xb21642c8590b2164], -260);
  ([0xaaaaaaaaaaaaaaab; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa; 0xaaaaaaaaaaaaaaaa], -260);
  ([0x70a3d70a3d70a3d7; 0xd70a3d70a3d70a3d; 0x3d70a3d70a3d70a3; 0xa3d70a3d70a3d70a], -260);
  ([0x9d89d89d89d89d8a; 0x89d89d89d89d89d8; 0xd89d89d89d89d89d; 0x9d89d89d89d89d89], -260);
  ([0x425ed097b425ed09; 0x5ed097b425ed097b; 0xd097b425ed097b42; 0x97b425ed097b425e], -260);
  ([0x9249249249249249; 0x4924924924924924; 0x2492492492492492; 0x9249249249249249], -260);
  ([0x08d3dcb08d3dcb09; 0xcb08d3dcb08d3dcb; 0x3dcb08d3dcb08d3d; 0x8d3dcb08d3dcb08d], -260);
  ([0x8888888888888889; 0x8888888888888888; 0x8888888888888888; 0x8888888888888888], -260);
  ([0x1084210842108421; 0x2108421084210842; 0x4210842108421084; 0x8421084210842108], -260);
  ([0x0000000000000000; 0x0000000000000000; 0x0000000000000000; 0x8000000000000000], -260);
  ([0xe0f83e0f83e0f83e; 0x3e0f83e0f83e0f83; 0x83e0f83e0f83e0f8; 0xf83e0f83e0f83e0f], -261);
  ([0xf0f0f0f0f0f0f0f1; 0xf0f0f0f0f0f0f0f0; 0xf0f0f0f0f0f0f0f0; 0xf0f0f0f0f0f0f0f0], -261);
  ([0xea0ea0ea0ea0ea0f; 0x0ea0ea0ea0ea0ea0; 0xa0ea0ea0ea0ea0ea; 0xea0ea0ea0ea0ea0e], -261);
  ([0xe38e38e38e38e38e; 0x8e38e38e38e38e38; 0x38e38e38e38e38e3; 0xe38e38e38e38e38e], -261);
  ([0x7c8a60dd67c8a60e; 0x8a60dd67c8a60dd6; 0x60dd67c8a60dd67c; 0xdd67c8a60dd67c8a], -261);
  ([0x435e50d79435e50d; 0x5e50d79435e50d79; 0x50d79435e50d7943; 0xd79435e50d79435e], -261);
  ([0xd20d20d20d20d20d; 0x0d20d20d20d20d20; 0x20d20d20d20d20d2; 0xd20d20d20d20d20d], -261);
  ([0xcccccccccccccccd; 0xcccccccccccccccc; 0xcccccccccccccccc; 0xcccccccccccccccc], -261);
  ([0xe0c7ce0c7ce0c7ce; 0xce0c7ce0c7ce0c7c; 0x7ce0c7ce0c7ce0c7; 0xc7ce0c7ce0c7ce0c], -261);
  ([0xc30c30c30c30c30c; 0x0c30c30c30c30c30; 0x30c30c30c30c30c3; 0xc30c30c30c30c30c], -261);
  ([0x0be82fa0be82fa0c; 0xfa0be82fa0be82fa; 0x82fa0be82fa0be82; 0xbe82fa0be82fa0be], -261);
  ([0xe8ba2e8ba2e8ba2f; 0x2e8ba2e8ba2e8ba2; 0xa2e8ba2e8ba2e8ba; 0xba2e8ba2e8ba2e8b], -261);
  ([0xb60b60b60b60b60b; 0x0b60b60b60b60b60; 0x60b60b60b60b60b6; 0xb60b60b60b60b60b], -261)
].

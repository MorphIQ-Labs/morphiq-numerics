(** The binary64 encodings of the Gauss-Legendre rules of the bivariate normal, the
    same values as crates/morphiq-numerics/src/bivariate_normal/tables.rs, written by
    generators/bivariate_normal_nodes.py; do not edit. *)
From Coq Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition gl6_x : list Z := [0x3fedd6ca4e80a01e; 0x3fe528a09655c95e; 0x3fce8b12d03675c5].
Definition gl6_w : list Z := [0x3fc5edf601e2dbf8; 0x3fd716b7b5794c1c; 0x3fddf24d499545e8].
Definition gl8_x : list Z := [0x3feebab1cb0acc67; 0x3fe97e4ab249f41e; 0x3fe0d129583284b4; 0x3fc77ac94f3c7345].
Definition gl8_w : list Z := [0x3fb9ea1d04ca0374; 0x3fcc76fb531d2b96; 0x3fd413c50a255615; 0x3fd736360b199343].
Definition gl12_x : list Z := [0x3fef68f1d8e42e81; 0x3fecee874ffb88b4; 0x3fe8a30aeed88f36; 0x3fe2cb4f05c077f9; 0x3fd78a8d20a8b19d; 0x3fc007a5f8f630e4].
Definition gl12_w : list Z := [0x3fa8275d9dea6d8f; 0x3fbb60602bce6181; 0x3fc47d7258f22d8f; 0x3fca0163e6b1ab72; 0x3fcde3155c256ab5; 0x3fcfe40ce6d4f025].
Definition gl14_x : list Z := [0x3fef8fa30fddab0b; 0x3fedb5bd12b99e9f; 0x3fea786ee46dd9c4; 0x3fe5fe4db09e0c89; 0x3fe07ceab54ef096; 0x3fd46c564912d702; 0x3fbba97d36de76b0].
Definition gl14_w : list Z := [0x3fa1fb2d8b27f553; 0x3fb4853d8adc703d; 0x3fbf1bd74ef611c1; 0x3fc41f3bbee2d2f2; 0x3fc7bfb8e2a8f57e; 0x3fca43f1796fab09; 0x3fcb8dc415514e34].
Definition gl16_w : list Z := [0x3f9bcddab4b7c211; 0x3fafdfb1a2c1265d; 0x3fb85c4ee79cc258; 0x3fbfe7af2bad386a; 0x3fc325f61bca3cbf; 0x3fc5a6ebbb5a75fc; 0x3fc75f8c77e0c00f; 0x3fc83feae80e4dfc].
Definition gl16_xp : list Z := [0x3fefd4a4cca98683; 0x3fef1e8d57d8a84a; 0x3fede2de9aee34b1; 0x3fec34c493f0b683; 0x3fea2d95256a041c; 0x3fe7ea6f407bd7eb; 0x3fe589b0206a4d68; 0x3fe328801d4fc000].
Definition gl16_xm : list Z := [0x3fd02b875fded849; 0x3fd0e62a968eda0d; 0x3fd238dce63d129e; 0x3fd427205b6ac166; 0x3fd6b2b3b0932b25; 0x3fd9d8c24d44f240; 0x3fdd8f081422f432; 0x3fe0e0be5bb4a011].
Definition gl20_x : list Z := [0x3fefc7b5a0c71ce0; 0x3feed8dba7bd769f; 0x3fed31064173fd92; 0x3feada0bd5efd6e7; 0x3fe7e1f37346a54e; 0x3fe45a8d3fa710db; 0x3fe05905c13f7ff7; 0x3fd7eaccf15652c4; 0x3fcd281636928bc0; 0x3fb3973df98b86b0].
Definition gl20_w : list Z := [0x3f9209680274e8af; 0x3fa4c9b5ea53b67f; 0x3fb00b467df7e475; 0x3fb5519fe196e24a; 0x3fba1817a317a821; 0x3fbe41ff31573b48; 0x3fc0db2c5db26dff; 0x3fc230348f34a535; 0x3fc31819b52c5992; 0x3fc38d6c490a3370].
Definition gl24_x : list Z := [0x3fefd892de691982; 0x3fef30f9f0cbf876; 0x3fee06585a70aa4d; 0x3fec5d841864d0f5; 0x3fea3d74ce0d3700; 0x3fe7af18edb9ddd6; 0x3fe4bd2ee5fa1086; 0x3fe17417bac4d72b; 0x3fdbc345d81e24b5; 0x3fd429a8c588e910; 0x3fc8769542b94f8d; 0x3fb0660853eda2e8].
Definition gl24_w : list Z := [0x3f89465bd3112202; 0x3f9d375514486f1d; 0x3fa6ab884f57c979; 0x3fae5c6255d25eda; 0x3fb2c6d5c2eff064; 0x3fb6108ef504463a; 0x3fb8fd8936444b16; 0x3fbb8177ba4a68dc; 0x3fbd91c78acb1b2d; 0x3fbf25cbce1d1ff6; 0x3fc01b7117cf8bd8; 0x3fc060475e763736].
Definition gl15_w : list Z := [0x3f9f7dc7227a291b; 0x3fb2038260b5d026; 0x3fbb6ec9635f1146; 0x3fc1dd73b4963161; 0x3fc5484f30a86ed1; 0x3fc7d41fa76dc267; 0x3fc96633f1fd02ce].
Definition gl15_xp : list Z := [0x3fefcee423f6fc6f; 0x3fef01161aab82c9; 0x3fed9e0d20c3da04; 0x3febbe1963146ab9; 0x3fe980f177e7cf2d; 0x3fe70a5ff5c4037a; 0x3fe47ecb2541debc].
Definition gl15_xm : list Z := [0x3fd031548da19ea6; 0x3fd104f50de1f726; 0x3fd285570e87b7f4; 0x3fd4b68da200c7cc; 0x3fd799c7c94230e5; 0x3fdb296afdc625ec; 0x3fdf5550656a1bb4].
Definition gl15_w0 : Z := 0x3fc9ee1575f9c980.

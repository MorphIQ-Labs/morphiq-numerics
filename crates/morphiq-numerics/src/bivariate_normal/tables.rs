//! Gauss-Legendre rules of the bivariate normal, written by
//! `generators/bivariate_normal_nodes.py`; do not edit. Each rule lists the
//! positive abscissas in descending order and their weights, each rounded
//! once to nearest-even binary64 from the 120-digit root of `P_n`;
//! `docs/bivariate_normal.md` gives the derivation.

/// The 2 positive abscissas of the 4-point rule
pub(super) const GL4_X: [f64; 2] = [
    f64::from_bits(0x3feb8e6dbcf63985),
    f64::from_bits(0x3fd5c23fd9dd3dfc),
];
/// Their weights, summing to 1 over the 2 positive nodes
pub(super) const GL4_W: [f64; 2] = [
    f64::from_bits(0x3fd64340f7e7b66b),
    f64::from_bits(0x3fe4de5f840c24ca),
];
/// The 3 positive abscissas of the 6-point rule
pub(super) const GL6_X: [f64; 3] = [
    f64::from_bits(0x3fedd6ca4e80a01e),
    f64::from_bits(0x3fe528a09655c95e),
    f64::from_bits(0x3fce8b12d03675c5),
];
/// Their weights, summing to 1 over the 3 positive nodes
pub(super) const GL6_W: [f64; 3] = [
    f64::from_bits(0x3fc5edf601e2dbf8),
    f64::from_bits(0x3fd716b7b5794c1c),
    f64::from_bits(0x3fddf24d499545e8),
];
/// The 4 positive abscissas of the 8-point rule
pub(super) const GL8_X: [f64; 4] = [
    f64::from_bits(0x3feebab1cb0acc67),
    f64::from_bits(0x3fe97e4ab249f41e),
    f64::from_bits(0x3fe0d129583284b4),
    f64::from_bits(0x3fc77ac94f3c7345),
];
/// Their weights, summing to 1 over the 4 positive nodes
pub(super) const GL8_W: [f64; 4] = [
    f64::from_bits(0x3fb9ea1d04ca0374),
    f64::from_bits(0x3fcc76fb531d2b96),
    f64::from_bits(0x3fd413c50a255615),
    f64::from_bits(0x3fd736360b199343),
];
/// The 5 positive abscissas of the 10-point rule
pub(super) const GL10_X: [f64; 5] = [
    f64::from_bits(0x3fef2a3e062af2d8),
    f64::from_bits(0x3febae995e9cb2f3),
    f64::from_bits(0x3fe5bdb9228de198),
    f64::from_bits(0x3fdbbcc009016adc),
    f64::from_bits(0x3fc30e507891e27a),
];
/// Their weights, summing to 1 over the 5 positive nodes
pub(super) const GL10_W: [f64; 5] = [
    f64::from_bits(0x3fb1115f8b62dc1f),
    f64::from_bits(0x3fc32138c878efe5),
    f64::from_bits(0x3fcc0b059d00bc31),
    f64::from_bits(0x3fd13baa7a559bfe),
    f64::from_bits(0x3fd2e9de7014d6ef),
];
/// The 6 positive abscissas of the 12-point rule
pub(super) const GL12_X: [f64; 6] = [
    f64::from_bits(0x3fef68f1d8e42e81),
    f64::from_bits(0x3fecee874ffb88b4),
    f64::from_bits(0x3fe8a30aeed88f36),
    f64::from_bits(0x3fe2cb4f05c077f9),
    f64::from_bits(0x3fd78a8d20a8b19d),
    f64::from_bits(0x3fc007a5f8f630e4),
];
/// Their weights, summing to 1 over the 6 positive nodes
pub(super) const GL12_W: [f64; 6] = [
    f64::from_bits(0x3fa8275d9dea6d8f),
    f64::from_bits(0x3fbb60602bce6181),
    f64::from_bits(0x3fc47d7258f22d8f),
    f64::from_bits(0x3fca0163e6b1ab72),
    f64::from_bits(0x3fcde3155c256ab5),
    f64::from_bits(0x3fcfe40ce6d4f025),
];
/// The 7 positive abscissas of the 14-point rule
pub(super) const GL14_X: [f64; 7] = [
    f64::from_bits(0x3fef8fa30fddab0b),
    f64::from_bits(0x3fedb5bd12b99e9f),
    f64::from_bits(0x3fea786ee46dd9c4),
    f64::from_bits(0x3fe5fe4db09e0c89),
    f64::from_bits(0x3fe07ceab54ef096),
    f64::from_bits(0x3fd46c564912d702),
    f64::from_bits(0x3fbba97d36de76b0),
];
/// Their weights, summing to 1 over the 7 positive nodes
pub(super) const GL14_W: [f64; 7] = [
    f64::from_bits(0x3fa1fb2d8b27f553),
    f64::from_bits(0x3fb4853d8adc703d),
    f64::from_bits(0x3fbf1bd74ef611c1),
    f64::from_bits(0x3fc41f3bbee2d2f2),
    f64::from_bits(0x3fc7bfb8e2a8f57e),
    f64::from_bits(0x3fca43f1796fab09),
    f64::from_bits(0x3fcb8dc415514e34),
];
/// The 8 positive abscissas of the 16-point rule
pub(super) const GL16_X: [f64; 8] = [
    f64::from_bits(0x3fefa92c264d787e),
    f64::from_bits(0x3fee39f56616f9b0),
    f64::from_bits(0x3febb3403514e483),
    f64::from_bits(0x3fe82c45dda4726b),
    f64::from_bits(0x3fe3c5a466d5e8b8),
    f64::from_bits(0x3fdd50259a43a772),
    f64::from_bits(0x3fd205cae642337c),
    f64::from_bits(0x3fb852bd6676a9f9),
];
/// Their weights, summing to 1 over the 8 positive nodes
pub(super) const GL16_W: [f64; 8] = [
    f64::from_bits(0x3f9bcddab4b7c211),
    f64::from_bits(0x3fafdfb1a2c1265d),
    f64::from_bits(0x3fb85c4ee79cc258),
    f64::from_bits(0x3fbfe7af2bad386a),
    f64::from_bits(0x3fc325f61bca3cbf),
    f64::from_bits(0x3fc5a6ebbb5a75fc),
    f64::from_bits(0x3fc75f8c77e0c00f),
    f64::from_bits(0x3fc83feae80e4dfc),
];
/// The 10 positive abscissas of the 20-point rule
pub(super) const GL20_X: [f64; 10] = [
    f64::from_bits(0x3fefc7b5a0c71ce0),
    f64::from_bits(0x3feed8dba7bd769f),
    f64::from_bits(0x3fed31064173fd92),
    f64::from_bits(0x3feada0bd5efd6e7),
    f64::from_bits(0x3fe7e1f37346a54e),
    f64::from_bits(0x3fe45a8d3fa710db),
    f64::from_bits(0x3fe05905c13f7ff7),
    f64::from_bits(0x3fd7eaccf15652c4),
    f64::from_bits(0x3fcd281636928bc0),
    f64::from_bits(0x3fb3973df98b86b0),
];
/// Their weights, summing to 1 over the 10 positive nodes
pub(super) const GL20_W: [f64; 10] = [
    f64::from_bits(0x3f9209680274e8af),
    f64::from_bits(0x3fa4c9b5ea53b67f),
    f64::from_bits(0x3fb00b467df7e475),
    f64::from_bits(0x3fb5519fe196e24a),
    f64::from_bits(0x3fba1817a317a821),
    f64::from_bits(0x3fbe41ff31573b48),
    f64::from_bits(0x3fc0db2c5db26dff),
    f64::from_bits(0x3fc230348f34a535),
    f64::from_bits(0x3fc31819b52c5992),
    f64::from_bits(0x3fc38d6c490a3370),
];
/// The 12 positive abscissas of the 24-point rule
pub(super) const GL24_X: [f64; 12] = [
    f64::from_bits(0x3fefd892de691982),
    f64::from_bits(0x3fef30f9f0cbf876),
    f64::from_bits(0x3fee06585a70aa4d),
    f64::from_bits(0x3fec5d841864d0f5),
    f64::from_bits(0x3fea3d74ce0d3700),
    f64::from_bits(0x3fe7af18edb9ddd6),
    f64::from_bits(0x3fe4bd2ee5fa1086),
    f64::from_bits(0x3fe17417bac4d72b),
    f64::from_bits(0x3fdbc345d81e24b5),
    f64::from_bits(0x3fd429a8c588e910),
    f64::from_bits(0x3fc8769542b94f8d),
    f64::from_bits(0x3fb0660853eda2e8),
];
/// Their weights, summing to 1 over the 12 positive nodes
pub(super) const GL24_W: [f64; 12] = [
    f64::from_bits(0x3f89465bd3112202),
    f64::from_bits(0x3f9d375514486f1d),
    f64::from_bits(0x3fa6ab884f57c979),
    f64::from_bits(0x3fae5c6255d25eda),
    f64::from_bits(0x3fb2c6d5c2eff064),
    f64::from_bits(0x3fb6108ef504463a),
    f64::from_bits(0x3fb8fd8936444b16),
    f64::from_bits(0x3fbb8177ba4a68dc),
    f64::from_bits(0x3fbd91c78acb1b2d),
    f64::from_bits(0x3fbf25cbce1d1ff6),
    f64::from_bits(0x3fc01b7117cf8bd8),
    f64::from_bits(0x3fc060475e763736),
];

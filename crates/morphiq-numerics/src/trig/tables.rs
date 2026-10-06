//! Constants of `sin` and `cos`, written by `generators/trig_constants.py`; do
//! not edit. `docs/sin_cos.md` gives the derivation.

/// `(sin t − t)/t³ ≈ Ps(t²)` (`generators/trig_poly.sollya`): relative error at most
/// 0x1.000002p-54 on `|t| <= 0.0078126`.
pub(super) const POLY_S: [f64; 3] = [
    f64::from_bits(0xbfc5555555555555),
    f64::from_bits(0x3f811111110bb1a8),
    f64::from_bits(0xbf2a0159d0d83966),
];
/// `(cos t − 1 + t²/2)/t⁴ ≈ Pc(t²)`: relative error at most
/// 0x1.000002p-54 on `|t| <= 0.0078126`.
pub(super) const POLY_C: [f64; 3] = [
    f64::from_bits(0x3fa5555555555555),
    f64::from_bits(0xbf56c16c16b6b967),
    f64::from_bits(0x3efa0115f5073e76),
];
/// `(sin(i/64), cos(i/64))`, each a double-word `(hi, lo)` as binary64 encodings;
/// relative error below 2^-107.1.
pub(super) const TABLE: [[(u64, u64); 2]; 51] = [
    [
        (0x0000000000000000, 0x0000000000000000),
        (0x3ff0000000000000, 0x0000000000000000),
    ],
    [
        (0x3f8fffaaaaeeeed5, 0xbc02ab639a9f0776),
        (0x3fefff000155549f, 0x3c828a28a03a5ef3),
    ],
    [
        (0x3f9ffeaaaeeee86f, 0xbc3cd406fb224ae2),
        (0x3feffc00155527d3, 0xbc83b54492d89b5b),
    ],
    [
        (0x3fa7fdc01032fba9, 0xbc4599bdf46e997a),
        (0x3feff7006bfdf99f, 0xbc78b3b560648d5f),
    ],
    [
        (0x3faffaaaeeed4edb, 0xbc42d16d32684b69),
        (0x3feff0015549f4d3, 0x3c8328387b99426f),
    ],
    [
        (0x3fb3facb12d1755b, 0xbc5921915299468b),
        (0x3fefe7034129ef6f, 0xbc6cbf4337c96f97),
    ],
    [
        (0x3fb7f701032550e4, 0x3c3afc2d1800501a),
        (0x3fefdc06bf7e6b9b, 0x3c831902b535f8db),
    ],
    [
        (0x3fbbf1b78568391d, 0x3c5e91841dea4cc8),
        (0x3fefcf0c800e99b1, 0x3c6ea3d786d186ac),
    ],
    [
        (0x3fbfeaaeee86ee36, 0xbc4afcb2bcc6f03b),
        (0x3fefc015527d5bd3, 0x3c8b68f35094efb8),
    ],
    [
        (0x3fc1f0d3d7afceaf, 0xbc66ef95099769a5),
        (0x3fefaf22263c4bd3, 0xbc552ace133a2769),
    ],
    [
        (0x3fc3eb312c5d66cb, 0x3c647d666b66cb91),
        (0x3fef9c340a7cc428, 0x3c8c5b6b063b7462),
    ],
    [
        (0x3fc5e44fcfa126f3, 0xbc66f443063f89b6),
        (0x3fef874c2e1eecf6, 0xbc8c6514e1332b16),
    ],
    [
        (0x3fc7dc102fbaf2b5, 0x3c45ab50e23c97c3),
        (0x3fef706bdf9ece1c, 0xbc8698c80c36dcb4),
    ],
    [
        (0x3fc9d252d0cec312, 0x3c59c43d80b1137d),
        (0x3fef57948cff6797, 0x3c6e3a0d3e03b1d4),
    ],
    [
        (0x3fcbc6f84edc6199, 0x3c69c1a56a7b0cab),
        (0x3fef3cc7c3b3d16e, 0xbc621a3ad28a3494),
    ],
    [
        (0x3fcdb9e15fb5a5d0, 0xbc632e20d6cc6fc2),
        (0x3fef20073086649f, 0x3c7b940416c1984b),
    ],
    [
        (0x3fcfaaeed4f31577, 0xbc615d88508e32b8),
        (0x3fef01549f7deea1, 0x3c8d3c1e99e5cafd),
    ],
    [
        (0x3fd0cd00cef36436, 0xbc79fb0a0c93e2b4),
        (0x3feee0b1fbc0f11c, 0xbc4bfd2380bbc3b1),
    ],
    [
        (0x3fd1c37d64c6b876, 0x3c746076fe0dcff4),
        (0x3feebe214f76efa8, 0xbc802f9f12ba543e),
    ],
    [
        (0x3fd2b8ddc43eb49f, 0x3c61553899f2d807),
        (0x3fee99a4c3a7cd83, 0xbc82264b1bc53ce8),
    ],
    [
        (0x3fd3ad129769d3d8, 0x3c003d550487839a),
        (0x3fee733ea0193d40, 0xbc86428b3546ce13),
    ],
    [
        (0x3fd4a00c9b0f3d20, 0x3c7823ba6bb08ead),
        (0x3fee4af14b2a449c, 0xbc868ca02e8a6833),
    ],
    [
        (0x3fd591bc9fa2f597, 0x3c67c74bac3fe0cb),
        (0x3fee20bf49acd6c1, 0xbc5660aec7ef636b),
    ],
    [
        (0x3fd682138a38d7f7, 0xbc7d889202444aad),
        (0x3fedf4ab3ebd875e, 0xbc8e2d8a7e6736c4),
    ],
    [
        (0x3fd7710255764214, 0xbc66ead7314bb6ce),
        (0x3fedc6b7eb995912, 0x3c54b364776dcd35),
    ],
    [
        (0x3fd85e7a12826949, 0x3c78a40e9b5face0),
        (0x3fed96e82f71a9dc, 0x3c8ff61bd5d2039d),
    ],
    [
        (0x3fd94a6be9f546c5, 0xbc769ce13e683f58),
        (0x3fed653f073e4040, 0xbc876236434bec37),
    ],
    [
        (0x3fda34c91cc50cca, 0xbc5a310e3b50cecd),
        (0x3fed31bf8d8d7c06, 0x3c7e60dd3089cbdd),
    ],
    [
        (0x3fdb1d8305321617, 0xbc7ae242cb99f519),
        (0x3fecfc6cfa52ad9f, 0x3c88b5b5508f2a0d),
    ],
    [
        (0x3fdc048b17b140a3, 0x3c619fe6757e9fa7),
        (0x3fecc54aa2b2972e, 0x3c64ee162ba83a98),
    ],
    [
        (0x3fdce9d2e3d4a51f, 0xbc62fc8a12dae298),
        (0x3fec8c5bf8ce1a84, 0x3c7ab3d1a1590123),
    ],
    [
        (0x3fddcd4c15329c9a, 0x3c70d4c6e171fd9a),
        (0x3fec51a48b8b175e, 0xbc61bbb43b9aa880),
    ],
    [
        (0x3fdeaee8744b05f0, 0xbc5789b43c9b027d),
        (0x3fec1528065b7d50, 0xbc8892111312e828),
    ],
    [
        (0x3fdf8e99e76abc97, 0x3c59d950af2d00a3),
        (0x3febd6ea310294f5, 0x3c731bbcc88c109d),
    ],
    [
        (0x3fe0362939c69955, 0xbc82d8cd78397b01),
        (0x3feb96eeef58840e, 0x3c545a3cc78fade0),
    ],
    [
        (0x3fe0a4021e9e1001, 0xbc86f643a13914f6),
        (0x3feb553a410c104e, 0x3c58ff7947027a15),
    ],
    [
        (0x3fe110d0c4b69c3b, 0x3c8d918998809981),
        (0x3feb11d04162a4c6, 0x3c71dd561efbc0c2),
    ],
    [
        (0x3fe17c8e5f2eedb0, 0x3c635e57102e2488),
        (0x3feaccb526f69de5, 0x3c88fb6a8dd6b6cc),
    ],
    [
        (0x3fe1e7343236574c, 0x3c722a3fa4f41d5a),
        (0x3fea85ed4373e02d, 0x3c69be06385ec792),
    ],
    [
        (0x3fe250bb93788bbb, 0x3c7ea3d02457bcce),
        (0x3fea3d7d0352bdcf, 0xbc868dbaeca19669),
    ],
    [
        (0x3fe2b91dea88421e, 0xbc8fa371db216ab0),
        (0x3fe9f368ed912f85, 0xbc81d200c5791606),
    ],
    [
        (0x3fe32054b148bc4f, 0x3c8f6b42095a135b),
        (0x3fe9a7b5a36a6514, 0x3c8722cfcc9fa7a9),
    ],
    [
        (0x3fe386597456282b, 0xbc710fada93b07a8),
        (0x3fe95a67e00cb1fd, 0xbc80befda21f862d),
    ],
    [
        (0x3fe3eb25d36cd53a, 0xbc5be570e1570fc0),
        (0x3fe90b84784ddaf7, 0xbc70feb10ab93b87),
    ],
    [
        (0x3fe44eb381cf386b, 0xbc83ed6c1e6a5505),
        (0x3fe8bb105a5dc900, 0x3c8863e03e9474c1),
    ],
    [
        (0x3fe4b0fc46aab761, 0x3c20da05738cc59c),
        (0x3fe869108d77a6c6, 0x3c7338ffe2bfe9dd),
    ],
    [
        (0x3fe511f9fd7b351c, 0xbc85c0e861c48831),
        (0x3fe8158a31916d5d, 0xbc6de8b90b8228de),
    ],
    [
        (0x3fe571a6966d59b3, 0x3c5c843b4d0fb197),
        (0x3fe7c0827f09e54f, 0xbc6c73d6d72aee68),
    ],
    [
        (0x3fe5cffc16bf8f0d, 0x3c896cb370eb578a),
        (0x3fe769fec655211f, 0xbc6827d5cf8c68c5),
    ],
    [
        (0x3fe62cf49921ac79, 0xbc8edd9855b6241a),
        (0x3fe712046fa77678, 0x3c8425b0a5029c81),
    ],
    [
        (0x3fe6888a4e134b2f, 0xbc86b7d37644d5e6),
        (0x3fe6b898fa9efb5d, 0x3c715ac786ccf4b2),
    ],
];
/// `1/((2n)(2n+1))`, `n = 1..=22`, as `(m, e)`: four limbs least significant
/// first, value `m 2^e`; relative error below 2^-256.2.
pub(super) const SIN_STEPS: [([u64; 4], i32); 22] = [
    (
        [
            0xaaaaaaaaaaaaaaab,
            0xaaaaaaaaaaaaaaaa,
            0xaaaaaaaaaaaaaaaa,
            0xaaaaaaaaaaaaaaaa,
        ],
        -258,
    ),
    (
        [
            0xcccccccccccccccd,
            0xcccccccccccccccc,
            0xcccccccccccccccc,
            0xcccccccccccccccc,
        ],
        -260,
    ),
    (
        [
            0xc30c30c30c30c30c,
            0x0c30c30c30c30c30,
            0x30c30c30c30c30c3,
            0xc30c30c30c30c30c,
        ],
        -261,
    ),
    (
        [
            0xe38e38e38e38e38e,
            0x8e38e38e38e38e38,
            0x38e38e38e38e38e3,
            0xe38e38e38e38e38e,
        ],
        -262,
    ),
    (
        [
            0x2094f2094f2094f2,
            0xf2094f2094f2094f,
            0x4f2094f2094f2094,
            0x94f2094f2094f209,
        ],
        -262,
    ),
    (
        [
            0xd20d20d20d20d20d,
            0x0d20d20d20d20d20,
            0x20d20d20d20d20d2,
            0xd20d20d20d20d20d,
        ],
        -263,
    ),
    (
        [
            0x9c09c09c09c09c0a,
            0x09c09c09c09c09c0,
            0xc09c09c09c09c09c,
            0x9c09c09c09c09c09,
        ],
        -263,
    ),
    (
        [
            0xf0f0f0f0f0f0f0f1,
            0xf0f0f0f0f0f0f0f0,
            0xf0f0f0f0f0f0f0f0,
            0xf0f0f0f0f0f0f0f0,
        ],
        -264,
    ),
    (
        [
            0x02fe80bfa02fe80c,
            0xfe80bfa02fe80bfa,
            0x80bfa02fe80bfa02,
            0xbfa02fe80bfa02fe,
        ],
        -264,
    ),
    (
        [
            0x9c09c09c09c09c0a,
            0x09c09c09c09c09c0,
            0xc09c09c09c09c09c,
            0x9c09c09c09c09c09,
        ],
        -264,
    ),
    (
        [
            0x5f1d58081848da90,
            0x36a3ebc349dd98ca,
            0x663297c756020612,
            0x81848da8faf0d277,
        ],
        -264,
    ),
    (
        [
            0x40da740da740da74,
            0x740da740da740da7,
            0xa740da740da740da,
            0xda740da740da740d,
        ],
        -265,
    ),
    (
        [
            0x656100bab656100c,
            0x6100bab656100bab,
            0x00bab656100bab65,
            0xbab656100bab6561,
        ],
        -265,
    ),
    (
        [
            0x2ea8fc377cd8e80a,
            0xc377cd8e80a16b31,
            0xd8e80a16b312ea8f,
            0xa16b312ea8fc377c,
        ],
        -265,
    ),
    (
        [
            0x008cf008cf008cf0,
            0xf008cf008cf008cf,
            0xcf008cf008cf008c,
            0x8cf008cf008cf008,
        ],
        -265,
    ),
    (
        [
            0xe0f83e0f83e0f83e,
            0x3e0f83e0f83e0f83,
            0x83e0f83e0f83e0f8,
            0xf83e0f83e0f83e0f,
        ],
        -266,
    ),
    (
        [
            0xdc4a00dc4a00dc4a,
            0x4a00dc4a00dc4a00,
            0x00dc4a00dc4a00dc,
            0xdc4a00dc4a00dc4a,
        ],
        -266,
    ),
    (
        [
            0xe07b00c4ce07b00c,
            0x7b00c4ce07b00c4c,
            0x00c4ce07b00c4ce0,
            0xc4ce07b00c4ce07b,
        ],
        -266,
    ),
    (
        [
            0x2a2600b0e2a2600b,
            0x2600b0e2a2600b0e,
            0x00b0e2a2600b0e2a,
            0xb0e2a2600b0e2a26,
        ],
        -266,
    ),
    (
        [
            0x809fd809fd809fd8,
            0xd809fd809fd809fd,
            0xfd809fd809fd809f,
            0x9fd809fd809fd809,
        ],
        -266,
    ),
    (
        [
            0xe4802449b5b92009,
            0x449b5b92009126d6,
            0xb92009126d6e4802,
            0x9126d6e4802449b5,
        ],
        -266,
    ),
    (
        [
            0x55d9bab2f1008465,
            0x655d9bab2f100846,
            0x4655d9bab2f10084,
            0x84655d9bab2f1008,
        ],
        -266,
    ),
];
/// `1/((2n−1)(2n))`, `n = 1..=23`, likewise.
pub(super) const COS_STEPS: [([u64; 4], i32); 23] = [
    (
        [
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
            0x8000000000000000,
        ],
        -256,
    ),
    (
        [
            0xaaaaaaaaaaaaaaab,
            0xaaaaaaaaaaaaaaaa,
            0xaaaaaaaaaaaaaaaa,
            0xaaaaaaaaaaaaaaaa,
        ],
        -259,
    ),
    (
        [
            0x8888888888888889,
            0x8888888888888888,
            0x8888888888888888,
            0x8888888888888888,
        ],
        -260,
    ),
    (
        [
            0x9249249249249249,
            0x4924924924924924,
            0x2492492492492492,
            0x9249249249249249,
        ],
        -261,
    ),
    (
        [
            0xb60b60b60b60b60b,
            0x0b60b60b60b60b60,
            0x60b60b60b60b60b6,
            0xb60b60b60b60b60b,
        ],
        -262,
    ),
    (
        [
            0xe0f83e0f83e0f83e,
            0x3e0f83e0f83e0f83,
            0x83e0f83e0f83e0f8,
            0xf83e0f83e0f83e0f,
        ],
        -263,
    ),
    (
        [
            0xb40b40b40b40b40b,
            0x0b40b40b40b40b40,
            0x40b40b40b40b40b4,
            0xb40b40b40b40b40b,
        ],
        -263,
    ),
    (
        [
            0x8888888888888889,
            0x8888888888888888,
            0x8888888888888888,
            0x8888888888888888,
        ],
        -263,
    ),
    (
        [
            0xd62b80d62b80d62c,
            0x2b80d62b80d62b80,
            0x80d62b80d62b80d6,
            0xd62b80d62b80d62b,
        ],
        -264,
    ),
    (
        [
            0x691840ac7691840b,
            0x1840ac7691840ac7,
            0x40ac7691840ac769,
            0xac7691840ac76918,
        ],
        -264,
    ),
    (
        [
            0xa520237694808dda,
            0xda520237694808dd,
            0xdda520237694808d,
            0x8dda520237694808,
        ],
        -264,
    ),
    (
        [
            0x03b5cc0ed7303b5d,
            0x0ed7303b5cc0ed73,
            0x3b5cc0ed7303b5cc,
            0xed7303b5cc0ed730,
        ],
        -265,
    ),
    (
        [
            0x633fcd967300c9a6,
            0xa633fcd967300c9a,
            0x9a633fcd967300c9,
            0xc9a633fcd967300c,
        ],
        -265,
    ),
    (
        [
            0x02b580ad602b580b,
            0xb580ad602b580ad6,
            0x80ad602b580ad602,
            0xad602b580ad602b5,
        ],
        -265,
    ),
    (
        [
            0x096a850096a85009,
            0x50096a850096a850,
            0xa850096a850096a8,
            0x96a850096a850096,
        ],
        -265,
    ),
    (
        [
            0x1084210842108421,
            0x2108421084210842,
            0x4210842108421084,
            0x8421084210842108,
        ],
        -265,
    ),
    (
        [
            0x00e9a3d25e00e9a4,
            0xa3d25e00e9a3d25e,
            0x5e00e9a3d25e00e9,
            0xe9a3d25e00e9a3d2,
        ],
        -266,
    ),
    (
        [
            0xd00d00d00d00d00d,
            0x0d00d00d00d00d00,
            0x00d00d00d00d00d0,
            0xd00d00d00d00d00d,
        ],
        -266,
    ),
    (
        [
            0x258200ba7258200c,
            0x8200ba7258200ba7,
            0x00ba7258200ba725,
            0xba7258200ba72582,
        ],
        -266,
    ),
    (
        [
            0xa80a80a80a80a80b,
            0x0a80a80a80a80a80,
            0x80a80a80a80a80a8,
            0xa80a80a80a80a80a,
        ],
        -266,
    ),
    (
        [
            0xb773a92e1600983b,
            0x3b773a92e1600983,
            0x83b773a92e160098,
            0x983b773a92e16009,
        ],
        -266,
    ),
    (
        [
            0x65c022a37347fbac,
            0x7008a8dcd1feeae4,
            0x022a37347fbab919,
            0x8a8dcd1feeae465c,
        ],
        -266,
    ),
    (
        [
            0xd0c1eaba7f226174,
            0x0fd477b6c956529c,
            0x0c1eaba7f2261740,
            0xfd477b6c956529cd,
        ],
        -267,
    ),
];

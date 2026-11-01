# Third-party notices

## MorphIQ Risk Thomas recurrence

- Project: MorphIQ Risk (MorphIQ Labs), commit `100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c`.
- Original source: <https://api.github.com/repositories/1321813529/contents/src/numerics/tridiag.rs?ref=100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c>.
  The source link uses GitHub's repository ID so it does not depend on the project name.
- SHA-256 of the complete original `src/numerics/tridiag.rs`:
  `ddd8e947454ecc0bf867d49442f81d518368ca152997cb487894083c1ac177e8`.
- License at that commit: MIT; reproduced below without changes.
- Derived library files: `src/linalg/tridiagonal.rs` and
  `src/linalg/tridiagonal/lanes.rs`.
- The unpublished workspace benchmark `crates/reference/src/bin/bench-tridiagonal.rs`
  also adapts the recurrence, retaining the historical tiny-pivot threshold.
- Changes: split factorization from RHS elimination/substitution; compact
  off-diagonal storage; engine-independent errors; checked strict-dominance
  admission; finite arithmetic checks; no absolute tiny-pivot cutoff;
  immutable factor lifetimes; optional outward residual/error certificate;
  row-interleaved batched solves with the same recurrence in independent SIMD lanes.
- Only the recurrence from this public historical version is adapted. Later
  private source, diagnostics, fixtures and tests are not included.

```text
MIT License

Copyright (c) 2026 MorphIQ Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

The checked sign-domain API shares the same adapted recurrence and SIMD kernel.
Its sign admission and residual-only certificate separation are local additions;
no additional external implementation source is incorporated.

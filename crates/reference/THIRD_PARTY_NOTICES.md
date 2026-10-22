# Unpublished reciprocal tridiagonal experiment

The recurrence and safe SIMD transcription in
`src/bin/tridiagonal_reciprocal/{mod,lanes}.rs` adapt the library implementation
at `83c7b06808baef7a44ef5c1bb8b8eed8de6fe6d2`. That implementation derives from
the public MIT FerroRisk source at
`100880f67b9da1c66e9a9d03ba9e1a5ad876eb5c`, source SHA-256
`ddd8e947454ecc0bf867d49442f81d518368ca152997cb487894083c1ac177e8`.
The experiment precomputes reciprocal pivots, multiplies in the forward sweep,
and retains division for unavailable finite reciprocals. It preserves the
original factorization and back substitution. No later private consumer code
or fixtures are included.

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

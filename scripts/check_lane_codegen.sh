#!/usr/bin/env sh
# Fails when a lane kernel calls an AVX2 or AVX-512F operation out of line
# (docs/lanes.md §7). Each backend operation is a `#[target_feature]` helper
# that inlines only into code compiled with the backend's features, inside
# `Simd::vectorize`. Code outside that wrapper, such as an `#[inline(never)]`
# cold path, still returns the scalar bits, so no test sees it, but every lane
# operation becomes a call: before this check, `ln`'s and `ln_1p`'s fallbacks
# made about 200 such calls per chunk and ran 4-7x slower than SSE2 there.
#
#   scripts/check_lane_codegen.sh [BINARY]
#
# Without BINARY, builds the release library tests (every kernel on every x86
# backend) and disassembles them; test functions are not checked. The only
# calls allowed are the store and load at `lanes::cold` and the scalar-only
# prefix `ln::lanes::finish_ln_1p`, to enter and leave the vector wrapper.
# Exit 1 on a violation, 2 when the check cannot run or the
# binary has no AVX2 or AVX-512F kernels to check. x86-64 only; needs objdump.
set -eu
cd "$(dirname "$0")/.."
command -v objdump >/dev/null || { echo "objdump is required" >&2; exit 2; }
if [ $# -ge 1 ]; then
    binary=$1
else
    binary=$(cargo test --locked --release -p morphiq-numerics --features simd,std --lib --no-run \
        --message-format=json 2>/dev/null | python3 -I -c '
import json, sys
for line in sys.stdin:
    m = json.loads(line)
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "morphiq_numerics":
        print(m["executable"])')
fi
[ -f "$binary" ] || { echo "no test binary: '$binary'" >&2; exit 2; }
objdump -d --no-show-raw-insn -C "$binary" | awk '
    /^[0-9a-f]+ <.*>:$/ {
        fn = $0; sub(/^[0-9a-f]+ </, "", fn); sub(/>:$/, "", fn)
        if (fn ~ /^morphiq_numerics_arch::x86_64::avx2_run(::)?</) avx2++
        if (fn ~ /^morphiq_numerics_arch::x86_64::avx512_run(::)?</) avx512++
        next
    }
    /call.*helpers::(avx2|avx512)::/ {
        if (fn ~ /::tests::/) next
        if (fn ~ /^morphiq_numerics::(lanes::cold|ln::lanes::finish_ln_1p)(::)?</ && /helpers::(avx2|avx512)::(load|store)>/) next
        bad[fn]++
    }
    END {
        if (!avx2 || !avx512) { print "no AVX2 or AVX-512F kernels in the binary" > "/dev/stderr"; exit 2 }
        n = 0
        for (f in bad) { printf "%5d out-of-line lane operations in %s\n", bad[f], f; n++ }
        if (n) exit 1
        printf "lane codegen: %d AVX2 and %d AVX-512F kernels, no out-of-line lane operations\n", avx2, avx512
    }'

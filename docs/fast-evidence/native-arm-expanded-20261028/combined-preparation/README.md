# Combined ARM qualification preparation

The owner requested the final ARM qualification. At preparation time, #240 still points to `ec1eb1c`, explicitly marked intermediate in #194. This packet records completed independent preparation on combined source `c9cb6814a2c693f3ea4835e6ab27e7da8dba7b6a`. **No timed qualification campaign has started in this directory.** Its stable-source dependency remains explicit.

All 64,496 retained independent 256-bit oracle cases pass unchanged error bounds with no scalar/slice mismatches. Maximum observed relative errors: exp 3.0793794411e-16, erfcx 2.8432637882e-16; CDF maximum absolute error 3.9085126779e-16. Historical x86 bits change for 12,021 exp and 983 CDF cases, and zero erfcx cases, following the deliberate arithmetic change. This is not a same-source cross-target check; matching final-source x86 observations are still needed.

All 16,116 expanded-bank cases pass. A separately rebuilt allocation/strong-observation wrapper against the combined checkout records zero allocations across 156 cases, 211 matching fallback observations, and passing composition/dependency-chain checks. Source/binary/input hashes and actual native composition dependency were checked before any timing. Source manifest and original outputs/scripts are retained.

The 163-cell matrix, 125 required classifications and confidence rule are unchanged. Exp slice lengths 14/15/16 join the previous 21 critical cells, followed by 139 remaining cells. The original short-screen anomaly and longer diagnostic observations remain in the sibling integration-screen packet. No threshold or acceptance rule was weakened.

Once the shared qualification SHA is established, use the frozen protocol in a new or still-unused matching-source run directory. If the source changes, rebuild and regenerate the relevant observations; do not relabel this packet. Use the pinned Python venv and run freeze-manifest.py before launching run-qualified.py. Full CI remains on GitHub. This packet contains neither a performance acceptance decision nor a release readiness claim.

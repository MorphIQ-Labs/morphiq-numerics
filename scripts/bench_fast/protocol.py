"""Calibration and decisions shared by the native runners; no native imports."""
import math

MINIMUM_NS = 250_000_000
TARGET_NS = 600_000_000
PROCESSES = 10
ROUNDS = 2
T9_ONE_SIDED_95 = 1.8331129326536335


def calibrate(measure, record, target_ns=TARGET_NS):
    """Find counts from this host, retaining every attempt; never reduce counts.

    Three pilots must each last at least 100ms. A pause/contention cannot reduce
    counts; the fastest pilot determines the target. The confirmation can raise
    counts again. Bounded search fails explicitly instead of silently accepting
    unusable calibration. Later measured durations are checked independently.
    """
    count = 1000
    for attempt in range(10):
        warm = measure(max(1, count//2))
        record('calibration-warmup', max(1, count//2), warm)
        pilots = []
        for _ in range(3):
            elapsed = measure(count)
            if elapsed <= 0:
                raise ValueError('Timer returned nonpositive elapsed time')
            record('calibration-pilot', count, elapsed)
            pilots.append(elapsed)
        fastest = min(pilots)
        if fastest >= 100_000_000:
            count = max(count, math.ceil(count*target_ns/fastest))
            elapsed = measure(count)
            record('calibration-confirmation', count, elapsed)
            if elapsed <= 0:
                raise ValueError('Timer returned nonpositive confirmation')
            return max(count, math.ceil(count*target_ns/elapsed))
        count = max(count+1, math.ceil(count*100_000_000/fastest))
        if count > 2**63-1:
            raise ValueError('Calibration iteration count overflows timer interface')
    raise RuntimeError('Calibration did not reach stable pilot duration; retain output and investigate')

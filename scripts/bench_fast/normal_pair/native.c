// Black-box system-libm comparison; no libm implementation source is used.
#define _GNU_SOURCE
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <time.h>
#include <string.h>
#ifdef __APPLE__
#include <pthread/qos.h>
// Apple's public combined sine/cosine entry; system libm is a black box.
#define sincos __sincos
int bench_set_qos(void) {
    return pthread_set_qos_class_self_np(QOS_CLASS_USER_INITIATED, 0);
}
#endif

typedef struct { double x, y; } pair;
typedef pair (*pair_fn)(uint64_t, uint64_t);

static double unit_open(uint64_t word) {
    return (double)((word >> 12) * 2 + 1) * 0x1p-53;
}

// Same words, uniform map, and octant fold as the strong and candidate pairs.
pair libm_folded(uint64_t w1, uint64_t w2) {
    double radius = sqrt(-2 * log(unit_open(w1)));
    uint64_t k = w2 >> 11, octant = k >> 50, j = k & ((1ULL << 50) - 1);
    uint64_t m = octant & 1 ? (1ULL << 50) - j : j;
    double phi = 0x1.921fb54442d18p+2 * ((double)m * 0x1p-53), s, c;
    sincos(phi, &s, &c);
    if ((octant + 1) & 2) { double t = c; c = s; s = t; }
    if (octant >= 2 && octant <= 5) c = -c;
    if (octant >= 4) s = -s;
    return (pair){radius * c, radius * s};
}

// Textbook full-angle libm Box–Muller, using the same unit map for paired
// inputs. The engine's zero-rejection uniform map is a separate stream contract.
pair libm_direct(uint64_t w1, uint64_t w2) {
    double radius = sqrt(-2 * log(unit_open(w1))), s, c;
    double theta = 0x1.921fb54442d18p+2 * ((double)(w2 >> 11) * 0x1p-53);
    sincos(theta, &s, &c);
    return (pair){radius * c, radius * s};
}

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000ULL + t.tv_nsec;
}

// Fixed bank: independent pair-call throughput. Every output is stored, with
// the same function-pointer/FFI interface for all implementations.
uint64_t measure(pair_fn f, const uint64_t *words, pair *out, size_t n, uint64_t rounds) {
    uint64_t start = now_ns();
    for (uint64_t r = 0; r < rounds; r++) {
        for (size_t i = 0; i < n; i++) out[i] = f(words[2*i], words[2*i+1]);
        __asm__ volatile("" : : "r"(out) : "memory");
    }
    return now_ns() - start;
}

// Finite previous outputs cancel to +0, retaining a dependency into the next
// call without changing input bits. Strict FP compilation must retain the
// subtraction because the opaque callee could return NaN. Observation and
// the numerical contracts establish finite outputs for these inputs.
uint64_t measure_chain(pair_fn f, const uint64_t *words, pair *out, size_t n, uint64_t rounds) {
    double previous = 0;
    uint64_t start = now_ns();
    for (uint64_t r = 0; r < rounds; r++) {
        for (size_t i = 0; i < n; i++) {
            double cancelled = previous - previous;
            uint64_t zero;
            memcpy(&zero, &cancelled, sizeof zero);
            out[i] = f(words[2*i] ^ zero, words[2*i+1]);
            previous = out[i].x;
        }
        __asm__ volatile("" : : "r"(out) : "memory");
    }
    return now_ns() - start;
}

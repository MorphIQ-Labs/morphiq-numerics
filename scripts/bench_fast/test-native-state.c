/* Native timer regression witness, not a performance workload. Build with
 * -mavx -mno-vzeroupper so the test caller deliberately leaves dirty state. */
#include <immintrin.h>
#include <stddef.h>
#include <stdint.h>

static unsigned dirty_seen;
static size_t calls;

static void observe(void) {
    __m128i upper;
    __asm__ volatile("vextractf128 $1, %%ymm15, %0" : "=x"(upper));
    dirty_seen |= _mm_movemask_epi8(upper) != 0;
    calls++;
}

double probe1(double x) { observe(); return x + 1; }
double probe2(double x, int skip) { observe(); return x + skip; }
void probe_packet(const double *x, double *y, size_t n) {
    observe();
    for (size_t i = 0; i < n; i++) y[i] = x[i] + 1;
}
unsigned probe_dirty_seen(void) { return dirty_seen; }
size_t probe_calls(void) { return calls; }

typedef uint64_t (*timer)(void *, const double *, double *, size_t, uint64_t);
typedef uint64_t (*cache_timer)(void *, const double *, double *, size_t, uint64_t, size_t);
void invoke_dirty(void *measure, void *callback, const double *x, double *y,
                  size_t n, uint64_t count, size_t slots) {
    dirty_seen = 0;
    calls = 0;
    __asm__ volatile("vpcmpeqd %%ymm15, %%ymm15, %%ymm15" ::: "ymm15");
    if (slots)
        ((cache_timer)measure)(callback, x, y, n, count, slots);
    else
        ((timer)measure)(callback, x, y, n, count);
}

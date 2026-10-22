/* Unpublished diagnostic harness for reference LAPACK 3.12.1 DGTTRF/DGTTRS.
 * Compile against the pinned reference Fortran routines, not an unrecorded
 * vendor BLAS. No implementation source is copied here. DGTTRF overwrites its
 * factors; DGTTRS overwrites its RHS, so the measured copies are intentional.
 * Usage: bench-lapack n ordinary|mixed|near factor|solve|group calls rhs_count
 */
#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <float.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern void dgttrf_(const int *, double *, double *, double *, double *, int *, int *);
extern void dgttrs_(const char *, const int *, const int *, const double *, const double *,
                   const double *, const double *, const int *, double *, const int *, int *, size_t);

static uint64_t now(void) {
    struct timespec t;
    assert(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
    return (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
}

int main(int argc, char **argv) {
    assert(argc == 7);
    int n = atoi(argv[1]), one = 1, info = 0, rhs_count = atoi(argv[6]);
    size_t calls = strtoull(argv[5], NULL, 10);
    assert(n > 0 && calls > 0 && rhs_count > 0);
    /* Allocate all work before timing; minimum one element for n=1/2. */
    double *a = calloc((size_t)n * 8, sizeof(double));
    int *ipiv = calloc((size_t)n, sizeof(int));
    assert(a && ipiv);
    double *l = a, *d = l+n, *u = d+n, *l0 = u+n, *d0 = l0+n;
    double *u0 = d0+n, *du2 = u0+n, *rhs = du2+n;
    double *b = calloc((size_t)n, sizeof(double));
    assert(b);
    for (int i = 0; i < n; i++) {
        l0[i] = -1.0;
        u0[i] = strcmp(argv[2], "mixed") == 0 && i % 2 == 0 ? 1.0 : -1.0;
        d0[i] = strcmp(argv[2], "near") == 0 ? 2.0 + DBL_EPSILON * 4.0 : 4.0;
        rhs[i] = (double)(i % 13);
    }
    size_t bytes = (size_t)n * sizeof(double);
    memcpy(l, l0, bytes); memcpy(d, d0, bytes); memcpy(u, u0, bytes);
    dgttrf_(&n, l, d, u, du2, ipiv, &info); assert(info == 0);
    int factor_only = strcmp(argv[3], "factor") == 0;
    int solve_only = strcmp(argv[3], "solve") == 0;
    assert(factor_only || solve_only || strcmp(argv[3], "group") == 0);
    /* argv[4] reserves an explicit calling-interface tag in raw records. */
    assert(strcmp(argv[4], "fortran") == 0);
    uint64_t start = now();
    for (size_t j = 0; j < calls; j++) {
        if (!solve_only) {
            memcpy(l, l0, bytes); memcpy(d, d0, bytes); memcpy(u, u0, bytes);
            dgttrf_(&n, l, d, u, du2, ipiv, &info); assert(info == 0);
        }
        if (!factor_only) {
            for (int k = 0; k < rhs_count; k++) {
                memcpy(b, rhs, bytes);
                dgttrs_("N", &n, &one, l, d, u, du2, ipiv, b, &n, &info, 1);
                assert(info == 0);
            }
        }
    }
    uint64_t elapsed = now() - start;
    printf("%llu\n", (unsigned long long)elapsed);
    /* Optional result dump for independent residual validation, outside timing. */
    if (getenv("TRIDIAGONAL_DUMP")) {
        for (int i = 0; i < n; i++) printf("%a\n", b[i]);
    }
    free(b); free(ipiv); free(a);
    return 0;
}

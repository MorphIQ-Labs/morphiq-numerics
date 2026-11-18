// C ABI adapters for pinned canonical CDF implementations; benchmark tooling only.
#include <cstddef>
#include <limits>
#if CDF_REFERENCE == 0
#include <ql/math/distributions/normaldistribution.hpp>
static const QuantLib::CumulativeNormalDistribution distribution;
static double evaluate(double x) { return distribution(x); }
#elif CDF_REFERENCE == 1 || CDF_REFERENCE == 2
#include <boost/math/distributions/normal.hpp>
#include <boost/math/policies/policy.hpp>
#if CDF_REFERENCE == 2
using Policy = boost::math::policies::policy<boost::math::policies::promote_double<false>>;
#else
using Policy = boost::math::policies::policy<>;
#endif
static const boost::math::normal_distribution<double, Policy> distribution;
static double evaluate(double x) { return boost::math::cdf(distribution, x); }
#elif CDF_REFERENCE == 3
#if defined(__aarch64__)
#include <arm_neon.h>
#else
#include <immintrin.h>
#endif
#include <sleef.h>
#if CDF_LANES == 8 && !defined(__AVX512F__)
extern "C" __m512d Sleef_erfcd8_u15avx512f(__m512d);
#endif
// SLEEF exposes erfc, not a normal-CDF entry. This conventional composition's
// complete CDF error is measured separately from erfc_u15's own contract.
static double evaluate(double x) {
    return 0.5 * Sleef_erfcd1_u15purecfma(x * -0x1.6a09e667f3bcdp-1);
}
#endif

static unsigned long errors = 0;
extern "C" unsigned long reference_errors() { return errors; }
extern "C" double prod_norm_cdf(double x) noexcept {
    try { return evaluate(x); }
    catch (...) { ++errors; return std::numeric_limits<double>::quiet_NaN(); }
}

#if CDF_REFERENCE == 3 && CDF_LANES == 8
#define CDF_TARGET __attribute__((target("avx512f,fma")))
#elif CDF_REFERENCE == 3 && CDF_LANES == 4
#define CDF_TARGET __attribute__((target("avx2,fma")))
#else
#define CDF_TARGET
#endif
extern "C" CDF_TARGET void prod_norm_cdf_slice(const double* x, double* y, std::size_t n) noexcept {
    std::size_t i = 0;
#if CDF_REFERENCE == 3 && CDF_LANES == 8
    for (; i+8<=n; i+=8) {
        const auto z = _mm512_mul_pd(_mm512_loadu_pd(x+i), _mm512_set1_pd(-0x1.6a09e667f3bcdp-1));
        _mm512_storeu_pd(y+i, _mm512_mul_pd(_mm512_set1_pd(0.5), Sleef_erfcd8_u15avx512f(z)));
    }
#elif CDF_REFERENCE == 3 && CDF_LANES == 4
    for (; i+4<=n; i+=4) {
        const auto z = _mm256_mul_pd(_mm256_loadu_pd(x+i), _mm256_set1_pd(-0x1.6a09e667f3bcdp-1));
        _mm256_storeu_pd(y+i, _mm256_mul_pd(_mm256_set1_pd(0.5), Sleef_erfcd4_u15avx2(z)));
    }
#elif CDF_REFERENCE == 3 && CDF_LANES == 2
    for (; i+2<=n; i+=2) {
        const auto z = vmulq_n_f64(vld1q_f64(x+i), -0x1.6a09e667f3bcdp-1);
        vst1q_f64(y+i, vmulq_n_f64(Sleef_erfcd2_u15advsimd(z), 0.5));
    }
#endif
    for (; i<n; ++i) y[i] = prod_norm_cdf(x[i]);
}

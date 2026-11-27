#if defined(__APPLE__)
#define _DARWIN_C_SOURCE
#include <pthread/qos.h>
int bench_set_qos(void) { return pthread_set_qos_class_self_np(QOS_CLASS_USER_INITIATED, 0); }
#else
#define _POSIX_C_SOURCE 200809L
#endif
#include <stdint.h>
#include <stddef.h>
#include <time.h>
#if defined(__x86_64__)
#include <immintrin.h>
#else
#include <arm_neon.h>
#ifndef NO_SLEEF
#include <sleef.h>
#endif
#endif
typedef double (*scalar1)(double);
typedef double (*scalar2)(double,int);
typedef void (*packet)(const double*,double*,size_t);
#ifndef NO_SLEEF
extern double Sleef_logd1_u10purecfma(double);
extern double Sleef_logd1_u10purec(double);
#if defined(__x86_64__)
extern __m128d Sleef_logd2_u10sse2(__m128d);
extern __m256d Sleef_logd4_u10avx2(__m256d);
extern __m512d Sleef_logd8_u10avx512f(__m512d);
double sleef_ln_scalar(double x){return Sleef_logd1_u10purecfma(x);}
void sleef_ln_sse2(const double*x,double*y,size_t n){size_t i=0;for(;i+2<=n;i+=2)_mm_storeu_pd(y+i,Sleef_logd2_u10sse2(_mm_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_logd1_u10purec(x[i]);}
__attribute__((target("avx2,fma"))) void sleef_ln_avx2(const double*x,double*y,size_t n){size_t i=0;for(;i+4<=n;i+=4)_mm256_storeu_pd(y+i,Sleef_logd4_u10avx2(_mm256_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_logd1_u10purecfma(x[i]);}
__attribute__((target("avx512f,fma"))) void sleef_ln_avx512(const double*x,double*y,size_t n){size_t i=0;for(;i+8<=n;i+=8)_mm512_storeu_pd(y+i,Sleef_logd8_u10avx512f(_mm512_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_logd1_u10purecfma(x[i]);}
#else
void sleef_ln_neon(const double*x,double*y,size_t n){size_t i=0;for(;i+2<=n;i+=2)vst1q_f64(y+i,Sleef_logd2_u10advsimd(vld1q_f64(x+i)));for(;i<n;i++)y[i]=Sleef_logd1_u10purecfma(x[i]);}
#endif
#endif
/* Native x86 performance targets have AVX. Keep timer loads/arithmetic in
 * VEX encoding and start each invocation with clean upper registers: a legacy
 * SSE timer otherwise measures caller-dependent AVX/SSE merge dependencies. */
#if defined(__x86_64__)
#define BENCH_TARGET __attribute__((target("avx")))
int bench_supported(void) { return __builtin_cpu_supports("avx") != 0; }
#else
#define BENCH_TARGET
int bench_supported(void) { return 1; }
#endif
/* Single-threaded harness metadata, captured before warmup and both clocks.
 * Reading SP avoids imposing a frame pointer on the measured call context. */
static uintptr_t last_stack_address;
static int inner_warmup = 1;
void bench_set_inner_warmup(int enabled) { inner_warmup = enabled != 0; }
/* The uniform first argument matches the public ctypes calling interface. */
typedef uint64_t (*sample_timer)(void *, const double *, double *, size_t, uint64_t);
uintptr_t bench_last_stack_address(void);
static BENCH_TARGET __attribute__((noinline)) uint64_t call_padded(
    sample_timer measure, void *function, const double *x, double *y,
    size_t n, uint64_t count, size_t padding) {
    volatile unsigned char *pad = __builtin_alloca(padding + 64);
    pad[0] = 1;
    __asm__ volatile("" :: "r"(pad) : "memory");
    uint64_t elapsed = measure(function, x, y, n, count);
    __asm__ volatile("" :: "r"(pad) : "memory");
    if (pad[0] != 1) __builtin_trap();
    return elapsed;
}
/* Time one sample with the timer's stack pointer at `offset` modulo 4 KiB
 * (a multiple of 16). The caller's stack depth is not stable: an interpreter
 * can change it between identical calls. So each sample first makes a zero-work
 * call to read the timer's address from this frame. The volatile pointer keeps
 * both calls on one out-of-line body, and the final barrier forbids a tail call,
 * which would enter that body at a different depth. */
BENCH_TARGET __attribute__((noinline)) uint64_t bench_at_stack_offset(
    sample_timer measure, void *function, const double *x, double *y,
    size_t n, uint64_t count, size_t offset) {
    uint64_t (*volatile call)(sample_timer, void *, const double *, double *,
                              size_t, uint64_t, size_t) = call_padded;
    call(measure, function, x, y, 0, 0, 0);
    size_t padding = (bench_last_stack_address() - offset) & 4095;
    uint64_t elapsed = call(measure, function, x, y, n, count, padding);
    __asm__ volatile("" ::: "memory");
    return elapsed;
}
static inline BENCH_TARGET __attribute__((always_inline)) void capture_stack(void) {
    uintptr_t sp;
#if defined(__x86_64__)
    __asm__ volatile("vzeroupper" ::: "xmm0", "xmm1", "xmm2", "xmm3",
                     "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9",
                     "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15");
    __asm__ volatile("mov %%rsp, %0" : "=r"(sp));
#elif defined(__aarch64__)
    __asm__ volatile("mov %0, sp" : "=r"(sp));
#else
#error Unsupported native benchmark target
#endif
    last_stack_address = sp;
    __asm__ volatile("" ::: "memory");
}
uintptr_t bench_last_stack_address(void) { return last_stack_address; }
static uint64_t now_ns(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
#define BARRIER(x,y) __asm__ volatile("" : : "r"(x),"r"(y) : "memory")
BENCH_TARGET uint64_t measure1(void *function,const double*x,double*y,size_t n,uint64_t it){scalar1 f=(scalar1)function;capture_stack();for(size_t w=0;w<(inner_warmup ? 100U : 0U);w++){for(size_t i=0;i<n;i++)y[i]=f(x[i]);BARRIER(x,y);}uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){BARRIER(x,y);for(size_t i=0;i<n;i++)y[i]=f(x[i]);BARRIER(x,y);}return now_ns()-start;}
BENCH_TARGET uint64_t measure2(void *function,const double*x,double*y,size_t n,uint64_t it){scalar2 f=(scalar2)function;capture_stack();for(size_t w=0;w<(inner_warmup ? 100U : 0U);w++){for(size_t i=0;i<n;i++)y[i]=f(x[i],1);BARRIER(x,y);}uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){BARRIER(x,y);for(size_t i=0;i<n;i++)y[i]=f(x[i],1);BARRIER(x,y);}return now_ns()-start;}
BENCH_TARGET uint64_t measure_packet(void *function,const double*x,double*y,size_t n,uint64_t it){packet f=(packet)function;capture_stack();for(size_t w=0;w<(inner_warmup ? 100U : 0U);w++){f(x,y,n);BARRIER(x,y);}uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){BARRIER(x,y);f(x,y,n);BARRIER(x,y);}return now_ns()-start;}
#ifndef NO_SLEEF
extern double Sleef_expd1_u10purecfma(double);
double sleef_ln_exp_scalar_fma(double x){return Sleef_expd1_u10purecfma(Sleef_logd1_u10purecfma(x));}
#if defined(__x86_64__)
extern double Sleef_erfcd1_u15purecfma(double);
extern __m256d Sleef_expd4_u10avx2(__m256d);
extern __m512d Sleef_expd8_u10avx512f(__m512d);
extern __m256d Sleef_erfcd4_u15avx2(__m256d);
extern __m512d Sleef_erfcd8_u15avx512f(__m512d);
double sleef_exp_scalar(double x){return Sleef_expd1_u10purecfma(x);}
double sleef_cdf_scalar(double x){return 0.5*Sleef_erfcd1_u15purecfma(x*(-0x1.6a09e667f3bcdp-1));}
__attribute__((target("avx2,fma"))) void sleef_exp_avx2(const double*x,double*y,size_t n){size_t i=0;for(;i+4<=n;i+=4)_mm256_storeu_pd(y+i,Sleef_expd4_u10avx2(_mm256_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_expd1_u10purecfma(x[i]);}
__attribute__((target("avx512f,fma"))) void sleef_exp_avx512(const double*x,double*y,size_t n){size_t i=0;for(;i+8<=n;i+=8)_mm512_storeu_pd(y+i,Sleef_expd8_u10avx512f(_mm512_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_expd1_u10purecfma(x[i]);}
__attribute__((target("avx2,fma"))) void sleef_cdf_avx2(const double*x,double*y,size_t n){size_t i=0;for(;i+4<=n;i+=4){__m256d z=_mm256_mul_pd(_mm256_loadu_pd(x+i),_mm256_set1_pd(-0x1.6a09e667f3bcdp-1));_mm256_storeu_pd(y+i,_mm256_mul_pd(_mm256_set1_pd(0.5),Sleef_erfcd4_u15avx2(z)));}for(;i<n;i++)y[i]=sleef_cdf_scalar(x[i]);}
__attribute__((target("avx512f,fma"))) void sleef_cdf_avx512(const double*x,double*y,size_t n){size_t i=0;for(;i+8<=n;i+=8){__m512d z=_mm512_mul_pd(_mm512_loadu_pd(x+i),_mm512_set1_pd(-0x1.6a09e667f3bcdp-1));_mm512_storeu_pd(y+i,_mm512_mul_pd(_mm512_set1_pd(0.5),Sleef_erfcd8_u15avx512f(z)));}for(;i<n;i++)y[i]=sleef_cdf_scalar(x[i]);}

extern double Sleef_expd1_u10purec(double);
extern double Sleef_erfcd1_u15purec(double);
extern __m128d Sleef_expd2_u10sse2(__m128d);
extern __m128d Sleef_erfcd2_u15sse2(__m128d);
void sleef_exp_sse2(const double*x,double*y,size_t n){size_t i=0;for(;i+2<=n;i+=2)_mm_storeu_pd(y+i,Sleef_expd2_u10sse2(_mm_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_expd1_u10purec(x[i]);}
void sleef_cdf_sse2(const double*x,double*y,size_t n){size_t i=0;for(;i+2<=n;i+=2){__m128d z=_mm_mul_pd(_mm_loadu_pd(x+i),_mm_set1_pd(-0x1.6a09e667f3bcdp-1));_mm_storeu_pd(y+i,_mm_mul_pd(_mm_set1_pd(0.5),Sleef_erfcd2_u15sse2(z)));}for(;i<n;i++)y[i]=0.5*Sleef_erfcd1_u15purec(x[i]*(-0x1.6a09e667f3bcdp-1));}
#endif
#endif
BENCH_TARGET uint64_t measure_chain1(void *function,const double*x,double*y,size_t n,uint64_t it){scalar1 f=(scalar1)function;capture_stack();double previous=0;for(size_t w=0;w<(inner_warmup ? 100U : 0U);w++)for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i]);uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i]);BARRIER(x,y);}*y=previous;return now_ns()-start;}
BENCH_TARGET uint64_t measure_chain2(void *function,const double*x,double*y,size_t n,uint64_t it){scalar2 f=(scalar2)function;capture_stack();double previous=0;for(size_t w=0;w<(inner_warmup ? 100U : 0U);w++)for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i],1);uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i],1);BARRIER(x,y);}*y=previous;return now_ns()-start;}

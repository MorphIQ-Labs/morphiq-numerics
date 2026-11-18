#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stddef.h>
#include <time.h>
typedef double (*scalar1)(double);
typedef void (*packet)(const double*,double*,size_t);
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
/* slots is a declared power of two. Buffer allocation and copying happen outside timing. */
BENCH_TARGET uint64_t measure1_cache(scalar1 f,const double*x,double*y,size_t n,uint64_t it,size_t slots){capture_stack();
 for(size_t s=0;s<slots;s++){for(size_t i=0;i<n;i++)y[s*n+i]=f(x[s*n+i]);BARRIER(x,y);}
 uint64_t start=now_ns();
 for(uint64_t r=0;r<it;r++){size_t off=(r&(slots-1))*n;BARRIER(x,y);for(size_t i=0;i<n;i++)y[off+i]=f(x[off+i]);BARRIER(x,y);}
 return now_ns()-start;
}
BENCH_TARGET uint64_t measure_packet_cache(packet f,const double*x,double*y,size_t n,uint64_t it,size_t slots){capture_stack();
 for(size_t s=0;s<slots;s++){f(x+s*n,y+s*n,n);BARRIER(x,y);}
 uint64_t start=now_ns();
 for(uint64_t r=0;r<it;r++){size_t off=(r&(slots-1))*n;BARRIER(x,y);f(x+off,y+off,n);BARRIER(x,y);}
 return now_ns()-start;
}

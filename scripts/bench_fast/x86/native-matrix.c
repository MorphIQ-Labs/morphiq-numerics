#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stddef.h>
#include <time.h>
#include <immintrin.h>
typedef double (*scalar1)(double);
typedef double (*scalar2)(double,int);
typedef void (*packet)(const double*,double*,size_t);
extern double Sleef_logd1_u10purecfma(double);
extern double Sleef_logd1_u10purec(double);
extern __m128d Sleef_logd2_u10sse2(__m128d);
extern __m256d Sleef_logd4_u10avx2(__m256d);
extern __m512d Sleef_logd8_u10avx512f(__m512d);
double sleef_ln_scalar(double x){return Sleef_logd1_u10purecfma(x);}
void sleef_ln_sse2(const double*x,double*y,size_t n){size_t i=0;for(;i+2<=n;i+=2)_mm_storeu_pd(y+i,Sleef_logd2_u10sse2(_mm_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_logd1_u10purec(x[i]);}
__attribute__((target("avx2,fma"))) void sleef_ln_avx2(const double*x,double*y,size_t n){size_t i=0;for(;i+4<=n;i+=4)_mm256_storeu_pd(y+i,Sleef_logd4_u10avx2(_mm256_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_logd1_u10purecfma(x[i]);}
__attribute__((target("avx512f,fma"))) void sleef_ln_avx512(const double*x,double*y,size_t n){size_t i=0;for(;i+8<=n;i+=8)_mm512_storeu_pd(y+i,Sleef_logd8_u10avx512f(_mm512_loadu_pd(x+i)));for(;i<n;i++)y[i]=Sleef_logd1_u10purecfma(x[i]);}
static uint64_t now_ns(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
#define BARRIER(x,y) __asm__ volatile("" : : "r"(x),"r"(y) : "memory")
uint64_t measure1(scalar1 f,const double*x,double*y,size_t n,uint64_t it){for(size_t w=0;w<100;w++){for(size_t i=0;i<n;i++)y[i]=f(x[i]);BARRIER(x,y);}uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){BARRIER(x,y);for(size_t i=0;i<n;i++)y[i]=f(x[i]);BARRIER(x,y);}return now_ns()-start;}
uint64_t measure2(scalar2 f,const double*x,double*y,size_t n,uint64_t it){for(size_t w=0;w<100;w++){for(size_t i=0;i<n;i++)y[i]=f(x[i],1);BARRIER(x,y);}uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){BARRIER(x,y);for(size_t i=0;i<n;i++)y[i]=f(x[i],1);BARRIER(x,y);}return now_ns()-start;}
uint64_t measure_packet(packet f,const double*x,double*y,size_t n,uint64_t it){for(size_t w=0;w<100;w++){f(x,y,n);BARRIER(x,y);}uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){BARRIER(x,y);f(x,y,n);BARRIER(x,y);}return now_ns()-start;}
extern double Sleef_expd1_u10purecfma(double);
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
uint64_t measure_chain1(scalar1 f,const double*x,double*y,size_t n,uint64_t it){double previous=0;for(size_t w=0;w<100;w++)for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i]);uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i]);BARRIER(x,y);}*y=previous;return now_ns()-start;}
uint64_t measure_chain2(scalar2 f,const double*x,double*y,size_t n,uint64_t it){double previous=0;for(size_t w=0;w<100;w++)for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i],1);uint64_t start=now_ns();for(uint64_t r=0;r<it;r++){for(size_t i=0;i<n;i++)previous=f((previous-previous)+x[i],1);BARRIER(x,y);}*y=previous;return now_ns()-start;}

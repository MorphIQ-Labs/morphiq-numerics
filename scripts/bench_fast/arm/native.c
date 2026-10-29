#define _DARWIN_C_SOURCE
#include <stdint.h>
#include <stddef.h>
#include <time.h>
#include <pthread/qos.h>
#include <arm_neon.h>
#include <sleef.h>
typedef double (*scalar1)(double);
typedef double (*scalar2)(double,int);
typedef void (*packet)(const double*,double*,size_t);
int bench_set_qos(void) { return pthread_set_qos_class_self_np(QOS_CLASS_USER_INITIATED, 0); }
static uint64_t now_ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec; }
#define BARRIER(x,y) __asm__ volatile("" : : "r"(x),"r"(y) : "memory")
uint64_t measure1(scalar1 f,const double*x,double*y,size_t n,uint64_t it) {
  for(size_t w=0;w<100;w++){for(size_t i=0;i<n;i++)y[i]=f(x[i]);BARRIER(x,y);}
  uint64_t start=now_ns();
  for(uint64_t r=0;r<it;r++){BARRIER(x,y);for(size_t i=0;i<n;i++)y[i]=f(x[i]);BARRIER(x,y);}
  return now_ns()-start;
}
uint64_t measure2(scalar2 f,const double*x,double*y,size_t n,uint64_t it) {
  for(size_t w=0;w<100;w++){for(size_t i=0;i<n;i++)y[i]=f(x[i],1);BARRIER(x,y);}
  uint64_t start=now_ns();
  for(uint64_t r=0;r<it;r++){BARRIER(x,y);for(size_t i=0;i<n;i++)y[i]=f(x[i],1);BARRIER(x,y);}
  return now_ns()-start;
}
uint64_t measure_packet(packet f,const double*x,double*y,size_t n,uint64_t it) {
  for(size_t w=0;w<100;w++){f(x,y,n);BARRIER(x,y);}
  uint64_t start=now_ns();
  for(uint64_t r=0;r<it;r++){BARRIER(x,y);f(x,y,n);BARRIER(x,y);}
  return now_ns()-start;
}
double sleef_cdf_scalar(double x) { return 0.5*Sleef_erfcd1_u15purecfma(x*(-0x1.6a09e667f3bcdp-1)); }
void sleef_exp_neon(const double*x,double*y,size_t n) {
  size_t i=0;for(;i+2<=n;i+=2)vst1q_f64(y+i,Sleef_expd2_u10advsimd(vld1q_f64(x+i)));
  for(;i<n;i++)y[i]=Sleef_expd1_u10purecfma(x[i]);
}
void sleef_cdf_neon(const double*x,double*y,size_t n) {
  size_t i=0;for(;i+2<=n;i+=2) {
    float64x2_t z=vmulq_f64(vld1q_f64(x+i),vdupq_n_f64(-0x1.6a09e667f3bcdp-1));
    vst1q_f64(y+i,vmulq_f64(vdupq_n_f64(0.5),Sleef_erfcd2_u15advsimd(z)));
  }
  for(;i<n;i++)y[i]=sleef_cdf_scalar(x[i]);
}
uint64_t measure_chain1(scalar1 f,const double*x,double*y,size_t n,uint64_t it) {
  double v=0;uint64_t start=now_ns();
  for(uint64_t r=0;r<it;r++){for(size_t i=0;i<n;i++)v=f(x[i]+v*0.03125);BARRIER(x,y);}
  y[0]=v;return now_ns()-start;
}
uint64_t measure_chain2(scalar2 f,const double*x,double*y,size_t n,uint64_t it) {
  double v=0;uint64_t start=now_ns();
  for(uint64_t r=0;r<it;r++){for(size_t i=0;i<n;i++)v=f(x[i]+v*0.03125,1);BARRIER(x,y);}
  y[0]=v;return now_ns()-start;
}
uint64_t measure_cache_packet(packet f,const double*x,double*y,size_t n,uint64_t it,double*cache,size_t count) {
  double v=0;uint64_t start=now_ns();
  for(uint64_t r=0;r<it;r++) {
    for(size_t j=0;j<count;j+=8)v+=cache[j];
    __asm__ volatile("" : "+w"(v) : : "memory");
    BARRIER(x,y);f(x,y,n);BARRIER(x,y);
  }
  cache[0]=v;return now_ns()-start;
}
uint64_t measure_cache1(scalar1 f,const double*x,double*y,size_t n,uint64_t it,double*cache,size_t count) {
  double v=0;uint64_t start=now_ns();
  for(uint64_t r=0;r<it;r++) {
    for(size_t j=0;j<count;j+=8)v+=cache[j];
    __asm__ volatile("" : "+w"(v) : : "memory");
    BARRIER(x,y);for(size_t i=0;i<n;i++)y[i]=f(x[i]);BARRIER(x,y);
  }
  cache[0]=v;return now_ns()-start;
}
extern double prod_norm_cdf(double);
extern void prod_exp_slice(const double*,double*,size_t);
extern void prod_erfcx_slice(const double*,double*,size_t);
void composed_cdf_passes(const double*x,double*y,size_t n) {
  double scaled[n?n:1], exponent[n?n:1];
  for(size_t i=0;i<n;i++) {double a=__builtin_fabs(x[i]);scaled[i]=a*0x1.6a09e667f3bcdp-1;exponent[i]=(-0.5*a)*a;}
  prod_exp_slice(exponent,y,n);prod_erfcx_slice(scaled,exponent,n);
  for(size_t i=0;i<n;i++) {double lower=(0.5*y[i])*exponent[i];y[i]=x[i]<0?lower:1-lower;}
}

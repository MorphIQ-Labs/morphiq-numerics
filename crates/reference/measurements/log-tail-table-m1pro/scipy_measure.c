#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <time.h>
typedef double (*scalar_fn)(double, int);
static uint64_t now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return (uint64_t)t.tv_sec*1000000000+t.tv_nsec; }
double measure(scalar_fn f, const double *xs, size_t n, int chain) {
  uint64_t start=now(), end; size_t rounds=0, index=0; volatile double sink=0;
  do {
    for (size_t i=0;i<n;i++) {
      double y=f(xs[chain?index:i],1); sink=y;
      if(chain) { uint64_t bits; memcpy(&bits,&y,sizeof(bits)); index=(index+1+((bits>>32)&1023))%n; }
    }
    rounds++; end=now();
  } while(end-start<150000000);
  (void)sink; return (double)(end-start)/(double)(rounds*n);
}

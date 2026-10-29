#define _GNU_SOURCE
#include <stdio.h>
extern void HeapProfilerStart(const char*);
extern void HeapProfilerDump(const char*);
extern void HeapProfilerStop(void);
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
typedef void (*packet)(const double*,double*,size_t);
typedef double (*scalar)(double);
/* Instrumented evidence only; never linked into the timing executable. */
void observe_allocations(void *f,const double*x,double*y,size_t n,int scalar_call,const char*trace){
 HeapProfilerStart(trace);
 for(size_t r=0;r<10001;r++){
  if(scalar_call){for(size_t i=0;i<n;i++)y[i]=((scalar)f)(x[i]);}
  else ((packet)f)(x,y,n);
  __asm__ volatile("" : : "r"(x),"r"(y) : "memory");
 }
 HeapProfilerDump("public-call observations");HeapProfilerStop();
}
/* Positive control establishes that the trace can detect an allocation. */
void observe_control(const char*trace){HeapProfilerStart(trace);void*p=malloc(71);__asm__ volatile("" : : "r"(p) : "memory");free(p);HeapProfilerDump("public-call observations");HeapProfilerStop();}

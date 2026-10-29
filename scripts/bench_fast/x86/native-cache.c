#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stddef.h>
#include <time.h>
typedef double (*scalar1)(double);
typedef void (*packet)(const double*,double*,size_t);
static uint64_t now_ns(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
#define BARRIER(x,y) __asm__ volatile("" : : "r"(x),"r"(y) : "memory")
/* slots is a declared power of two. Buffer allocation and copying happen outside timing. */
uint64_t measure1_cache(scalar1 f,const double*x,double*y,size_t n,uint64_t it,size_t slots){
 for(size_t s=0;s<slots;s++){for(size_t i=0;i<n;i++)y[s*n+i]=f(x[s*n+i]);BARRIER(x,y);}
 uint64_t start=now_ns();
 for(uint64_t r=0;r<it;r++){size_t off=(r&(slots-1))*n;BARRIER(x,y);for(size_t i=0;i<n;i++)y[off+i]=f(x[off+i]);BARRIER(x,y);}
 return now_ns()-start;
}
uint64_t measure_packet_cache(packet f,const double*x,double*y,size_t n,uint64_t it,size_t slots){
 for(size_t s=0;s<slots;s++){f(x+s*n,y+s*n,n);BARRIER(x,y);}
 uint64_t start=now_ns();
 for(uint64_t r=0;r<it;r++){size_t off=(r&(slots-1))*n;BARRIER(x,y);f(x+off,y+off,n);BARRIER(x,y);}
 return now_ns()-start;
}

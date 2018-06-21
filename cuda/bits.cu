#include <stdio.h>

#define N 65536 // 256 ^ 256

#define h2d(h,d,n) cudaMemcpy(d,h,sizeof(int)*n, cudaMemcpyHostToDevice)
#define d2h(d,h,n) cudaMemcpy(h,d,sizeof(int)*n, cudaMemcpyDeviceToHost)
#define dma(v,n) int *v; cudaMalloc((void **)&v, sizeof(int)*n)
#define dfr(v) cudaFree(v)
#define DO(n) for(int i=0;i<n;++i)
#define P(n) for(int i=0;i<n;++i)
#define BIx blockIdx.x
#define BX(v) v[BIx]
#define OP1(nm) __global__ void nm(int *r, int*x)
#define OP2(nm) __global__ void nm(int *r, int *x, int *y)

OP1(not){ BX(r) = ~BX(a); }
OP2(xor){ BX(r) = BX(a) ^ BX(b); }
OP2(and){ BX(r) = BX(a) & BX(b); }

int main() {

  // arrays on the cpu: h:'host'
  int ha[N], hb[N];

  // arrays on the gpu d:'device'
  int *da, *db; dma(da, N); dma(db, N);

  // ha: !N
  DO(N) ha[i] = i;

  dma(II, N);  dma(OO, N);

  h2d(ha, da, N);
  add<<<N, 1>>>(da, db);
  d2h(db, hb, N);

  DO(N) { P("%6x ", hb[i]); if (!(15&i-1)) P("\n"); }
  P("\n");

  dfr(da); dfr(db);

  P("hello from CUDA!\n");
  return 0;
}

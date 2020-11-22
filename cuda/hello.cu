// based on https://gist.github.com/dpiponi/1502434
#include <stdio.h>

#define N  256 // 0x1d710 // 65536 // 4096 //1024

#define h2d(h,d,n) cudaMemcpy(d,h,sizeof(int)*n, cudaMemcpyHostToDevice)
#define d2h(d,h,n) cudaMemcpy(h,d,sizeof(int)*n, cudaMemcpyDeviceToHost)
#define I(n) for(int i=0;i<n;++i)

__global__
void add(int *a, int *b) { int i = blockIdx.x; if (i<N) { b[i] = 2*a[i]; }}

int main() {

  // arrays on the cpu: h:'host'
  int ha[N], hb[N];

  // arrays on the gpu d:'device'
  int *da, *db;
  cudaMalloc((void **)&da, N*sizeof(int));
  cudaMalloc((void **)&db, N*sizeof(int));

  // ha: !N
  I(N) ha[i] = i;

  h2d(ha, da, N);
  add<<<N, 1>>>(da, db);
  d2h(db, hb, N);

  for(int i=0; i<N;){ printf("%6x ", hb[i]); if(!(++i&15))printf("\n"); }
  printf("\n");

  cudaFree(da);
  cudaFree(db);

  printf("hello from CUDA!\n");
  int dc; cudaGetDeviceCount(&dc);
  printf("Device count: %d\n", dc);
  return 0;
}

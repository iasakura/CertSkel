#include<cstdio>
#include<cstdlib>
#include<utility>

int* alloc(int n) {
  int *in_d; cudaMalloc(&in_d, sizeof(int) * n);
  cudaDeviceSynchronize();
  return in_d;
}

#define cudaCheckError() { \
  cudaError_t e=cudaGetLastError(); \
  if(e!=cudaSuccess) {\
    printf("Cuda failure %s:%d: '%s'\n",__FILE__,__LINE__,cudaGetErrorString(e));\
    exit(0);\
  }\
}

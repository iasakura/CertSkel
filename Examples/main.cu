#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <utility>

#define check(call) {    \
  call;\
  cudaError_t e=cudaGetLastError(); \
  if(e!=cudaSuccess) {\
    printf("Cuda failure %s:%d: '%s'\n",__FILE__,__LINE__,cudaGetErrorString(e));\
    exit(0);\
  }\
}

int __main(int, int*, int*, int, int*);

int main(int argc, char**argv) {
  int n = 10;
  int* arr = (int*)malloc(sizeof(int) * n);
  int* out1 = (int*)malloc(sizeof(int) * 1);
  int* out2 = (int*)malloc(sizeof(int) * 1);
  printf("argc = %d\n", argc);
  srand(argc);
  for (int i = 0; i < n; i++) {
    arr[i] = rand() % 100;
    printf("arr[%d] = %d\n", i, arr[i]);
  }

  int *in_d; check(cudaMalloc(&in_d, sizeof(int) * n));
  check(cudaMemcpy(in_d, arr, sizeof(int) * n, cudaMemcpyHostToDevice));
  int *out1_d; check(cudaMalloc(&out1_d, sizeof(int) * 1));
  int *out2_d; check(cudaMalloc(&out2_d, sizeof(int) * 1));
  cudaDeviceSynchronize();
  int len = __main(n, out1_d, out2_d, n, in_d);
  
  printf("len = %d\n", len);
  int* out1_h = (int*)malloc(sizeof(int) * len);
  int* out2_h = (int*)malloc(sizeof(int) * len);
  check(cudaMemcpy(out1_h, out1_d, sizeof(int) * len, cudaMemcpyDeviceToHost));
  check(cudaMemcpy(out2_h, out2_d, sizeof(int) * len, cudaMemcpyDeviceToHost));
  cudaDeviceSynchronize();
  for (int i = 0; i < len; i++) {
    printf("res[%d] = %d\n", i, out1_h[i]);
  }
}

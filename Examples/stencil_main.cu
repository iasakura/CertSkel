#include <cstdio>
#include <cstdlib>
#include <cassert>
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

int __main(int, int*, int, int*, int, int*, int*);

int main(int argc, char**argv) {
  int dx = 4, dy = 4;
  int n = dx * dy;
  // input array
  int* inp = (int*)malloc(sizeof(int) * n);
  // X/Y dimension 
  int* dimX = (int*)malloc(sizeof(int) * 1);
  int* dimY = (int*)malloc(sizeof(int) * 1);
  printf("argc = %d\n", argc);
  srand(argc);
  for (int i = 0; i < n; i++) {
      inp[i] = rand() % 100;
      printf("arr[%d] = %d\n", i, inp[i]);
  }
  *dimX = dx; *dimY = dy;

  int *inp_d; check(cudaMalloc(&inp_d, sizeof(int) * n));
  check(cudaMemcpy(inp_d, inp, sizeof(int) * n, cudaMemcpyHostToDevice));
  int *dimX_d; check(cudaMalloc(&dimX_d, sizeof(int) * 1));
  check(cudaMemcpy(dimX_d, dimX, sizeof(int) * 1, cudaMemcpyHostToDevice));
  int *dimY_d; check(cudaMalloc(&dimY_d, sizeof(int) * 1));
  check(cudaMemcpy(dimY_d, dimY, sizeof(int) * 1, cudaMemcpyHostToDevice));
  int *out_d; check(cudaMalloc(&out_d, sizeof(int) * n));
  cudaDeviceSynchronize();
  int len = __main(n, out_d, n, inp_d, 1, dimX_d, dimY_d);
  
  printf("len = %d\n", len);
  // output array
  int* out = (int*)malloc(sizeof(int) * n);
  check(cudaMemcpy(out, out_d, sizeof(int) * len, cudaMemcpyDeviceToHost));
  cudaDeviceSynchronize();

  // for check the correctness
  int* ans = (int*)malloc(sizeof(int) * n);
  for (int i = 0; i < dy; i++) {
      for (int j = 0; j < dx; j++) {
          ans[i * dx + j] = 
              (inp[i * dx + j] +
               ((i == 0) ? 0 : inp[(i - 1) * dx + j]) +
               ((i == dy - 1) ? 0 : inp[(i + 1) * dx + j]) +
               ((j == 0) ? 0 : inp[i * dx + (j - 1)]) +
               ((j == dx - 1) ? 0 : inp[i * dx + (j + 1)])) / 5;
      }
  }

  for (int i = 0; i < len; i++) {
      printf("out[%d] = %d\n", i, out[i]);
      assert(ans[i] == out[i]);
  }
}

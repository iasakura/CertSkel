#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define check(call) {                           \
  call;\
  cudaError_t e=cudaGetLastError(); \
  if(e!=cudaSuccess) {\
    printf("Cuda failure %s:%d: '%s'\n",__FILE__,__LINE__,cudaGetErrorString(e));\
    exit(0);\
  }\
}

#define measure(block)  { \
    struct timeval tv1, tv2; \
    gettimeofday(&tv1, NULL); \
    block; \
    gettimeofday(&tv2, NULL); \
    printf ("Total time = %f seconds\n", \
         (double) (tv2.tv_usec - tv1.tv_usec) / 1000000 + \
         (double) (tv2.tv_sec - tv1.tv_sec)); \
}

int __main(int, int*, int, int*, int, int*);

int main(int argc, char** argv) {
    int n;
    if (argc > 1) {
        n = atoi(argv[1]);
    } else {
        n = 10;
    }
    
    int* arr1 = (int*)malloc(sizeof(int) * n);
    int* arr2 = (int*)malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) {
        arr1[i] = rand() % 100;
        arr2[i] = rand() % 100;
        printf("arr1[%d] = %d\n", i, arr1[i]);
        printf("arr2[%d] = %d\n", i, arr2[i]);
    }

    int *in_d1; check(cudaMalloc(&in_d1, sizeof(int) * n));
    check(cudaMemcpy(in_d1, arr1, sizeof(int) * n, cudaMemcpyHostToDevice));
    int *in_d2; check(cudaMalloc(&in_d2, sizeof(int) * n));
    check(cudaMemcpy(in_d2, arr2, sizeof(int) * n, cudaMemcpyHostToDevice));

    int *out_d; check(cudaMalloc(&out_d, sizeof(int) * n));
    cudaDeviceSynchronize();
    int len;
    measure ({
       len = __main(n, out_d, n, in_d1, n, in_d2);
    });
  
    printf("len = %d\n", len);
    int* out_h = (int*)malloc(sizeof(int) * len);
    check(cudaMemcpy(out_h, out_d, sizeof(int) * len, cudaMemcpyDeviceToHost));
    for (int i = 0; i < len; i++) {
        printf("out_h[%d] = %d\n", i, out_h[i]);
    }
}

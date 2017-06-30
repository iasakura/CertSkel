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

// stopwatch start
timespec sw_start() {
    timespec start;
    clock_gettime(CLOCK_REALTIME, &start);
    return start;
}

// stopwatch start
void sw_stop(const char* header, timespec start) {
    timespec stop;
    clock_gettime(CLOCK_REALTIME, &stop);
    fprintf (stderr, "%s: %fs\n", 
            header, 
            (double) (stop.tv_nsec - start.tv_nsec) / (1000 * 1000 * 1000) +
            (double) (stop.tv_sec - start.tv_sec));
}

#define measure(header, block)  { \
    struct timespec start = sw_start(); \
    block; \
    sw_stop(header, start); \
}

int __main(int, int*, int, int*, int, int*);

int dot_host(int len, int* arr1, int* arr2) {
    int sum = 0;
    for (int i = 0; i < len; i++) {
        sum += arr1[i] * arr2[i];
    }
    return sum;
}

int main(int argc, char** argv) {
    int n;
    if (argc > 1) {
        n = atoi(argv[1]);
    } else {
        n = 10;
    }
    if (argc > 2) {
        srand(atoi(argv[2]));
    }
    
    int* arr1 = (int*)malloc(sizeof(int) * n);
    int* arr2 = (int*)malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) {
        arr1[i] = rand() % 10;
        arr2[i] = rand() % 10;
        // printf("arr1[%d] = %d\n", i, arr1[i]);
        // printf("arr2[%d] = %d\n", i, arr2[i]);
    }

    int *in_d1; check(cudaMalloc(&in_d1, sizeof(int) * n));
    check(cudaMemcpy(in_d1, arr1, sizeof(int) * n, cudaMemcpyHostToDevice));
    int *in_d2; check(cudaMalloc(&in_d2, sizeof(int) * n));
    check(cudaMemcpy(in_d2, arr2, sizeof(int) * n, cudaMemcpyHostToDevice));

    int *out_d; check(cudaMalloc(&out_d, sizeof(int) * 1));
    cudaDeviceSynchronize();
    int len;
    int* out_h;
    // warmup
    check(__main(n, out_d, n, in_d1, n, in_d2));

    measure ("certskel dot", {
       len = __main(n, out_d, n, in_d1, n, in_d2);
       out_h = (int*)malloc(sizeof(int) * len);
       check(cudaMemcpy(out_h, out_d, sizeof(int) * len, cudaMemcpyDeviceToHost));
    });

    printf("len = %d\n", len);
    for (int i = 0; i < len; i++) {
        printf("out_h[%d] = %d\n", i, out_h[i]);
    }
    printf("expected: %d, actual: %d\n", dot_host(n, arr1, arr2), out_h[0]);
}

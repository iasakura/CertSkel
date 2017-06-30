#include <thrust/host_vector.h>
#include <thrust/device_vector.h>
#include <thrust/inner_product.h>
#include <iostream>

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

    thrust::host_vector<int> xs(n);
    thrust::host_vector<int> ys(n);
    for (int i = 0; i < n; i++) {
        xs[i] = rand() % 10;
        ys[i] = rand() % 10;
    }
    thrust::device_vector<int> d_xs = xs;
    thrust::device_vector<int> d_ys = ys;

    // warmup
    thrust::inner_product(d_xs.begin(), d_xs.end(), d_ys.begin(), 0);

    int res;
    measure("thrust dot", {
      res = thrust::inner_product(d_xs.begin(), d_xs.end(), d_ys.begin(), 0);
    });
    std::cout << res << std::endl;
}


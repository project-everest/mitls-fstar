#include "bench.h"

void nego_baseline(int);

#define ITERATIONS 100000
#define BENCHES 1

int main() {
    benchmark baseline = mk_benchmark("baseline", ITERATIONS, nego_baseline);
    benchmark bs[BENCHES] = { baseline };
    printf("Starting ...\n");
    printf(MARKER);
    run_benchmarks(BENCHES, bs);
    // printf(MARKER);
}

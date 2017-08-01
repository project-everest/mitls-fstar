#include "bench.h"

void nego_baseline(int);
void nego_const_ptr_ctxt(int);

#define ITERATIONS 10000
#define BENCHES 2

int main() {
    benchmark bs[BENCHES] = {
        mk_benchmark("baseline", ITERATIONS, nego_baseline),
        mk_benchmark("const_ctxt_ptr", ITERATIONS, nego_const_ptr_ctxt),
    };
    printf("Starting ...\n");
    printf(MARKER);
    run_benchmarks(BENCHES, bs);
}

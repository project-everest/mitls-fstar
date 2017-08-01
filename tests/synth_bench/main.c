#include "bench.h"

void nego_baseline(int);
void nego_const_ptr_ctxt(int);
void nego_state_by_ptr(int);

#define ITERATIONS 10000
#define BENCHES 3

int main() {
    benchmark bs[BENCHES] = {
        mk_benchmark("baseline", ITERATIONS, nego_baseline),
        mk_benchmark("const_ctxt_ptr", ITERATIONS, nego_const_ptr_ctxt),
        mk_benchmark("nego_state_by_ptr", ITERATIONS, nego_state_by_ptr),
    };
    printf("Starting ...\n");
    printf(MARKER);
    run_benchmarks(BENCHES, bs);
}

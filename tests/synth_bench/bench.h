#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MARKER "-------------------------------------------\n"

typedef struct benchmark {
    const char * name;
    int iterations;
    time_t start_time;
    time_t end_time;
    double total_time;
    void (*bench_fn)(int);
} benchmark;

benchmark mk_benchmark(const char * name, int iterations, void (*bench_fn)(int)) {
    benchmark bench;
    // char * n = (char *)malloc(sizeof(char) * (strlen(name) + 1));
    //strncpy(n, name, strlen(name));
    bench.name = name;
    bench.iterations = iterations;
    bench.bench_fn = bench_fn;
    return bench;
}

void run_benchmarks(int num_of_benches, benchmark bs[]) {
    int i = 0;
    for (; i < num_of_benches; i++) {
        benchmark bench = bs[i];
        bench.start_time = time(NULL);
        bench.bench_fn(bench.iterations);
        bench.end_time = time(NULL);
        double total_time = difftime(bench.end_time, bench.start_time);
        printf("name: %s | iterations: %d | total: %f\n", bench.name, bench.iterations, total_time);
        printf(MARKER);
    }
}

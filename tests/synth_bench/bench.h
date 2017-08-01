#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MARKER "-------------------------------------------\n"

#include <sys/time.h>

long long current_timestamp() {
    struct timeval te;
    gettimeofday(&te, NULL); // get current time
    long long milliseconds = te.tv_sec*1000LL + te.tv_usec/1000; // caculate milliseconds
    return milliseconds;
}

typedef struct benchmark {
    const char * name;
    int iterations;
    long long start_time;
    long long end_time;
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
    long long baseline_total_time = 0;
    for (; i < num_of_benches; i++) {
        benchmark bench = bs[i];
        bench.start_time = current_timestamp();
        bench.bench_fn(bench.iterations);
        bench.end_time = current_timestamp();
        long long total_time = bench.end_time - bench.start_time;

        if (baseline_total_time == 0.0) {
            baseline_total_time = total_time;
        }

        double speed_up = (double)total_time / (double)baseline_total_time;

        printf("name: %s | iterations: %d | total: %lld | speedup: %f\n", bench.name, bench.iterations, total_time, speed_up);

        printf(MARKER);
    }
}

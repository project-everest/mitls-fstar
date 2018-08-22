#!/bin/bash

rm -f results

for i in $(seq 10); do \
    DYLD_LIBRARY_PATH=../../src/tls/extract/Kremlin-Library:../../src/pki:../../../MLCrypto/openssl \
                     gtime -f '%U' ./cmitls.exe 0.0.0.0 4443 100000 -quiet 2>&1 | tail -1 | tee -a results;
done

awk '{ total += $1; count++ } END { print 100000/(total/count) " kB/s"}' results

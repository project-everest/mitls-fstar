#!/bin/bash

set -e
OPENSSL_ROOT=/home/user/dev/git/openssl
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$OPENSSL_ROOT/openssl/

./server

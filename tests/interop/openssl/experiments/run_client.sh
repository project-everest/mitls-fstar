#!/bin/bash

set -e
OPENSSL_ROOT=/home/user/dev/git/openssl
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$OPENSSL_ROOT/openssl/

./client

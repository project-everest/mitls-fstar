#!/bin/bash

set -e

gcc -shared -fPIC cutils.c -I../../../libs/ffi/  -o cutils.so
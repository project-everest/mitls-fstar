#!/bin/bash

set -e

gcc -shared -fPIC cutils.c -o cutils.so
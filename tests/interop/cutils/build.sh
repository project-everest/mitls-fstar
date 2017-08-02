#!/bin/bash

set -e

OPENSSL_PATH=/home/user/dev/git/openssl/openssl/

gcc -shared -fPIC cutils.c 				\
		-I../../../../everest/mitls-fstar/libs/ffi/ \
		-I$OPENSSL_PATH/crypto/bio/ 	\
		-I$OPENSSL_PATH/crypto/include 	\
		-I$OPENSSL_PATH/include/ 		\
		-I$OPENSSL_PATH 				\
		$OPENSSL_PATH/libcrypto.so 		\
		-o cutils.so


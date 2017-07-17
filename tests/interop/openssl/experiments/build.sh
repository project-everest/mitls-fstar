#!/bin/bash

set -e

# rm -f server

OPENSSL_ROOT=/home/user/dev/git/openssl

# gcc server.c \
# 	-I$OPENSSL_ROOT/openssl/include/openssl/
# 	$OPENSSL_ROOT/openssl/libssl.so \
# 	$OPENSSL_ROOT/openssl/libcrypto.so \
# 	-o server

# echo $OPENSSL_ROOT/openssl/include/openssl/

gcc server.c \
	-I$OPENSSL_ROOT/openssl/include/ \
	$OPENSSL_ROOT/openssl/libcrypto.so \
	$OPENSSL_ROOT/openssl/libssl.so \
	-o server

gcc client.c \
	-I$OPENSSL_ROOT/openssl/include/ \
	$OPENSSL_ROOT/openssl/libcrypto.so \
	$OPENSSL_ROOT/openssl/libssl.so \
	-o client
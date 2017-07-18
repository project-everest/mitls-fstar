#!/bin/bash

set -e

OPENSSL_ROOT=/home/user/dev/git/openssl

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
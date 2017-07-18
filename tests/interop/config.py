# configs for running pytester

import logging

## Check out {everest, everest-interop} parallel to each other. 

MITLS_SO_PATH               = "../../../everest/mitls-fstar/src/tls/libmitls.so"
SERVER_CERT_PATH            = "../../../everest/mitls-fstar/data/server-ecdsa.crt" 
SERVER_KEY_PATH             = "../../../everest/mitls-fstar/data/server-ecdsa.key"
SERVER_CA_PATH              = "../../../everest/mitls-fstar/data/ca.crt"

MITLS_OPENSSL_PATH 			= '../../../everest/FStar/ucontrib/CoreCrypto/ml/openssl/libcrypto.so'
OPENSSL_PATH 				= '/home/user/dev/git/openssl/openssl/libssl.so'

LOG_LEVEL = logging.DEBUG

def set_log_level( logLevel ):
	global LOG_LEVEL
	# print( "set_log_level( %d )" % logLevel )
	LOG_LEVEL = logLevel

def set_mitls_so_path( filename ):
	global MITLS_SO_PATH
	print("config set MITLS_SO_PATH to " + filename)
	MITLS_SO_PATH = filename

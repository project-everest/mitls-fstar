# configs for running pytester
#for docker
import logging

## Check out {everest, everest-interop} parallel to each other. 

MITLS_SO_PATH               = "./mitls-dependencies/libmitls.so"
SERVER_CERT_PATH            = "./mitls-dependencies/server-ecdsa.crt" 
SERVER_KEY_PATH             = "./mitls-dependencies/server-ecdsa.key"
SERVER_CA_PATH              = "./mitls-dependencies/ca.crt"

MITLS_OPENSSL_PATH 			= './mitls-dependencies/libcrypto.so'
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

# configs for running pytester
#for docker
import logging

## Check out {everest, everest-interop} parallel to each other. 


MITLS_SO_PATH               = "./mitls-dependencies/libmitls.so"
SERVER_CERT_PATH            = { 'ECDSA+SHA256' : "certificates/ecdsa/ecdsa_secp256r1_sha256.crt",
								'ECDSA+SHA384' : "certificates/ecdsa/ecdsa_secp384r1_sha384.crt",
								'ECDSA+SHA512' : "certificates/ecdsa/ecdsa_secp521r1_sha512.crt", }
SERVER_KEY_PATH             = { 'ECDSA+SHA256' : "certificates/ecdsa/ecdsa_secp256r1_sha256.key",
								'ECDSA+SHA384' : "certificates/ecdsa/ecdsa_secp384r1_sha384.key",
								'ECDSA+SHA512' : "certificates/ecdsa/ecdsa_secp521r1_sha512.key", }
SERVER_CA_PATH              = "certificates/ecdsadata/ca.crt"
NSS_KEY_DATABASE_PATH		= { 'ECDSA+SHA256' : "certificates/ecdsa/db-256",
								'ECDSA+SHA384' : "certificates/ecdsa/db-384",
								'ECDSA+SHA512' : "certificates/ecdsa/db-512", }

MITLS_OPENSSL_PATH 			= './mitls-dependencies/libcrypto.so.1.1'
OPENSSL_PATH 				= './openssl-dependencies/libssl.so.1.1'


LOG_LEVEL = logging.DEBUG

def set_log_level( logLevel ):
	global LOG_LEVEL
	# print( "set_log_level( %d )" % logLevel )
	LOG_LEVEL = logLevel

def set_mitls_so_path( filename ):
	global MITLS_SO_PATH
	print("config set MITLS_SO_PATH to " + filename)
	MITLS_SO_PATH = filename

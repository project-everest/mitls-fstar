#!/bin/bash
set -e
set -v

NSS_PATH=/home/user/dev/nightly-nss/dist/Linux4.10_x86_64_cc_glibc_PTH_64_DBG.OBJ/
LD_LIBRARY_PATH=$NSS_PATH/lib
# create database directory:

rm -rf db-256
rm -rf db-384
rm -rf db-512

mkdir db-256
mkdir db-384
mkdir db-512

# Create empty database. Please use 12345678 as password
$NSS_PATH/bin/certutil -N -d db-256
$NSS_PATH/bin/certutil -N -d db-384
$NSS_PATH/bin/certutil -N -d db-512

# Convert your private key and certificates to pkcs12 format. The output file is server.pfx
openssl pkcs12 -export -out ecdsa_secp256r1_sha256.pfx -inkey ecdsa_secp256r1_sha256.key -in ecdsa_secp256r1_sha256.crt -certfile ca.crt 
openssl pkcs12 -export -out ecdsa_secp384r1_sha384.pfx -inkey ecdsa_secp384r1_sha384.key -in ecdsa_secp384r1_sha384.crt -certfile ca.crt 
openssl pkcs12 -export -out ecdsa_secp521r1_sha512.pfx -inkey ecdsa_secp521r1_sha512.key -in ecdsa_secp521r1_sha512.crt -certfile ca.crt

# Add private key and certificate to database:
$NSS_PATH/bin/pk12util -i ecdsa_secp256r1_sha256.pfx -d  db-256
$NSS_PATH/bin/pk12util -i ecdsa_secp384r1_sha384.pfx -d  db-384
$NSS_PATH/bin/pk12util -i ecdsa_secp521r1_sha512.pfx -d  db-512


#Listing the certificates in your database:
#$NSS_PATH/bin/certutil -L -d db 

#Listing keys
#$NSS_PATH/bin/certutil -K -d db 




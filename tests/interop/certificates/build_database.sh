NSS_PATH=/home/user/dev/nss-3.30.2/dist/Linux4.8_x86_64_cc_glibc_PTH_64_DBG.OBJ/bin

# create database directory:
mkdir db

# Create empty database. Please use 12345678 as password
$NSS_PATH/certutil -N -d db

# Convert your private key and certificates to pkcs12 format. The output file is server.pfx
openssl pkcs12 -export -out server.pfx -inkey server-ecdsa.key -in server-ecdsa.crt -certfile ca.crt

# Add private key and certificate to database:
$NSS_PATH/pk12util -i server.pfx -d  db

# Listing the certificates in your database:
#	%NSS_PATE%\certutil -L -d db 

# Listing keys
# %NSS_PATE%\certutil -K -d db 


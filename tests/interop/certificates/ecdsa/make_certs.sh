
openssl req -newkey rsa:4096 -nodes -keyout ca.key -x509 -days 3650 -out ca.crt -subj "/C=US/ST=WA/L=localCA/O=CAorg/OU=myCAunit/CN=CA.com"


# SHA256 key
openssl ecparam -genkey -name secp256r1 -out ecdsa_secp256r1_sha256.key
openssl req -new -sha384 -key ecdsa_secp256r1_sha256.key -nodes -out ecdsa_secp256r1_sha256.csr -subj "/C=US/ST=WA/L=local/O=org/OU=myunit/CN=test_server.com"
openssl x509 -req -in ecdsa_secp256r1_sha256.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out ecdsa_secp256r1_sha256.crt

# SHA384 key
openssl ecparam -genkey -name secp384r1 -out ecdsa_secp384r1_sha384.key
openssl req -new -sha384 -key ecdsa_secp384r1_sha384.key -nodes -out ecdsa_secp384r1_sha384.csr -subj "/C=US/ST=WA/L=local/O=org/OU=myunit/CN=test_server.com"
openssl x509 -req -in ecdsa_secp384r1_sha384.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out ecdsa_secp384r1_sha384.crt

# SHA512 key
openssl ecparam -genkey -name secp521r1 -out ecdsa_secp521r1_sha512.key
openssl req -new -sha384 -key ecdsa_secp521r1_sha512.key -nodes -out ecdsa_secp521r1_sha512.csr -subj "/C=US/ST=WA/L=local/O=org/OU=myunit/CN=test_server.com"
openssl x509 -req -in ecdsa_secp521r1_sha512.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out ecdsa_secp521r1_sha512.crt



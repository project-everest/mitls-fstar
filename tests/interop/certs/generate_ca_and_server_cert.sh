 #!/bin/bash

set -e

openssl req -newkey rsa:4096 -nodes -keyout ca.key -x509 -days 3650 -out ca.crt

openssl req -newkey rsa:2048 -nodes -keyout test_server.key -out test_server.csr

openssl req -in test_server.csr -noout -text

openssl x509 -req -in test_server.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out test_server.crt
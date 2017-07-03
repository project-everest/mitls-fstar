set NSS_PATE=c:\dev\nss-3.30.2\dist\WIN954.0_DBG.OBJ\bin\

REM create database directory:
mkdir db

REM Create empty database. Please use 12345678 as password
%NSS_PATE%\certutil -N -d db

REM Convert your private key and certificates to pkcs12 format. The output file is server.pfx
openssl pkcs12 -export -out server.pfx -inkey server-ecdsa.key -in server-ecdsa.crt -certfile ca.crt

REM Add private key and certificate to database:
%NSS_PATE%\pk12util -i server.pfx -d  db

REM Listing the certificates in your database:
REM	%NSS_PATE%\certutil -L -d db 

REM Listing keys
REM %NSS_PATE%\certutil -K -d db 


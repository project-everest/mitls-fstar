Linux
-----

1. Edit build.sh, update OPENSSL_PATH to location of OpenSSL supporting TLS 1.3
2. Run ./build.cmd



Windows
-------
1. Start Visual Studio command line environment (e.g., at C:\Program Files\Microsoft Visual Studio 14.0\Common7\Tools\VsDevCmd.bat)
2. Run `cl.exe /LD cutils.c`
3. Support for OpenSSL is not working on Windows yet. 

<h1>Building</h1>

Until the tester is incorporated into the everest build system, it will require manual building. To build the tester, open the <b>Tester.sln</b> file, found in the root of the solution directory, with Visual Studio 2017. The solution requires three library files, <b>libmitls.lib</b>, <b>libmipki.lib</b> and <b>libquiccrypo.lib</b> which should all be present in the <b>\Tester</b> subdirectory. These libraries are built using the everest script:-

  ./everest -j XX -windows -opt make drop qbuild

By default Visual studio will create the final executable in an "\X64\Debug" subdirectory in the solution. 

<h1>Running</h1>

To run the tester, there are a number of run-time dependencies:-

  1) The tester expects to find the dll files, "libmitls.dll", "libmipki.dll", "libcrypto-1_1-x64.dll" and "libquiccrypto.dll" either in the "\Tester" subdirectory or in the path.

  2) The certificate files should either be copied to the "\Tester" subdirectory or the tester can be invoked from the "everest\mitls-fstar\data" directory. Three certificate files are used by default, "CAFile.pem" is the certificate authority file. "server-ecdsa.crt" is the security certificate file and "server-ecdsa.key" is the certificate key file.

Then type tester.exe to run the tester.

When running Tester.exe with no arguments, it will generate the help text:-
<code><pre>
           TLS/DTLS Tester
            Version 0.0.2
(c) Microsoft Research 21st August 2018

Usage: Tester.exe [Arguments...]

  -v              Be verbose in console output (otherwise no console output except errors)
  -d              Turn on console debugging output
  -f:filename     Use file to specify server names (otherwise tester uses google.com)
  -c              Do libmitls as client TLS and DTLS tests
  -s              Do libmitls as client & server TLS and DTLS tests
  -i              Do libmitls as client interoperability TLS and DTLS tests
  -x              Do libmitls as server interoperability TLS and DTLS tests
  -t              Do TLS part of any tests
  -q              Do QUIC part of any tests
  -l:tlsversion   Specify TLS version number to support (default is '1.3')
  -p:port number  Specify port number to use (default is 443)
  -o:hostname     Specify host name to use (default is 'google.com')
  -r:certfilename Use specified Server Certificate filename (default is 'server-ecdsa.crt')
  -k:keyfilename  Use specified Server certificate key filename (default is 'server-ecdsa.key')
  -a:authfilename Use specified Certificate Authority Chain filename (default is 'CAFile.pem')
</pre></code>
All the options except for "-f:filename", "-s", "i", "-x" are currently supported. The Component DLL currently produces copious amounts of debug output, but this is gathered into a file. If you want to see this output then choose the "-v" flag which makes the tester more verbose.

If no other arguments are given, the tester does not perform any tests. You have to enable the tests you want to run by using the "-c" and "-t" flags. There are no server or interoperability tests as yet so the "-s", "i", "-x" flags have no effect.

The tester has a built in TLS Decoder which can be enabled with the "-d" flag. The QUIC tests do not currently run correcly.

<h1>Output</h1>
The tester generates several output files in the "\Tester" directory but the main one is the "ComponentStatistics.csv" file which is a summary of the test results. More details of the measurements are stored in the "RecordedMeasurements.csv" file. The file whose name starts with "RedirectedStandardOutput" is the DLL debug output for the test run.

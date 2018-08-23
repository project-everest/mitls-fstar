By default Visual studio will create the final executable in a subdirectory in the solution. 

To run the tester, there are a number of run-time dependencies:-

  1) The tester expects to find the dll files (libmitls.dll, libmipki.dll and libcryptoXXX.dll) either in the TESTER subdirectory or in the path.

  2) The certificate files should either be copied to the Tester subdirectory or the tester can be invoked from the data directory.

Then type tester.exe to run the tester.

When running Tester.exe with no arguments will generate the help text:-

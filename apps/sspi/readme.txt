Readme for mitls-fstar/apps/sspi
================================

What it does
============
It implements a Windows SSP (Security Support Provider), which implements the
SSPI (Security Support Provider Interface).  This same interface is used by
applications that wish to use the built-in Windows support for TLS (schannel).

Applications generally call AcquireCredentialsHandleW() and pass
UNISP_NAME_W as the name of the SSP.  With the miTLS SSP installed, apps can
pass MITLS_NAME_W ("Everest miTLS     Security Protocol Provider") instead,
and invoke miTLS.

Further, this DLL is capable of two hacks, to inject itself in place of
schannel without the need to modify the calling application:
1. It will patch the SSP name on the callstack as it is loaded, enabling
   the first AcquireCredentialsHandle() call to be redirected to miTLS.
2. It can use MSR Detours to intercept future calls to 
   AcquireCredentialsHandle() to substitute miTLS for schannel.

Building
========
This project was developed with Visual Studio 2017.  It will most likely build 
with other versions of Visual Studio too.

The Debug and Release targets build a standalone SSP.

The Detours targets require MSR Detours to be installed and built.  To do this:
- clone Detours from https://github.com/microsoft/detours to
mitls-fstar\apps\sspi\Detours (so the Detours directory contains README.md, makefile,
src\ and samples\ directories)
- build Detours for amd64:
    - open a VS2017 x64 command prompt
    - cd mitls-fstar\apps\sspi\Detours
    - nmake
- also make sure the entire 'everest make drop qbuild' has completed
- now build the miTLS_SSP.sln.

Installing
==========
Copy the miTLS_SSP.dll to a directory on the machine which does not contain
any spaces in the pathname.  Make sure libmitls.dll, libmipki.dll, and their
Cygwin and mingw32 dependencies are on your PATH.

set PATH=c:\users\barrybo\everest\mitls-fstar\src\windows\mitls;%PATH%
set PATH=c:\users\barrybo\everest\mitls-fstar\src\pki;%PATH%
set PATH=c:\users\barrybo\everest\mitls-fstar\src\windows\evercrypt;%PATH%

Then from an elevated command prompt, run:
  regsvr32 miTLS_SSP.dll

This modifies
HKEY_LOCAL_MACHINE\SYSTEM\CurrentControlSet\Control\SecurityProviders.   The
value is "SecurityProviders" and it is a space-delimited set of DLL names.
Append a space and the fully qualified path to miTLS_SSP.dll.

Uninstalling
============
From an elevated command prompt, run:
   regsvr32 /u miTLS_SSP.dll

Using
=====
Make sure libmitls.dll and its Cygwin and mingw32 dependencies are on your 
PATH.

set PATH=c:\users\barrybo\everest\mitls-fstar\src\windows\mitls;%PATH%
set PATH=c:\users\barrybo\everest\mitls-fstar\src\pki;%PATH%
set PATH=c:\users\barrybo\everest\mitls-fstar\src\windows\evercrypt;%PATH%

Once the registry key is present, Windows sspicli.dll, loaded into Windows
applications, will enumerate the SecurityProviders key and load all of the
providers into memory.

The miTLS provider defaults to failing its initialization code, so that it
is very unlikely that it will break any application due to bugs or missing
features.  sspicli.dll will unload it without complaint, if initialization
fails.

To enable the provider for a specific application, use the MITLS_ATTACH_SSP
environment variable.  Set it to the EXE filename (ie. "iexplore.exe" or
powershell.exe") with no path component.  The name is case insensitive.

The provider will default to TLS 1.2 for all connections.  To override, also
set MITLS_SCHANNEL_VERSION to a string, "1.2" or "1.3".

Set MITLS_SCHANNEL_CIPHER_SUITES to override the default cipher suites.

Examples
========
set MITLS_ATTACH_SSP=curl.exe
%windir%\system32\curl.exe https://www.bing.com

set MITLS_ATTACH_SSP=powershell.exe
powershell.exe wget https://www.bing.com

set MITLS_ATTACH_SSP=iexplore.exe
"\Program Files\internet explorer\iexplore.exe" https://www.bing.com
 - Use Internet Options / Advanced and check "Enable 64-bit Processes for
   Enhanced Protected Mode"
 - note, iexplore will open bing.com and fetch the contents, but
   it will also fail to negotiate with other TLS servers, such as
   iecvlist.microsoft.com, as its signature algorithms don't match
   what miTLS offers by default.

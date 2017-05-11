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

The Detours targets require MSR Detours to be installed and built, in a 
directory named Detours, under the current directory.

Installing
==========
Copy the miTLS_SSP.dll to a directory on the machine which does not contain
any spaces in the pathname.  Then use regedit to modify
HKEY_LOCAL_MACHINE\SYSTEM\CurrentControlSet\Control\SecurityProviders.   The
value is "SecurityProviders" and it is a space-delimited set of DLL names.
Append a space and the fully qualified path to miTLS_SSP.dll.

Using
=====
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

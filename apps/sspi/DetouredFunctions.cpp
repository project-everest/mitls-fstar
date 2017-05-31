//////////////////////////////////////////////////////////////////////////////
//
//  Detours support for intercepting apps that use schannel, to redirect
//  into the miTLS SSP code.
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
#define SECURITY_WIN32  // tell Sspi.h which feature set we consume
#define WINNT 1         // avoid conflict between ddraw.h and winerror.h
#include <Windows.h>
#include <sspi.h>
#include <NTSecAPI.h>
#include <NtSecPkg.h>
#include <SubAuth.h> // for some NTSTATUS_ constants
#include <minidrv.h> // for logging functions
#include "mitls.h"
#include <schnlsp.h>

#if USE_DETOURS
#include "detours.h"
#endif

#if DBG
INT giDebugLevel = DBG_VERBOSE;
#endif

ACQUIRE_CREDENTIALS_HANDLE_FN_W Real_AcquireCredentialsHandleW = AcquireCredentialsHandleW;
ACQUIRE_CREDENTIALS_HANDLE_FN_A Real_AcquireCredentialsHandleA = AcquireCredentialsHandleA;

SECURITY_STATUS SEC_ENTRY
Mine_AcquireCredentialsHandleW(
#if ISSP_MODE == 0     // For Kernel mode
    _In_opt_  PSECURITY_STRING pPrincipal,
    _In_      PSECURITY_STRING pPackage,
#else
    _In_opt_  LPWSTR pszPrincipal,                // Name of principal
    _In_      LPWSTR pszPackage,                  // Name of package
#endif
    _In_      unsigned long fCredentialUse,       // Flags indicating use
    _In_opt_  void * pvLogonId,           // Pointer to logon ID
    _In_opt_  void * pAuthData,           // Package specific data
    _In_opt_  SEC_GET_KEY_FN pGetKeyFn,           // Pointer to GetKey() func
    _In_opt_  void * pvGetKeyArgument,    // Value to pass to GetKey()
    _Out_     PCredHandle phCredential,           // (out) Cred Handle
    _Out_opt_ PTimeStamp ptsExpiry                // (out) Lifetime (optional)
)
{
    _PrintEnter("_AcquireCredentialsHandleW(%ls %ls %x %x %x %x %x %x %x\n",
        (pszPrincipal == NULL) ? L"(NULL)" : pszPrincipal,
        (pszPackage == NULL) ? L"(NULL)" : pszPackage,
        fCredentialUse,
        pvLogonId,
        pAuthData,
        pGetKeyFn,
        pvGetKeyArgument,
        phCredential,
        ptsExpiry);

    SECURITY_STATUS rv = 0;
    if (_wcsicmp(pszPackage, UNISP_NAME_W) == 0 || _wcsicmp(pszPackage, DEFAULT_TLS_SSP_NAME_W) == 0) {
        // Redirect to the miTLS SSP
        pszPackage = MITLS_NAME_W;
    }
    rv = Real_AcquireCredentialsHandleW(
        pszPrincipal,
        pszPackage,
        fCredentialUse,
        pvLogonId,
        pAuthData,
        pGetKeyFn,
        pvGetKeyArgument,
        phCredential,
        ptsExpiry);
    _PrintExit("_AcquireCredentialsHandleW(,) -> %p %x\n", *phCredential, rv);
    return rv;
}

SECURITY_STATUS SEC_ENTRY
Mine_AcquireCredentialsHandleA(
#if ISSP_MODE == 0     // For Kernel mode
    _In_opt_  PSECURITY_STRING pPrincipal,
    _In_      PSECURITY_STRING pPackage,
#else
    _In_opt_  LPSTR pszPrincipal,                // Name of principal
    _In_      LPSTR pszPackage,                  // Name of package
#endif
    _In_      unsigned long fCredentialUse,       // Flags indicating use
    _In_opt_  void * pvLogonId,           // Pointer to logon ID
    _In_opt_  void * pAuthData,           // Package specific data
    _In_opt_  SEC_GET_KEY_FN pGetKeyFn,           // Pointer to GetKey() func
    _In_opt_  void * pvGetKeyArgument,    // Value to pass to GetKey()
    _Out_     PCredHandle phCredential,           // (out) Cred Handle
    _Out_opt_ PTimeStamp ptsExpiry                // (out) Lifetime (optional)
)
{
    _PrintEnter("_AcquireCredentialsHandleA(%s %s %x %x %x %x %x %x %x\n",
        (pszPrincipal == NULL) ? "(NULL)" : pszPrincipal,
        (pszPackage == NULL) ? "(NULL)" : pszPackage,
        fCredentialUse,
        pvLogonId,
        pAuthData,
        pGetKeyFn,
        pvGetKeyArgument,
        phCredential,
        ptsExpiry);

    SECURITY_STATUS rv = 0;
    if (_stricmp(pszPackage, UNISP_NAME_A) == 0 || _stricmp(pszPackage, DEFAULT_TLS_SSP_NAME_A) == 0) {
        // Redirect to the miTLS SSP
        pszPackage = MITLS_NAME_A;
    }
    rv = Real_AcquireCredentialsHandleA(
        pszPrincipal,
        pszPackage,
        fCredentialUse,
        pvLogonId,
        pAuthData,
        pGetKeyFn,
        pvGetKeyArgument,
        phCredential,
        ptsExpiry);
    _PrintExit("_AcquireCredentialsHandleA(,) -> %p %x\n", *phCredential, rv);
    return rv;
}



VOID _PrintCommon(const CHAR *psz, va_list args)
{
    CHAR szBuf[1024];
    vsprintf_s(szBuf, psz, args);
    VERBOSE(("%s\n", szBuf));
}

VOID _PrintEnter(const CHAR *psz, ...)
{
    DWORD dwErr = GetLastError();

    CHAR szBuf[128];
    sprintf_s(szBuf, "%x Enter %s", GetCurrentThreadId(), psz);
    va_list  args;
    va_start(args, psz);
    _PrintCommon(szBuf, args);
    SetLastError(dwErr);
}

VOID _PrintExit(const CHAR *psz, ...)
{
    DWORD dwErr = GetLastError();

    CHAR szBuf[128];
    sprintf_s(szBuf, "%x Leave %s", GetCurrentThreadId(), psz);
    va_list  args;
    va_start(args, psz);
    _PrintCommon(szBuf, args);
    SetLastError(dwErr);
}

VOID _Print(const CHAR *psz, ...)
{
    DWORD dwErr = GetLastError();

    CHAR szBuf[128];
    sprintf_s(szBuf, "%x %s", GetCurrentThreadId(), psz);
    va_list  args;
    va_start(args, psz);
    _PrintCommon(szBuf, args);
    SetLastError(dwErr);
}

VOID _PrintDump(SOCKET socket, PCHAR pszData, INT cbData)
{
    if (pszData && cbData > 0) {
        CHAR szBuffer[256];
        PCHAR pszBuffer = szBuffer;
        INT cbBuffer = 0;
        INT nLines = 0;

        while (cbData > 0) {
#if ABBREVIATE
            if (nLines > 20) {
                *pszBuffer++ = '.';
                *pszBuffer++ = '.';
                *pszBuffer++ = '.';
                cbBuffer += 3;
                break;
            }
#endif

            if (*pszData == '\t') {
                *pszBuffer++ = '\\';
                *pszBuffer++ = 't';
                cbBuffer += 2;
                pszData++;
                cbData--;
                continue;
            }
            if (*pszData == '\r') {
                *pszBuffer++ = '\\';
                *pszBuffer++ = 'r';
                cbBuffer += 2;
                pszData++;
                cbData--;
                continue;
            }
            else if (*pszData == '\n') {
                *pszBuffer++ = '\\';
                *pszBuffer++ = 'n';
                cbBuffer += 2;
                *pszBuffer++ = '\0';
                _Print("%p:   %hs\n", socket, szBuffer);
                nLines++;
                pszBuffer = szBuffer;
                cbBuffer = 0;
                pszData++;
                cbData--;
                continue;
            }
            else if (cbBuffer >= 80) {
                *pszBuffer++ = '\0';
                _Print("%p:   %hs\n", socket, szBuffer);
                nLines++;
                pszBuffer = szBuffer;
                cbBuffer = 0;
            }

            if (*pszData < ' ' || *pszData >= 127) {
                *pszBuffer++ = '\\';
                *pszBuffer++ = 'x';
                *pszBuffer++ = "0123456789ABCDEF"[(*pszData & 0xf0) >> 4];
                *pszBuffer++ = "0123456789ABCDEF"[(*pszData & 0x0f)];
                cbBuffer += 4;
            }
            else {
                *pszBuffer++ = *pszData;
            }
            cbBuffer++;
            pszData++;
            cbData--;
        }

        if (cbBuffer > 0) {
            *pszBuffer++ = '\0';
            _Print("%p:   %hs", socket, szBuffer);
        }
    }
}

#if USE_DETOURS
PCHAR DetRealName(PCHAR psz)
{
    PCHAR pszBeg = psz;
    // Move to end of name.
    while (*psz) {
        psz++;
    }
    // Move back through A-Za-z0-9 names.
    while (psz > pszBeg &&
        ((psz[-1] >= 'A' && psz[-1] <= 'Z') ||
        (psz[-1] >= 'a' && psz[-1] <= 'z') ||
            (psz[-1] >= '0' && psz[-1] <= '9'))) {
        psz--;
    }
    return psz;
}

VOID DetAttach(PVOID *ppbReal, PVOID pbMine, PCHAR psz)
{
    LONG l = DetourAttach(ppbReal, pbMine);
    if (l != 0) {
        ERR(("Attach failed: `%s': error %d\n", DetRealName(psz), l));
    }
}

VOID DetDetach(PVOID *ppbReal, PVOID pbMine, PCHAR psz)
{
    LONG l = DetourDetach(ppbReal, pbMine);
    if (l != 0) {
        ERR(("Detach failed: `%s': error %d\n", DetRealName(psz), l));
    }
}

#define ATTACH(x)       DetAttach(&(PVOID&)Real_##x,Mine_##x,#x)
#define DETACH(x)       DetDetach(&(PVOID&)Real_##x,Mine_##x,#x)

// To hook:
// AcquireCredentialsHandleA/W
// schannel:  
//  SslCrackCertificate
//  SslEmptyCacheA/W
//  SslFreeCertificate
//  SslFreeCustomBuffer
//  SslGenerateRandomBits
//  SslGetMaximumKeySize
//  SslGetServerIdentity
//  SslLoadCertificate

bool AttachDetours(VOID)
{
    // The C compiler initialize the Real_* variables to point at thunk code inside
    // mitls_ssp.dll, causing Detours to hook the thunk code, not the SspiCli
    // entrypoints.
    HMODULE h = LoadLibraryW(L"SspiCli.dll");
    Real_AcquireCredentialsHandleA = (ACQUIRE_CREDENTIALS_HANDLE_FN_A)GetProcAddress(h, "AcquireCredentialsHandleA");
    Real_AcquireCredentialsHandleW = (ACQUIRE_CREDENTIALS_HANDLE_FN_W)GetProcAddress(h, "AcquireCredentialsHandleW");

    DetourTransactionBegin();
    DetourUpdateThread(GetCurrentThread());

    ATTACH(AcquireCredentialsHandleA);
    ATTACH(AcquireCredentialsHandleW);

    return DetourTransactionCommit() == NO_ERROR;
}

bool DetachDetours(VOID)
{
    DetourTransactionBegin();
    DetourUpdateThread(GetCurrentThread());

    DETACH(AcquireCredentialsHandleA);
    DETACH(AcquireCredentialsHandleW);

    return DetourTransactionCommit() == NO_ERROR;
}

#endif // USE_DETOURS

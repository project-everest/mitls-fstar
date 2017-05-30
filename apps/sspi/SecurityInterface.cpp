//////////////////////////////////////////////////////////////////////////////
//
//  Implements a Windows SSP on top of miTLS.  This is a usermode SSP
//  that loads and runs inside applications.  It is not loaded into
//  LSASS or kernelmode.
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
#define SECURITY_WIN32 // tell Sspi.h which feature set we consume
#define WINNT 1         // avoid conflict between ddraw.h and winerror.h
#include <Windows.h>
#include <sspi.h>
#include <NTSecAPI.h>
#include <NtSecPkg.h>
#include <SubAuth.h> // for some NTSTATUS_ constants
#include <minidrv.h> // for logging functions
#include <schannel.h>
#include "mitls.h"

HMODULE g_hModule;

SECURITY_STATUS SEC_ENTRY
SpiEnumerateSecurityPackagesW(
    _Out_    unsigned long * pcPackages,     // Receives num. packages
    _Outptr_ PSecPkgInfoW  * ppPackageInfo   // Receives array of info
);
SECURITY_STATUS
SEC_ENTRY
SpiQueryCredentialsAttributesW(
    __in    PCredHandle phCredential,
    __in    ULONG       ulAttribute,
    __inout PVOID       pBuffer
);
SECURITY_STATUS
SEC_ENTRY
SpiAcquireCredentialsHandleW(
    __in_opt  LPWSTR         pszPrincipal,
    __in      LPWSTR         pszPackageName,
    __in      ULONG          fCredentialUse,
    __in_opt  PVOID          pvLogonId,
    __in_opt  PVOID          pAuthData,
    __in_opt  SEC_GET_KEY_FN pGetKeyFn,
    __in_opt  PVOID          pvGetKeyArgument,
    __out     PCredHandle    phCredential,
    __out_opt PTimeStamp     ptsExpiry
);
SECURITY_STATUS
SEC_ENTRY
SpiFreeCredentialsHandle(
    __in PCredHandle phCredential
);
SECURITY_STATUS
SEC_ENTRY
SpiInitializeSecurityContextW(
    __in_opt    PCredHandle      phCredential,
    __in_opt    PCtxtHandle      phContext,
    __in_opt    LPWSTR           pszTargetName,
    __in        ULONG            fContextReq,
    __in        ULONG            Reserved1,
    __in        ULONG            TargetDataRep,
    __in_opt    PSecBufferDesc   pInput,
    __in        ULONG            Reserved2,
    __inout_opt PCtxtHandle      phNewContext,
    __inout_opt PSecBufferDesc   pOutput,
    __out       PULONG           pfContextAttr,
    __out_opt   PTimeStamp       ptsExpiry
);
SECURITY_STATUS
SEC_ENTRY
SpiAcceptSecurityContext(
    __in_opt    PCredHandle      phCredential,
    __in_opt    PCtxtHandle      phContext,
    __in_opt    PSecBufferDesc   pInput,
    __in        ULONG            fContextReq,
    __in        ULONG            TargetDataRep,
    __inout_opt PCtxtHandle      phNewContext,
    __inout_opt PSecBufferDesc   pOutput,
    __out       PULONG           pfContextAttr,
    __out_opt   PTimeStamp       ptsExpiry
);
SECURITY_STATUS
SEC_ENTRY
SpiCompleteAuthToken(
    __in PCtxtHandle    phContext,
    __in PSecBufferDesc pInput
);
SECURITY_STATUS
SEC_ENTRY
SpiDeleteSecurityContext(
    __in PCtxtHandle phContext
);
SECURITY_STATUS
SEC_ENTRY
SpiApplyControlToken(
    __in PCtxtHandle    phContext,
    __in PSecBufferDesc pInput
);
SECURITY_STATUS
SEC_ENTRY
SpiQueryContextAttributesW(
    __in  PCtxtHandle phContext,
    __in  ULONG       ulAttribute,
    __out PVOID       pBuffer
);
SECURITY_STATUS
SEC_ENTRY
SpiImpersonateSecurityContext(
    __in PCtxtHandle phContext
);
SECURITY_STATUS
SEC_ENTRY
SpiRevertSecurityContext(
    __in PCtxtHandle phContext
);
SECURITY_STATUS
SEC_ENTRY
SpiMakeSignature(
    __in PCtxtHandle    phContext,
    __in ULONG          fQOP,
    __in PSecBufferDesc pMessage,
    __in ULONG          MessageSeqNo
);
SECURITY_STATUS
SEC_ENTRY
SpiVerifySignature(
    __in        PCtxtHandle     phContext,
    __in        PSecBufferDesc  pMessage,
    __in        ULONG           MessageSeqNo,
    __out_opt   ULONG          *pfQOP
);
SECURITY_STATUS SEC_ENTRY
SpiFreeContextBuffer(
    void SEC_FAR *      pvContextBuffer
);
SECURITY_STATUS
SEC_ENTRY
SpiQuerySecurityPackageInfoW(
    __in        LPWSTR        pszPackageName,
    __deref_out PSecPkgInfoW *pPackageInfo
);
SECURITY_STATUS
SEC_ENTRY
SpiExportSecurityContext(
    __in  PCtxtHandle ContextHandle,
    __in  ULONG       Flags,
    __out PSecBuffer  MarshalledContext,
    __out PHANDLE     TokenHandle
);
SECURITY_STATUS
SEC_ENTRY
SpiImportSecurityContextW(
    __in  LPWSTR      PackageName,
    __in  PSecBuffer  MarshalledContext,
    __in  HANDLE      TokenHandle,
    __out PCtxtHandle ContextHandle
);
SECURITY_STATUS
SEC_ENTRY
SpiAddCredentialsW(
    __in      PCredHandle    phCredentials,
    __in_opt  LPWSTR         pszPrincipal,
    __in      LPWSTR         pszPackageName,
    __in      ULONG          fCredentialUse,
    __in_opt  PVOID          pAuthData,
    __in_opt  SEC_GET_KEY_FN pGetKeyFn,
    __in_opt  PVOID          pvGetKeyArgument,
    __out_opt PTimeStamp     ptsExpiry
);
SECURITY_STATUS
SEC_ENTRY
SpiQuerySecurityContextToken(
    __in  PCtxtHandle phContext,
    __out PHANDLE     TokenHandle
);
SECURITY_STATUS
SEC_ENTRY
SpiEncryptMessage(
    __in    PCtxtHandle     phContext,
    __in    ULONG           fQOP,
    __inout PSecBufferDesc  pMessage,
    __in    ULONG           MessageSeqNo
);
SECURITY_STATUS
SEC_ENTRY
SpiDecryptMessage(
    __in      PCtxtHandle    phContext,
    __inout   PSecBufferDesc pMessage,
    __in      ULONG          MessageSeqNo,
    __out_opt ULONG *        pfQOP
);
SECURITY_STATUS
SEC_ENTRY
SpiSetContextAttributesW(
    __in PCtxtHandle            phContext,
    __in ULONG                  ulAttribute,
    __in_bcount(cbBuffer) PVOID pBuffer,
    __in ULONG                  cbBuffer
);
SECURITY_STATUS
SEC_ENTRY
SpiSetCredentialsAttributesW(
    __in PCredHandle            phCredential,
    __in ULONG                  ulAttribute,
    __in_bcount(cbBuffer) PVOID pBuffer,
    __in ULONG                  cbBuffer
);
#if ISSP_MODE != 0
SECURITY_STATUS
SEC_ENTRY
SpiChangeAccountPasswordW(
    __in    LPWSTR         pszPackageName,
    __in    LPWSTR         pszDomainName,
    __in    LPWSTR         pszAccountName,
    __in    LPWSTR         pszOldPassword,
    __in    LPWSTR         pszNewPassword,
    __in    BOOLEAN        bImpersonating,
    __in    ULONG          dwEncoded,
    __inout PSecBufferDesc pOutput
);
#endif
SECURITY_STATUS
SEC_ENTRY
SpiQueryContextAttributesExW(
    __in  PCtxtHandle phContext,              // Context to query
    __in  unsigned long ulAttribute,          // Attribute to query
    __out_bcount(cbBuffer) void * pBuffer,    // Buffer for attributes
    __in  unsigned long cbBuffer              // Length of buffer
);
SECURITY_STATUS
SEC_ENTRY
SpiQueryCredentialsAttributesExW(
    __in    PCredHandle phCredential,
    __in    ULONG       ulAttribute,
    __inout_bcount(cbBuffer) PVOID pBuffer,
    __in    ULONG       cbBuffer
);

SECURITY_STATUS
SEC_ENTRY SpiSealMessage(
    PCtxtHandle, unsigned long, PSecBufferDesc, unsigned long);

SECURITY_STATUS SEC_ENTRY
SpiUnsealMessage(
    PCtxtHandle ContextHandle,
    PSecBufferDesc Message,
    unsigned long Sequence,
    unsigned long __SEC_FAR * QOP
);

SecurityFunctionTable g_SecurityInterfaceTableW = {
    SECURITY_SUPPORT_PROVIDER_INTERFACE_VERSION,
    SpiEnumerateSecurityPackagesW,
    SpiQueryCredentialsAttributesW,
    SpiAcquireCredentialsHandleW,
    SpiFreeCredentialsHandle,
    NULL, // Reserved2
    SpiInitializeSecurityContextW,
    SpiAcceptSecurityContext,
    SpiCompleteAuthToken,
    SpiDeleteSecurityContext,
    SpiApplyControlToken,
    SpiQueryContextAttributesW,
    SpiImpersonateSecurityContext,
    SpiRevertSecurityContext,
    SpiMakeSignature,
    SpiVerifySignature,
    SpiFreeContextBuffer,
    SpiQuerySecurityPackageInfoW,
    SpiSealMessage, // Reserved3  sspicli.cpp's EncryptMessage() treats Reserved3 as SEAL_MESSAGE_FN and calls it
    SpiUnsealMessage, // Reserved4  sspicli.cpp's DecryptMessage() treats Reserved4 as UNSEAL_MESSAGE_FN and calls it
    SpiExportSecurityContext,
    SpiImportSecurityContextW,
    SpiAddCredentialsW,
    NULL, // Reserved8
    SpiQuerySecurityContextToken,
    SpiEncryptMessage,
    SpiDecryptMessage,
    SpiSetContextAttributesW,
    SpiSetCredentialsAttributesW,
#if ISSP_MODE != 0
    SpiChangeAccountPasswordW,
#else
    NULL, // Reserved9
#endif
    SpiQueryContextAttributesExW,
    SpiQueryCredentialsAttributesExW
};

// See SpGetInfo() for the source of these values
const SecPkgInfoW g_Package = {
    // fCapabilities...
    SECPKG_FLAG_INTEGRITY |     // Supports MakeSignature/VerifySignature
    SECPKG_FLAG_PRIVACY |       // Supports EncryptMessage/DecryptMessage
    SECPKG_FLAG_CONNECTION |    // Supports connection-style authentication
    SECPKG_FLAG_MULTI_REQUIRED |// Multiple legs are required for authentication
    SECPKG_FLAG_EXTENDED_ERROR |// Supports extended error handling
    SECPKG_FLAG_IMPERSONATION | // Supports Windows impersonation in server contexts
    SECPKG_FLAG_ACCEPT_WIN32_NAME | // Understands Windows principal and target names
    SECPKG_FLAG_MUTUAL_AUTH |   // Supports mutual authentication.
    SECPKG_FLAG_APPCONTAINER_PASSTHROUGH | // This package receives all calls from app container apps
    SECPKG_FLAG_STREAM,          // Supports stream semantics
    1, // wVersion of Driver
    SECPKG_ID_NONE, // wRPCID
    0x6000, // cbMaxToken
    // This string must be the same length as the "Microsoft Unified Security Protocol Provider" to support
    // patching for SECURITY_STRING struct on the stack, where the .Buffer will be patched but the .Length
    // and .MaximumLength will still have the original sizes present.
   //"Microsoft Unified Security Protocol Provider"
    MITLS_NAME_W,
    L"Everest Expedition miTLS" // Comment
};

extern "C"  PSecurityFunctionTable SEC_ENTRY SpiInitSecurityInterface(void)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return &g_SecurityInterfaceTableW;
}

void PatchSSPName(void)
{
    ULONG_PTR LowLimit;
    ULONG_PTR HighLimit;
    const size_t size = sizeof(UNISP_NAME_W); // size in bytes

    VERBOSE(("Patching this process to use SpiSSP in place of schannel\n"));

    GetCurrentThreadStackLimits(&LowLimit, &HighLimit);
    for (ULONG_PTR i = LowLimit; i < HighLimit; i += 8) {
        MEMORY_BASIC_INFORMATION mbi;
        VirtualQuery((LPCVOID)i, &mbi, sizeof(mbi));
        if (mbi.State != MEM_COMMIT) {
            // Skip this stack page if it isn't committed
            i += (4096 - 8);
            continue;
        }
        wchar_t **pStack = (wchar_t**)i;
        wchar_t *pData = *pStack;
        SIZE_T s = VirtualQuery(pData, &mbi, sizeof(mbi));
        if (s && mbi.State == MEM_COMMIT) { // If the potential data pointer points to a committed page, check its contents
            __try {
                if (memcmp(pData, UNISP_NAME_W, size) == 0) {
                    VERBOSE(("Patching stack address %p to point to miTLS (%p to %p)\n", pStack, *pStack, g_Package.Name));
                    *pStack = g_Package.Name;
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                ; // Do nothing
            }
        }
    }
}

SECURITY_STATUS SEC_ENTRY SpiEnumerateSecurityPackagesW(
    unsigned long *pcPackages,
    PSecPkgInfoW *ppwPackageInfo)
{
    VERBOSE(("%s\n", __FUNCTION__));
    if ((pcPackages == NULL) || (ppwPackageInfo == NULL)) {
        return SEC_E_INVALID_HANDLE;
    }

    wchar_t Var[_MAX_PATH];
    bool ShouldLoad = false;
    DWORD dw = GetEnvironmentVariableW(L"MITLS_ATTACH_SSP", Var, ARRAYSIZE(Var));
    if (dw > 0 && dw < ARRAYSIZE(Var)) { // Environment variable lookup succeeded
        wchar_t ModuleName[_MAX_PATH];
        GetModuleFileNameW(NULL, ModuleName, ARRAYSIZE(ModuleName));
        wchar_t *FileName = wcsrchr(ModuleName, '\\');
        if (FileName == NULL) {
            FileName = ModuleName;
        }
        else {
            FileName++; // Skip the '\\' character
        }
        if (_wcsicmp(Var, FileName) == 0) {
            ShouldLoad = true;
        }
    }
    if (!ShouldLoad) {
        // Refuse to load here, so that this process doesn't end up hanging onto a filesystem
        // lock on the DLL.
        return SEC_E_UNSUPPORTED_FUNCTION;
    }
    if (MITLS_Initialize() == FALSE) {
        ERR(("miTLS failed to initialize.  Unloading."));
        return SEC_E_UNSUPPORTED_FUNCTION;
    }

#if USE_DETOURS
    if (!AttachDetours()) {
        ERR(("AttachDetours failed.  Unloading."));
        return SEC_E_UNSUPPORTED_FUNCTION;
    }
#endif

    // Allocate with LocalAlloc() so FreeContextBuffer() can free it later
    PSecPkgInfoW p = (PSecPkgInfoW)LocalAlloc(LMEM_FIXED, sizeof(*p));
    if (p == NULL) {
        return SEC_E_INSUFFICIENT_MEMORY;
    }
    memcpy(p, &g_Package, sizeof(*p));
    *pcPackages = 1u;
    *ppwPackageInfo = p;

    PatchSSPName();
    return SEC_E_OK;
}

SECURITY_STATUS
SEC_ENTRY
SpiQueryCredentialsAttributesW(
    __in    PCredHandle phCredential,
    __in    ULONG       ulAttribute,
    __inout PVOID       pBuffer
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    // See https://msdn.microsoft.com/en-us/library/windows/desktop/aa379342(v=vs.85).aspx
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiAcquireCredentialsHandleW(
    __in_opt  LPWSTR         pszPrincipal,
    __in      LPWSTR         pszPackageName,
    __in      ULONG          fCredentialUse,
    __in_opt  PVOID          pvLogonId,
    __in_opt  PVOID          pAuthData,
    __in_opt  SEC_GET_KEY_FN pGetKeyFn,
    __in_opt  PVOID          pvGetKeyArgument,
    __out     PCredHandle    phCredential,
    __out_opt PTimeStamp     ptsExpiry
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    // See https://msdn.microsoft.com/en-us/library/windows/desktop/aa374712(v=vs.85).aspx

    SECURITY_STATUS st = MITLS_AcquireCredentialsHandleW(
        pszPrincipal,
        pszPackageName,
        fCredentialUse,
        pvLogonId,
        pAuthData,
        pGetKeyFn,
        pvGetKeyArgument,
        phCredential,
        ptsExpiry);

    VERBOSE(("%s ret 0x%x\n", __FUNCTION__, st));
    return st;
}

SECURITY_STATUS
SEC_ENTRY
SpiFreeCredentialsHandle(
    __in PCredHandle phCredential
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_FreeCredentialsHandle(phCredential);
}

SECURITY_STATUS
SEC_ENTRY
SpiInitializeSecurityContextW(
    __in_opt    PCredHandle      phCredential,
    __in_opt    PCtxtHandle      phContext,
    __in_opt    LPWSTR           pszTargetName,
    __in        ULONG            fContextReq,
    __in        ULONG            Reserved1,
    __in        ULONG            TargetDataRep,
    __in_opt    PSecBufferDesc   pInput,
    __in        ULONG            Reserved2,
    __inout_opt PCtxtHandle      phNewContext,
    __inout_opt PSecBufferDesc   pOutput,
    __out       PULONG           pfContextAttr,
    __out_opt   PTimeStamp       ptsExpiry
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_InitializeSecurityContextW(
        phCredential,
        phContext,
        pszTargetName,
        fContextReq,
        Reserved1,
        TargetDataRep,
        pInput,
        Reserved2,
        phNewContext,
        pOutput, 
        pfContextAttr,
        ptsExpiry
    );
}

SECURITY_STATUS
SEC_ENTRY
SpiAcceptSecurityContext(
    __in_opt    PCredHandle      phCredential,
    __in_opt    PCtxtHandle      phContext,
    __in_opt    PSecBufferDesc   pInput,
    __in        ULONG            fContextReq,
    __in        ULONG            TargetDataRep,
    __inout_opt PCtxtHandle      phNewContext,
    __inout_opt PSecBufferDesc   pOutput,
    __out       PULONG           pfContextAttr,
    __out_opt   PTimeStamp       ptsExpiry
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiCompleteAuthToken(
    __in PCtxtHandle    phContext,
    __in PSecBufferDesc pInput
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiDeleteSecurityContext(
    __in PCtxtHandle phContext
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_DeleteSecurityContext(phContext);
}

SECURITY_STATUS
SEC_ENTRY
SpiApplyControlToken(
    __in PCtxtHandle    phContext,
    __in PSecBufferDesc pInput
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_ApplyControlToken(phContext, pInput);
}

SECURITY_STATUS
SEC_ENTRY
SpiQueryContextAttributesW(
    __in  PCtxtHandle phContext,
    __in  ULONG       ulAttribute,
    __out PVOID       pBuffer
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_QueryContextAttributesW(phContext, ulAttribute, pBuffer);
}

SECURITY_STATUS
SEC_ENTRY
SpiImpersonateSecurityContext(
    __in PCtxtHandle phContext
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiRevertSecurityContext(
    __in PCtxtHandle phContext
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiMakeSignature(
    __in PCtxtHandle    phContext,
    __in ULONG          fQOP,
    __in PSecBufferDesc pMessage,
    __in ULONG          MessageSeqNo
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiVerifySignature(
    __in        PCtxtHandle     phContext,
    __in        PSecBufferDesc  pMessage,
    __in        ULONG           MessageSeqNo,
    __out_opt   ULONG          *pfQOP
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS SEC_ENTRY
SpiFreeContextBuffer(
    void SEC_FAR *      pvContextBuffer
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_FreeContextBuffer(pvContextBuffer);
}

SECURITY_STATUS
SEC_ENTRY
SpiQuerySecurityPackageInfoW(
    __in        LPWSTR        pszPackageName,
    __deref_out PSecPkgInfoW *pPackageInfo
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiExportSecurityContext(
    __in  PCtxtHandle ContextHandle,
    __in  ULONG       Flags,
    __out PSecBuffer  MarshalledContext,
    __out PHANDLE     TokenHandle
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiImportSecurityContextW(
    __in  LPWSTR      PackageName,
    __in  PSecBuffer  MarshalledContext,
    __in  HANDLE      TokenHandle,
    __out PCtxtHandle ContextHandle
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiAddCredentialsW(
    __in      PCredHandle    phCredentials,
    __in_opt  LPWSTR         pszPrincipal,
    __in      LPWSTR         pszPackageName,
    __in      ULONG          fCredentialUse,
    __in_opt  PVOID          pAuthData,
    __in_opt  SEC_GET_KEY_FN pGetKeyFn,
    __in_opt  PVOID          pvGetKeyArgument,
    __out_opt PTimeStamp     ptsExpiry
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiQuerySecurityContextToken(
    __in  PCtxtHandle phContext,
    __out PHANDLE     TokenHandle
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiEncryptMessage(
    __in    PCtxtHandle     phContext,
    __in    ULONG           fQOP,
    __inout PSecBufferDesc  pMessage,
    __in    ULONG           MessageSeqNo
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_EncryptMessage(phContext, fQOP, pMessage, MessageSeqNo);
}

SECURITY_STATUS
SEC_ENTRY
SpiDecryptMessage(
    __in      PCtxtHandle    phContext,
    __inout   PSecBufferDesc pMessage,
    __in      ULONG          MessageSeqNo,
    __out_opt ULONG *        pfQOP
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_DecryptMessage(phContext, pMessage, MessageSeqNo, pfQOP);
}

SECURITY_STATUS
SEC_ENTRY
SpiSetContextAttributesW(
    __in PCtxtHandle            phContext,
    __in ULONG                  ulAttribute,
    __in_bcount(cbBuffer) PVOID pBuffer,
    __in ULONG                  cbBuffer
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_SetContextAttributesW(
        phContext,
        ulAttribute,
        pBuffer,
        cbBuffer
    );
}

SECURITY_STATUS
SEC_ENTRY
SpiSetCredentialsAttributesW(
    __in PCredHandle            phCredential,
    __in ULONG                  ulAttribute,
    __in_bcount(cbBuffer) PVOID pBuffer,
    __in ULONG                  cbBuffer
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

#if ISSP_MODE != 0
SECURITY_STATUS
SEC_ENTRY
SpiChangeAccountPasswordW(
    __in    LPWSTR         pszPackageName,
    __in    LPWSTR         pszDomainName,
    __in    LPWSTR         pszAccountName,
    __in    LPWSTR         pszOldPassword,
    __in    LPWSTR         pszNewPassword,
    __in    BOOLEAN        bImpersonating,
    __in    ULONG          dwEncoded,
    __inout PSecBufferDesc pOutput
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}
#endif

SECURITY_STATUS
SEC_ENTRY
SpiQueryContextAttributesExW(
    __in  PCtxtHandle phContext,              // Context to query
    __in  unsigned long ulAttribute,          // Attribute to query
    __out_bcount(cbBuffer) void * pBuffer,    // Buffer for attributes
    __in  unsigned long cbBuffer              // Length of buffer
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY
SpiQueryCredentialsAttributesExW(
    __in    PCredHandle phCredential,
    __in    ULONG       ulAttribute,
    __inout_bcount(cbBuffer) PVOID pBuffer,
    __in    ULONG       cbBuffer
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS
SEC_ENTRY SpiSealMessage(
    PCtxtHandle ContextHandle, unsigned long QOP, PSecBufferDesc Message, unsigned long Sequence)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_EncryptMessage(ContextHandle, QOP, Message, Sequence);
}

SECURITY_STATUS SEC_ENTRY
SpiUnsealMessage(
    PCtxtHandle ContextHandle,
    PSecBufferDesc Message,
    unsigned long Sequence,
    unsigned long __SEC_FAR * QOP
)
{
    VERBOSE(("%s\n", __FUNCTION__));
    return MITLS_DecryptMessage(ContextHandle, Message, Sequence, QOP);
}


BOOL WINAPI DllMain(
	_In_ HINSTANCE hinstDLL,
	_In_ DWORD fdwReason,
	_In_ LPVOID lpvReserved
)
{
	g_hModule = (HMODULE)hinstDLL;
	if (fdwReason == DLL_PROCESS_ATTACH) {
		DisableThreadLibraryCalls((HMODULE)hinstDLL);
	}
	return TRUE;
}

HRESULT __stdcall DllRegisterServer(void)
{
	LSTATUS l;
	HKEY hKey;
	DWORD dwType;
	WCHAR Value[8192];
	DWORD cbValue;
	WCHAR ModuleName[_MAX_PATH+1];

	l = RegOpenKeyExW(HKEY_LOCAL_MACHINE, L"SYSTEM\\CurrentControlSet\\Control\\SecurityProviders", 
					  0,
					  KEY_READ|KEY_WRITE|KEY_SET_VALUE,
					  &hKey);
	if (l != ERROR_SUCCESS) {
		MessageBoxW(NULL, L"Failed to open the SecurityProviders key.  regsvr32.exe must be run elevated.", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	cbValue = sizeof(Value); // this is truly a byte count, not a character count
	l = RegQueryValueExW(hKey, L"SecurityProviders",
						 NULL,
						 &dwType,
						 (LPBYTE)Value,
						 &cbValue);
	if (l != ERROR_SUCCESS) {
		MessageBoxW(NULL, L"Failed to query the SecurityProviders key.", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	} else if (dwType != REG_SZ) {
		MessageBoxW(NULL, L"Unexpected type for the SecurityProviders value.  Expected REG_SZ", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	const DWORD MaxModuleNameSize = sizeof(ModuleName) / sizeof(ModuleName[0]);
	DWORD ModuleNameSize = GetModuleFileNameW(g_hModule, ModuleName, MaxModuleNameSize);
	if (ModuleNameSize >= MaxModuleNameSize) {
		MessageBoxW(NULL, L"GetModuleFileNameW failed", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	if (wcschr(ModuleName, L' ')) {
		MessageBoxW(NULL, L"Path to this DLL may not contain a space", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	if (Value[0] != '\0') { // appending after an existing SSP
		if (wcscat_s(Value, L",")) {
			MessageBoxW(NULL, L"Strings are too long", L"miTLS_SSP", MB_OK);
			return E_FAIL;
		}
	}
	if (wcscat_s(Value, ModuleName)) {
		MessageBoxW(NULL, L"Strings are too long", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	l = RegSetValueExW(hKey, L"SecurityProviders",
					   0,
					   REG_SZ,
					   (const BYTE*)Value,
					   (DWORD)(wcslen(Value)+1) * sizeof(Value[0])); // Length in bytes, not characters, counting '\0'
	if (l != ERROR_SUCCESS) {
		MessageBoxW(NULL, L"Failed to write to SecurityProviders", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	RegCloseKey(hKey);
	return S_OK;
}

HRESULT __stdcall DllUnregisterServer(void)
{
	LSTATUS l;
	HKEY hKey;
	DWORD dwType;
	WCHAR Value[8192];
	WCHAR NewValue[8192];
	DWORD cbValue;
	WCHAR ModuleName[_MAX_PATH + 1];

	l = RegOpenKeyExW(HKEY_LOCAL_MACHINE, L"SYSTEM\\CurrentControlSet\\Control\\SecurityProviders",
					  0,
					  KEY_READ | KEY_WRITE | KEY_SET_VALUE,
					  &hKey);
	if (l != ERROR_SUCCESS) {
		MessageBoxW(NULL, L"Failed to open the SecurityProviders key.  regsvr32.exe must be run elevated.", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	cbValue = sizeof(Value); // this is truly a byte count, not a character count
	l = RegQueryValueExW(hKey, L"SecurityProviders",
						 NULL,
						 &dwType,
						 (LPBYTE)Value,
						 &cbValue);
	if (l != ERROR_SUCCESS) {
		MessageBoxW(NULL, L"Failed to query the SecurityProviders key.", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	} else if (dwType != REG_SZ) {
		MessageBoxW(NULL, L"Unexpected type for the SecurityProviders value.  Expected REG_SZ", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	const DWORD MaxModuleNameSize = sizeof(ModuleName) / sizeof(ModuleName[0]);
	DWORD ModuleNameSize = GetModuleFileNameW(g_hModule, ModuleName, MaxModuleNameSize);
	if (ModuleNameSize >= MaxModuleNameSize) {
		MessageBoxW(NULL, L"GetModuleFileNameW failed", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	if (wcschr(ModuleName, L' ')) {
		MessageBoxW(NULL, L"Path to this DLL may not contain a space", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}

	wchar_t *p = wcsstr(Value, ModuleName);
	if (!p) {
		MessageBoxW(NULL, L"The SSP does not appear to be registered", L"miTLS_SSP", MB_OK);
		return S_OK;
	}
	wchar_t *pEnd = p + wcslen(ModuleName); // get a pointer to the text following our name
	if (p != Value) {
		p--;  // we are not the first entry, so back up and include the comma or space separator
	}
	*p = '\0'; // truncate ahead of our DLL name
	if (wcscpy_s(NewValue, Value) || wcscat_s(NewValue, pEnd)) {
		MessageBoxW(NULL, L"String too long", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	l = RegSetValueExW(hKey, L"SecurityProviders",
					   0,
					   REG_SZ,
					   (const BYTE*)NewValue,
					   (DWORD)(wcslen(NewValue) + 1) * sizeof(NewValue[0])); // Length in bytes, not characters, counting '\0'
	if (l != ERROR_SUCCESS) {
		MessageBoxW(NULL, L"Failed to write to SecurityProviders", L"miTLS_SSP", MB_OK);
		return E_FAIL;
	}
	RegCloseKey(hKey);
	return S_OK;
}

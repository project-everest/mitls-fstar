//////////////////////////////////////////////////////////////////////////////
//
//  mitls wrapper on schannel
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
#pragma once

VOID _PrintDump(SOCKET socket, PCHAR pszData, INT cbData);
VOID _PrintEnter(PCSTR psz, ...);
VOID _PrintExit(PCSTR psz, ...);
VOID _Print(PCSTR psz, ...);
void _PrintPSecBuffer(PSecBuffer b, bool fDump = false);
void _PrintPSecBufferDesc(const char *label, PSecBufferDesc p, bool fDump = false);

#define MITLS_NAME_W  L"Everest miTLS"
#define MITLS_NAME_A   "Everest miTLS"

#if USE_DETOURS
bool AttachDetours(VOID);
bool DetachDetours(VOID);
#endif


// These appear to have been added in v10.0.14393 of the Windows SDK, and are not yet documented on MSDN.
#ifndef SECBUFFER_SRTP_PROTECTION_PROFILES
#define SECBUFFER_SRTP_PROTECTION_PROFILES      19  // List of SRTP protection profiles, in descending order of preference
#endif

#ifndef SECBUFFER_SRTP_MASTER_KEY_IDENTIFIER
#define SECBUFFER_SRTP_MASTER_KEY_IDENTIFIER    20  // SRTP master key identifier
#endif

#ifndef SECBUFFER_TOKEN_BINDING
#define SECBUFFER_TOKEN_BINDING                 21  // Supported Token Binding protocol version and key parameters
#endif

#ifndef SECBUFFER_PRESHARED_KEY
#define SECBUFFER_PRESHARED_KEY                 22  // Preshared key
#endif

#ifndef SECBUFFER_PRESHARED_KEY_IDENTITY
#define SECBUFFER_PRESHARED_KEY_IDENTITY        23  // Preshared key identity
#endif

BOOL MITLS_Initialize(void);

BOOL MITLS_IsMITLSHandle(PSecHandle h);

SECURITY_STATUS SEC_ENTRY
MITLS_AcquireCredentialsHandleW(
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
);

SECURITY_STATUS SEC_ENTRY
MITLS_AcquireCredentialsHandleA(
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
);

SECURITY_STATUS
SEC_ENTRY MITLS_InitializeSecurityContextA(
    _In_opt_    PCredHandle phCredential,               // Cred to base context
    _In_opt_    PCtxtHandle phContext,                  // Existing context (OPT)
    _In_opt_    SEC_CHAR * pszTargetName,       // Name of target
    _In_        unsigned long fContextReq,              // Context Requirements
    _In_        unsigned long Reserved1,                // Reserved, MBZ
    _In_        unsigned long TargetDataRep,            // Data rep of target
    _In_opt_    PSecBufferDesc pInput,                  // Input Buffers
    _In_        unsigned long Reserved2,                // Reserved, MBZ
    _Inout_opt_ PCtxtHandle phNewContext,               // (out) New Context handle
    _Inout_opt_ PSecBufferDesc pOutput,                 // (inout) Output Buffers
    _Out_       unsigned long * pfContextAttr,  // (out) Context attrs
    _Out_opt_   PTimeStamp ptsExpiry                    // (out) Life span (OPT)
);

SECURITY_STATUS
SEC_ENTRY MITLS_InitializeSecurityContextW(
    _In_opt_    PCredHandle phCredential,               // Cred to base context
    _In_opt_    PCtxtHandle phContext,                  // Existing context (OPT)
#if ISSP_MODE == 0
    _In_opt_ PSECURITY_STRING pTargetName,
#else
    _In_opt_ SEC_WCHAR * pszTargetName,         // Name of target
#endif
    _In_        unsigned long fContextReq,              // Context Requirements
    _In_        unsigned long Reserved1,                // Reserved, MBZ
    _In_        unsigned long TargetDataRep,            // Data rep of target
    _In_opt_    PSecBufferDesc pInput,                  // Input Buffers
    _In_        unsigned long Reserved2,                // Reserved, MBZ
    _Inout_opt_ PCtxtHandle phNewContext,               // (out) New Context handle
    _Inout_opt_ PSecBufferDesc pOutput,                 // (inout) Output Buffers
    _Out_       unsigned long * pfContextAttr,  // (out) Context attrs
    _Out_opt_   PTimeStamp ptsExpiry                    // (out) Life span (OPT)
);

SECURITY_STATUS SEC_ENTRY MITLS_FreeContextBuffer(
    _In_ PVOID pvContextBuffer);

SECURITY_STATUS SEC_ENTRY
MITLS_FreeCredentialsHandle(
    _In_ PCredHandle phCredential            // Handle to free
);

SECURITY_STATUS SEC_ENTRY
MITLS_SetContextAttributesW(
    _In_ PCtxtHandle phContext,                   // Context to Set
    _In_ unsigned long ulAttribute,               // Attribute to Set
    _In_reads_bytes_(cbBuffer) void * pBuffer, // Buffer for attributes
    _In_ unsigned long cbBuffer                   // Size (in bytes) of Buffer
);

SECURITY_STATUS SEC_ENTRY
MITLS_SetContextAttributesA(
    _In_ PCtxtHandle phContext,                   // Context to Set
    _In_ unsigned long ulAttribute,               // Attribute to Set
    _In_reads_bytes_(cbBuffer) void * pBuffer, // Buffer for attributes
    _In_ unsigned long cbBuffer                   // Size (in bytes) of Buffer
);

SECURITY_STATUS SEC_ENTRY MITLS_QueryContextAttributesW(
    PCtxtHandle phContext,
    ULONG ulAttribute,
    PVOID pBuffer
);

SECURITY_STATUS SEC_ENTRY MITLS_QueryContextAttributesA(
    PCtxtHandle phContext,
    ULONG ulAttribute,
    PVOID pBuffer
);

SECURITY_STATUS SEC_ENTRY MITLS_EncryptMessage(PCtxtHandle         phContext,
    unsigned long       fQOP,
    PSecBufferDesc      pMessage,
    unsigned long       MessageSeqNo);

SECURITY_STATUS SEC_ENTRY MITLS_DecryptMessage(PCtxtHandle         phContext,
    PSecBufferDesc      pMessage,
    unsigned long       MessageSeqNo,
    unsigned long *     pfQOP);

SECURITY_STATUS SEC_ENTRY
MITLS_DeleteSecurityContext(
    _In_ PCtxtHandle phContext               // Context to delete
);

SECURITY_STATUS
SEC_ENTRY
MITLS_ApplyControlToken(
    __in PCtxtHandle    phContext,
    __in PSecBufferDesc pInput
);

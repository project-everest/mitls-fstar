/* -------------------------------------------------------------------- */
#define NTDDI_VERSION 0x06000000
#include <windows.h>
#include <wincrypt.h>

#define NT_SUCCESS(Status)          (((NTSTATUS)(Status)) >= 0)

#include "mipki.h"
#define DEBUG 1
#if DEBUG
#include <stdio.h>
#endif

struct mipki_state {
    HCERTSTORE hStore;
};


mipki_state* mipki_init(const mipki_config_entry config[], size_t config_len, password_callback pcb, int *erridx)
{
    if (config || config_len || pcb) {
#if DEBUG
        printf("mipki_init - config[] not supported on Windows.  Install certificates separately.\n");
#endif        
        //  openssl pkcs12 -export -out server.pfx -inkey server.key -in server.crt
        return 0;
    }
    mipki_state* st = (mipki_state*)HeapAlloc(GetProcessHeap(), 0, sizeof(mipki_state));
    if (!st) {
        return NULL;
    }
    st->hStore = CertOpenStore(
      CERT_STORE_PROV_SYSTEM, // Open the logical system store
      0,                      // MsgAndCertEncodingType is ignored
      0,                      // Use default crypto provider
      CERT_SYSTEM_STORE_CURRENT_USER, // Set the store location
      L"MY"
      );
    if (!st->hStore) {
#if DEBUG
        printf("mipki_init: CertOpenStore() failed - gle=0x%x\n", GetLastError());
#endif
        free(st);
        return NULL;
    }

    *erridx = 0;
    return st;
}

void mipki_free(mipki_state *st)
{
    if (!st) {
        return;
    }
    CertCloseStore(st->hStore, 0);
    HeapFree(GetProcessHeap(), 0, st);
}


int mipki_add_root_file_or_path(mipki_state *st, const char *ca_file)
{
    UNREFERENCED_PARAMETER(st)
    UNREFERENCED_PARAMETER(ca_file);
#if DEBUG
    printf("mipki_add_root_file_or_path - not supported on Windows.  Install certificates separately.\n");
#endif        
    return 0;
}

// Map the TLS signature to the OID value expected in a certificate
static const char *OIDFromTLS(mipki_signature alg)
{
    switch (alg) {
    // RSASSA-PKCS1-v1_5
    case 0x0401: return szOID_RSA_SHA256RSA; // rsa_pkcs1_sha256
    case 0x0501: return szOID_RSA_SHA384RSA; // rsa_pkcs1_sha384
    case 0x0601: return szOID_RSA_SHA512RSA; // rsa_pkcs1_sha512

    // ECDSA
    case 0x0403: return szOID_ECDSA_SHA256; // ecdsa_secp256r1_sha256
    case 0x0503: return szOID_ECDSA_SHA384; // ecdsa_secp384r1_sha384
    case 0x0603: return szOID_ECDSA_SHA512; // ecdsa_secp384r1_sha512

    // RSASSA-PSS
    case 0x0804: return szOID_RSA_SHA256RSA; // rsa_pss_sha256
    case 0x0805: return szOID_RSA_SHA384RSA; // rsa_pss_sha384
    case 0x0806: return szOID_RSA_SHA512RSA; // rsa_pss_sha512

    // EdDSA
    case 0x0807: return NULL; // ed25519 supported by bcrypt: BCRYPT_ECC_CURVE_25519
    case 0x0808: return NULL; // ed448   not supported by Windows

    // Legacy
    case 0x0201: return szOID_RSA_SHA1RSA; // rsa_pkcs1_sha1
    case 0x0203: return NULL; // ecdsa_sha1 supported by bcyprpt: BCRYPT_ECDSA_ALGORITHM

    return NULL; // Unknown/unsupported value
    }
}

mipki_chain mipki_select_certificate(mipki_state *st, const char *sni, size_t sni_len, const mipki_signature *algs, size_t algs_len, mipki_signature *selected)
{
    *selected = (mipki_signature)~0u;
    
    char* OID_SERVER_AUTH = szOID_PKIX_KP_SERVER_AUTH;
    CERT_ENHKEY_USAGE Usage;
    Usage.cUsageIdentifier = 1;
    Usage.rgpszUsageIdentifier = &OID_SERVER_AUTH;
    PCCERT_CONTEXT p;
    PCCERT_CONTEXT pPrev;
    for (pPrev = NULL;
        (p = CertFindCertificateInStore(st->hStore,
          X509_ASN_ENCODING,
          CERT_FIND_OPTIONAL_ENHKEY_USAGE_FLAG, // FindFlags
          CERT_FIND_ENHKEY_USAGE,
          &Usage,
          pPrev)); 
        pPrev = p) {
        #if DEBUG
        printf("Found a certificate!\n");
        #endif

        DWORD dw = CertGetNameStringA(
          p, 
          CERT_NAME_DNS_TYPE,
          CERT_NAME_SEARCH_ALL_NAMES_FLAG,
          NULL,
          NULL,
          0);
        char *CertificateNames = (char*)HeapAlloc(GetProcessHeap(), 0, dw);
        if (CertificateNames == NULL) {
            CertFreeCertificateContext(p);
            CertFreeCertificateContext(pPrev);
            return NULL;
        }
        dw = CertGetNameStringA(
          p, 
          CERT_NAME_DNS_TYPE,
          CERT_NAME_SEARCH_ALL_NAMES_FLAG,
          NULL,
          CertificateNames,
          dw);
        char *CertificateName;
        for (CertificateName = CertificateNames;
             *CertificateName;
             CertificateName += strlen(CertificateName)+1) {
                 
            if (strcmp(CertificateName, sni) == 0) {
                break;
            }
         }
         if (*CertificateName == '\0') {
            // This certificate doesn't match the sni name.  Skip it.
            HeapFree(GetProcessHeap(), 0, CertificateNames);
            continue;
         }
         HeapFree(GetProcessHeap(), 0, CertificateNames);
         
         // High byte of algs[] is the TLS HashAlgorithm:
         //  none(0), md5(1), sha1(2), sha224(3), sha256(4), sha384(5), sha512(6)
         // Low byte of algs[] is the TLS SignatureAlgorithm:
         //  anonymous(0), rsa(1), dsa(2), ecdsa(3)
         for (size_t i=0; i<algs_len; ++i) {
            const char *oid = OIDFromTLS(algs[i]);
            if (oid == NULL) {
                #if DEBUG
                printf("Unsupported alg=%4.4x", algs[i]);
                #endif
            } else if (strcmp(p->pCertInfo->SignatureAlgorithm.pszObjId, oid) == 0) {
                #if DEBUG
                printf(" + Certificate selected with alg=%04x\n", algs[i]);
                #endif
                
                *selected = algs[i];
                return (mipki_chain)p;
            }
         }
    }
    
    return NULL;
}

// // High byte of algs[] is the TLS HashAlgorithm:
//  none(0), md5(1), sha1(2), sha224(3), sha256(4), sha384(5), sha512(6)
static ALG_ID AlgidFromTLS(mipki_signature alg)
{
    switch (alg) {
    // RSASSA-PKCS1-v1_5
    case 0x0401: return CALG_SHA_256; // rsa_pkcs1_sha256
    case 0x0501: return CALG_SHA_384; // rsa_pkcs1_sha384
    case 0x0601: return CALG_SHA_512; // rsa_pkcs1_sha512

    // ECDSA
    case 0x0403: return CALG_SHA_256; // ecdsa_secp256r1_sha256
    case 0x0503: return CALG_SHA_384; // ecdsa_secp384r1_sha384
    case 0x0603: return CALG_SHA_512; // ecdsa_secp384r1_sha512

    // RSASSA-PSS
    case 0x0804: return CALG_SHA_256; // rsa_pss_sha256
    case 0x0805: return CALG_SHA_384; // rsa_pss_sha384
    case 0x0806: return CALG_SHA_512; // rsa_pss_sha512

    // EdDSA
    case 0x0807: return ~0u; // ed25519 supported by bcrypt: BCRYPT_ECC_CURVE_25519
    case 0x0808: return ~0u; // ed448   not supported by Windows

    // Legacy
    case 0x0201: return CALG_SHA1; // rsa_pkcs1_sha1
    case 0x0203: return ~0u; // ecdsa_sha1 supported by bcyprpt: BCRYPT_ECDSA_ALGORITHM

    default:
        return ~0u;
    }
}

static DWORD ProvTypeFromTLS(mipki_signature alg)
{
    switch (alg) {
    // RSASSA-PKCS1-v1_5
    case 0x0401: return PROV_RSA_AES; // rsa_pkcs1_sha256
    case 0x0501: return PROV_RSA_AES; // rsa_pkcs1_sha384
    case 0x0601: return PROV_RSA_AES; // rsa_pkcs1_sha512

    // ECDSA
    case 0x0403: return ~0u; // ecdsa_secp256r1_sha256
    case 0x0503: return ~0u; // ecdsa_secp384r1_sha384
    case 0x0603: return ~0u; // ecdsa_secp384r1_sha512

    // RSASSA-PSS
    case 0x0804: return PROV_RSA_AES; // rsa_pss_sha256
    case 0x0805: return PROV_RSA_AES; // rsa_pss_sha384
    case 0x0806: return PROV_RSA_AES; // rsa_pss_sha512

    // EdDSA
    case 0x0807: return ~0u; // ed25519 supported by bcrypt: BCRYPT_ECC_CURVE_25519
    case 0x0808: return ~0u; // ed448   not supported by Windows

    // Legacy
    case 0x0201: return PROV_RSA_AES; // rsa_pkcs1_sha1
    case 0x0203: return ~0u; // ecdsa_sha1 supported by bcyprpt: BCRYPT_ECDSA_ALGORITHM

    default:
        return ~0u;
    }
}

int mipki_sign_verify(mipki_state *st, const mipki_chain cert_ptr, const mipki_signature sigalg, const char *tbs, size_t tbs_len, char *sig, size_t *sig_len, mipki_mode m)
{
    PCCERT_CONTEXT p = (PCCERT_CONTEXT)cert_ptr;
    
    DWORD dwProvType = ProvTypeFromTLS(sigalg);
    if (dwProvType == ~0u) {
        #if DEBUG
        printf("Unsupported signature algorithm 0x%x (ProvType)\n", sigalg);
        #endif
        return 0;
    }
    ALG_ID Algid = AlgidFromTLS(sigalg);
    if (Algid == ~0u) {
        #if DEBUG
        printf("Unsupported signature algorithm 0x%x (AlgId)\n", sigalg);
        #endif
        return 0;
    }
    
    HCRYPTPROV hProv;
    if (!CryptAcquireContext(
      &hProv, 
      NULL,
      MS_ENH_RSA_AES_PROV, // this provider supports CALG_SHA_*
      dwProvType, 
      CRYPT_VERIFYCONTEXT)) {
        #if DEBUG
        printf("CryptAcquireContext failed.  gle=0x%x\n", GetLastError());
        #endif
        return 0;
    }
    
    HCRYPTKEY hKey;
    if (!CryptImportPublicKeyInfo(
      hProv, 
      X509_ASN_ENCODING | PKCS_7_ASN_ENCODING,
      &p->pCertInfo->SubjectPublicKeyInfo,
      &hKey)) {
        #if DEBUG
        printf("CryptImportPublicKeyInfo failed.  gle=0x%x\n", GetLastError());
        #endif
        CryptReleaseContext(hProv, 0);
        return 0;
    }
    
    HCRYPTHASH hHash;
    if (!CryptCreateHash(hProv,
      Algid,
      0,
      0,
      &hHash)) {
        #if DEBUG
        printf("CryptCreateHash failed.  gle=0x%x\n", GetLastError());
        #endif
        CryptDestroyKey(hKey);
        CryptReleaseContext(hProv, 0);
        return 0;
    }
    
    if (!CryptHashData(
      hHash,
      tbs,
      tbs_len,
      0)) {
        #if DEBUG
        printf("CryptHashData failed.  gle=0x%x\n", GetLastError());
        #endif
        CryptDestroyHash(hHash);
        CryptDestroyKey(hKey);
        CryptReleaseContext(hProv, 0);
        return 0;
    }
    
    if (m == MIPKI_VERIFY) {
        if (!CryptVerifySignature(
          hHash,
          sig,
          *sig_len,
          hKey,
          NULL,
          0)) {
            #if DEBUG
            printf("CryptVerifySignature failed.  gle=0x%x\n", GetLastError());
            #endif
            CryptDestroyHash(hHash);
            CryptDestroyKey(hKey);
            CryptReleaseContext(hProv, 0);
            return 0;
        }
        
    } else {
        DWORD dwSigLen = (DWORD)*sig_len;
        if (!CryptSignHash(
          hHash,
          AT_SIGNATURE,
          NULL,
          0,
          sig,
          &dwSigLen)) {
            #if DEBUG
            printf("CryptVerifySignature failed.  gle=0x%x\n", GetLastError());
            #endif
            CryptDestroyHash(hHash);
            CryptDestroyKey(hKey);
            CryptReleaseContext(hProv, 0);
            return 0;
          }
          *sig_len = dwSigLen;
    }
    
    CryptDestroyHash(hHash);
    CryptDestroyKey(hKey);
    CryptReleaseContext(hProv, 0);
    return 1;
}

mipki_chain mipki_parse_chain(mipki_state *st, const char *chain, size_t chain_len)
{
    HCERTSTORE h;
    
    h = CertOpenStore(CERT_STORE_PROV_MEMORY,
        0,0, CERT_STORE_DEFER_CLOSE_UNTIL_LAST_FREE_FLAG, 0);
    if (!h) {
        #if DEBUG
        printf("CertOpenStore failed.  gle=0x%x\n", GetLastError());
        #endif
        return NULL;
    }

    PCCERT_CONTEXT Root = NULL;
    PCCERT_CONTEXT p = NULL;
    for (DWORD certnumber=0; chain_len; ++certnumber) {
        if (chain_len < 3) {
            #if DEBUG
            printf("Insufficient buffer\n");
            #endif
            CertCloseStore(h, 0);
            return NULL;
        }
        DWORD cb = ((DWORD)(BYTE)chain[0]) << 16 |
                   ((DWORD)(BYTE)chain[1]) << 8 |
                   ((DWORD)(BYTE)chain[2]);
        chain_len -= 3;
        chain += 3;
        if (!CertAddEncodedCertificateToStore(
          h,
          X509_ASN_ENCODING,
          chain,
          cb,
          CERT_STORE_ADD_USE_EXISTING,
          &p)) {
            #if DEBUG
            printf("CertAddEncodedCertificateToStore failed for cert #%u.  gle=0x%x\n", certnumber, GetLastError());
            #endif
            if (Root) {
                CertFreeCertificateContext(Root);
            }
            CertCloseStore(h, 0);
            return NULL;
        }
        chain += cb;
        chain_len -= cb;
        if (Root == NULL) {
            Root = p;
        } else {
            CertFreeCertificateContext(p);
        }
    }
    if (chain_len) {
        #if DEBUG
        printf("Not all bytes were processed.\n");
        #endif
        if (Root) {
            CertFreeCertificateContext(Root);
        }
        CertCloseStore(h, 0);
        return NULL;
    }
    CertCloseStore(h, 0);

    return Root;
}

size_t mipki_format_chain(mipki_state *st, const mipki_chain chain, char *buffer, size_t buffer_len)
{
    CERT_CHAIN_PARA ChainPara;
    CERT_ENHKEY_USAGE EnhkeyUsage;
    CERT_USAGE_MATCH CertUsage;
    PCCERT_CHAIN_CONTEXT pChainContext;
    
    EnhkeyUsage.cUsageIdentifier = 0;
    EnhkeyUsage.rgpszUsageIdentifier=NULL;
    CertUsage.dwType = USAGE_MATCH_TYPE_AND;
    CertUsage.Usage  = EnhkeyUsage;
    ChainPara.cbSize = sizeof(CERT_CHAIN_PARA);
    ChainPara.RequestedUsage=CertUsage;

    if (!CertGetCertificateChain(
      NULL,   // default chain engine
      (PCCERT_CONTEXT)chain,
      NULL,
      NULL,
      &ChainPara,
      0,
      NULL,
      &pChainContext)) {
        #if DEBUG
        printf("CertGetCertificateChain failed.  gle=0x%x\n", GetLastError());
        #endif
        return 0;
    }
    char *b = buffer;
    for (DWORD i=0; i<pChainContext->cChain; ++i) {
        PCERT_SIMPLE_CHAIN schain = pChainContext->rgpChain[i];
        for (DWORD j=0; j<schain->cElement; ++j) {
            PCERT_CHAIN_ELEMENT element = schain->rgpElement[j];
            PCCERT_CONTEXT p = element->pCertContext;
            if (p->cbCertEncoded+3 > buffer_len) {
                #if DEBUG
                printf("Insufficient buffer to store the formatted chain\n");
                #endif
                CertFreeCertificateChain(pChainContext);
                return 0;
            }
            b[0] = (char)(p->cbCertEncoded >> 16);
            b[1] = (char)(p->cbCertEncoded >> 8);
            b[2] = (char)p->cbCertEncoded;
            b += 3;
            memcpy(b, p->pbCertEncoded, p->cbCertEncoded);
            b += p->cbCertEncoded;
            buffer_len -= (3+p->cbCertEncoded);
        }
    }
    size_t ChainLength = (size_t)(b-buffer);

    CertFreeCertificateChain(pChainContext);
    return ChainLength;
}

int mipki_validate_chain(mipki_state *st, const mipki_chain chain, const char *host)
{
    PCCERT_CONTEXT p = (PCCERT_CONTEXT)chain;
    HTTPSPolicyCallbackData polHttps;
    CERT_CHAIN_PARA ChainPara;
    LPWSTR pwszServerName = NULL;
    PCCERT_CHAIN_CONTEXT pChainContext = NULL;
    CERT_CHAIN_POLICY_PARA PolicyPara;
    CERT_CHAIN_POLICY_STATUS PolicyStatus;
    
    LPSTR rgszUsages[] = {
        szOID_PKIX_KP_SERVER_AUTH,
        szOID_SERVER_GATED_CRYPTO,
        szOID_SGC_NETSCAPE };

    memset(&ChainPara, 0, sizeof(ChainPara));
    ChainPara.cbSize = sizeof(ChainPara);
    ChainPara.RequestedUsage.dwType = USAGE_MATCH_TYPE_OR;
    ChainPara.RequestedUsage.Usage.cUsageIdentifier     = ARRAYSIZE(rgszUsages);
    ChainPara.RequestedUsage.Usage.rgpszUsageIdentifier = rgszUsages;

    if (!CertGetCertificateChain(
      NULL,
      p,
      NULL,
      p->hCertStore,
      &ChainPara,
      0,
      NULL,
      &pChainContext)) {
        #if DEBUG
        printf("CertGetCertificateChain() failed.  gle=0x%x\n", GetLastError());
        #endif
        return 0;
    }

    if (host) {
        int widelen = MultiByteToWideChar(CP_UTF8, 0, host, -1, NULL, 0);
        if (widelen == 0) {
            #if DEBUG
            printf("MultiByteToWideChar (1) failed.  gle=%d\n", GetLastError());
            #endif
            CertFreeCertificateChain(pChainContext);
            return 0;
        }
        pwszServerName = (LPWSTR)HeapAlloc(GetProcessHeap(), 0, widelen*sizeof(WCHAR));
        if (!pwszServerName) {
            #if DEBUG
            printf("Out of memory\n");
            #endif
            CertFreeCertificateChain(pChainContext);
            return 0;
        }
        widelen = MultiByteToWideChar(CP_UTF8, 0, host, -1, pwszServerName, widelen);
        if (widelen == 0) {
            #if DEBUG
            printf("MultiByteToWideChar (2) failed.  gle=%d\n", GetLastError());
            #endif
            CertFreeCertificateChain(pChainContext);
            HeapFree(GetProcessHeap(), 0, pwszServerName);
            return 0;
        }
    }

    memset(&polHttps, 0, sizeof(HTTPSPolicyCallbackData));
    polHttps.cbStruct = sizeof(HTTPSPolicyCallbackData);
    polHttps.dwAuthType = AUTHTYPE_SERVER;
    polHttps.fdwChecks = 0;
    polHttps.pwszServerName = pwszServerName;

    memset(&PolicyPara, 0, sizeof(PolicyPara));
    PolicyPara.cbSize = sizeof(PolicyPara);
    PolicyPara.pvExtraPolicyPara = &polHttps;

    memset(&PolicyStatus, 0, sizeof(PolicyStatus));
    PolicyStatus.cbSize = sizeof(PolicyStatus);

    if (!CertVerifyCertificateChainPolicy(
      CERT_CHAIN_POLICY_SSL,
      pChainContext,
      &PolicyPara,
      &PolicyStatus))
    {
        #if DEBUG
        printf("CertVerifyCertificateChainPolicy() failed.  gle=0x%x\n", GetLastError());
        #endif
        CertFreeCertificateChain(pChainContext);
        HeapFree(GetProcessHeap(), 0, pwszServerName);
        return 0;
    }

    CertFreeCertificateChain(pChainContext);
    HeapFree(GetProcessHeap(), 0, pwszServerName);
    return 1;
}

void mipki_free_chain(mipki_state *st, mipki_chain chain)
{
    PCCERT_CONTEXT p = (PCCERT_CONTEXT)chain;
    CertFreeCertificateContext(p);
}



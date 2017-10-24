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

// High byte of algs[] is the TLS HashAlgorithm:
//  none(0), md5(1), sha1(2), sha224(3), sha256(4), sha384(5), sha512(6)
// Low byte of algs[] is the TLS SignatureAlgorithm:
//  anonymous(0), rsa(1), dsa(2), ecdsa(3)
static const char *OIDFromTLS(mipki_signature alg)
{
    switch (alg) {
    case 0x0101: return szOID_RSA_MD5RSA;
    case 0x0201: return szOID_RSA_SHA1RSA;
    case 0x0401: return szOID_RSA_SHA256RSA;
    case 0x0501: return szOID_RSA_SHA384RSA;
    case 0x0601: return szOID_RSA_SHA512RSA;
    
    case 0x0203: return szOID_ECDSA_SHA1;
    case 0x0403: return szOID_ECDSA_SHA256;
    case 0x0503: return szOID_ECDSA_SHA384;
    case 0x0603: return szOID_ECDSA_SHA512;
    default:
        return NULL; // Unknown/unsupported value
    }
}

static DWORD ProviderTypeFromTLS(mipki_signature alg)
{
    switch (alg & 0xff) {
    case 0x01: return PROV_RSA_FULL;
    case 0x02: return PROV_DSS;
    case 0x03: return PROV_EC_ECDSA_FULL;
    default:
        return ~0u;
    }
}

mipki_chain mipki_select_certificate(mipki_state *st, const char *sni, const mipki_signature *algs, size_t algs_len, mipki_signature *selected)
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
    switch (alg >> 8) {
    case 0x01: return CALG_MD5;
    case 0x02: return CALG_SHA1;
    case 0x03: return ~0u; // unsupported
    case 0x04: return CALG_SHA_256;
    case 0x05: return CALG_SHA_384;
    case 0x06: return CALG_SHA_512;
    default:
        return ~0u;
    }
}

static DWORD ProvTypeFromTLS(mipki_signature alg)
{
    switch (alg & 0xff) {
    case 0x01: return PROV_RSA_AES;
    case 0x02: return PROV_DSS;
    case 0x03: return ~0u; // This requires Crypto CNG
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
        printf("Unsupported signature algorithm 0x%x\n", sigalg);
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
    
    ALG_ID Algid = AlgidFromTLS(sigalg);
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
    // bugbug: implement
    #if DEBUG
    printf("mipki_parse_chain is NYI\n");
    #endif
    
    return NULL;
}

size_t mipki_format_chain(mipki_state *st, const mipki_chain chain, char *buffer, size_t buffer_len)
{
    // bugbug: implement
    #if DEBUG
    printf("mipki_format_chain is NYI\n");
    #endif
    
    return 0;
}

int mipki_validate_chain(mipki_state *st, const mipki_chain chain, const char *host)
{
    // bugbug: implement
    #if DEBUG
    printf("mipki_validate_chain is NYI\n");
    #endif
    
    return 0;
}

void mipki_free_chain(mipki_state *st, mipki_chain chain)
{    
    // bugbug: implement
    #if DEBUG
    printf("mipki_free_chain is NYI\n");
    #endif
}



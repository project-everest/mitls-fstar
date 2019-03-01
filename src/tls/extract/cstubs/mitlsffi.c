#include <memory.h>
#include <stdarg.h>
#if __APPLE__
#include <sys/errno.h> // OS/X only provides include/sys/errno.h
#else
#include <errno.h> // MinGW only provides include/errno.h
#include <malloc.h>
#endif
#if defined(_MSC_VER) || defined(__MINGW32__)
#define IS_WINDOWS 1
  #ifdef _KERNEL_MODE
    #include <nt.h>
    #include <ntrtl.h>
  #else
    #include <windows.h>
    extern ULONG DbgPrint(const char *, ...);
  #endif
#else
#define IS_WINDOWS 0
#include <pthread.h>
#endif

#include "EverCrypt.h"
#include "Spec.h"
#include "FFI.h"
#include "QUIC.h"
#include "mitlsffi.h"
#include "RegionAllocator.h"

// Convert internal to external algorithm representations
#define CONVERT_HASH(h) (h == Spec_Hash_Definitions_MD5 ? TLS_hash_MD5 : (h == Spec_Hash_Definitions_SHA1 ? TLS_hash_SHA1 : (h == Spec_Hash_Definitions_SHA2_224 ? TLS_hash_SHA224 : (h == Spec_Hash_Definitions_SHA2_256 ? TLS_hash_SHA256 : (h == Spec_Hash_Definitions_SHA2_384 ? TLS_hash_SHA384 : TLS_hash_SHA512)))))
#define CONVERT_AEAD(ae) (ae == EverCrypt_AES128_GCM ? TLS_aead_AES_128_GCM : (ae == EverCrypt_AES256_GCM ? TLS_aead_AES_256_GCM : TLS_aead_CHACHA20_POLY1305))

// This file is hand-written C code, to wrap the Kremlin-extracted
// code to match the mitlsffi.h interface.
//
// So it uses KRML_HOST_MALLOC and KRML_HOST_FREE in order to
// support the same pluggable heap manager as the rest of miTLS.

#if LOG_TO_CHOICE
typedef void (*p_log)(const char *fmt, ...);
p_log g_LogPrint;
#endif

struct mitls_state {
  HEAP_REGION rgn;
  TLSConstants_config cfg;
  Connection_connection cxn;
};

// BUGBUG: temporary global lock to protect global
//         mutable variables in mitls.  Remove when
//         the variables have their own protection.
#if IS_WINDOWS
  #ifdef _KERNEL_MODE
    FAST_MUTEX lock;
    #define LOCK_MUTEX(x) ExAcquireFastMutex (x)
    #define UNLOCK_MUTEX(x) ExReleaseFastMutex (x)
  #else
    CRITICAL_SECTION lock;
    #define LOCK_MUTEX(x) EnterCriticalSection(x)
    #define UNLOCK_MUTEX(x) LeaveCriticalSection(x)
  #endif
#else
static pthread_mutex_t lock;
#define LOCK_MUTEX(x) pthread_mutex_lock(x)
#define UNLOCK_MUTEX(x) pthread_mutex_unlock(x)
#endif

static Prims_string CopyPrimsString(const char *src)
{
    size_t len = strlen(src)+1;
    Prims_string dst = KRML_HOST_MALLOC(len);
    memcpy((char*)dst, src, len);
    return dst;
}

static void MakeFStar_Bytes_bytes(FStar_Bytes_bytes *b, const unsigned char *data, uint32_t length)
{
    b->data = KRML_HOST_MALLOC(length);
    memcpy((char*)b->data, data, length);
    b->length = length;
}

void NoPrintf(const char *fmt, ...)
{
}

pfn_mitls_trace_callback trace_callback;

void TracePrintf(const char *fmt, ...)
{
    va_list args;
    va_start (args, fmt);

    char buffer[256];
#if !IS_WINDOWS
    vsnprintf(buffer, sizeof(buffer), fmt, args);
#else
    vsprintf_s(buffer, sizeof(buffer), fmt, args);
#endif
    // For WPP tracing, the trailing '\n' is undesirable, so remove.
    char *c = strrchr(buffer, '\n');
    if (c) {
        *c = '\0';
    }

    (*trace_callback)(buffer);
}

//
// Hosts may provide a callback function for debug tracing.
//
void MITLS_CALLCONV FFI_mitls_set_trace_callback(pfn_mitls_trace_callback cb)
{
    trace_callback = cb;
#if LOG_TO_CHOICE
    g_LogPrint = TracePrintf;
#endif
}

//
// Initialize miTLS.
//
//  Called once ahead of using miTLS
//
//  Returns:  0 for error, nonzero for success
//
int MITLS_CALLCONV FFI_mitls_init(void)
{
  if (HeapRegionInitialize() == 0) {
      return 0;
  }

  if (Random_init() != 1) {
      HeapRegionCleanup();
      return 0;
  }

  #if IS_WINDOWS
    #ifdef _KERNEL_MODE
    ExInitializeFastMutex(&lock);
      #if LOG_TO_CHOICE
      if (!g_LogPrint) {
        g_LogPrint = (p_log)DbgPrint;
      }
      #endif
    #else /* _KERNEL_MODE */
    InitializeCriticalSection(&lock);
      #if LOG_TO_CHOICE
      if (!g_LogPrint) {
        if (GetEnvironmentVariableA("MITLS_LOG", NULL, 0) == 0) {
          g_LogPrint = (p_log)NoPrintf; // no logging
        } else {
          g_LogPrint = (p_log)printf;
        }
      }
      #endif
    #endif /* _KERNEL_MODE */
  #else /* IS_WINDOWS */
  if (pthread_mutex_init(&lock, NULL) != 0) {
    HeapRegionCleanup();
    return 0;
  }
  #if LOG_TO_CHOICE
    if (!g_LogPrint) {
      if (getenv("MITLS_LOG") == NULL) {
        g_LogPrint = NoPrintf; // default to no logging
      } else {
        g_LogPrint = (p_log)printf;
      }
    }
  #endif
#endif

  ENTER_GLOBAL_HEAP_REGION();
  kremlinit_globals();
  LEAVE_GLOBAL_HEAP_REGION();
  
  if (HAD_OUT_OF_MEMORY) {
      HeapRegionCleanup();
      return 0;
  }
  
  return 1; // success
}

void MITLS_CALLCONV FFI_mitls_cleanup(void)
{
  Random_cleanup();
    
#if IS_WINDOWS
  #ifndef _KERNEL_MODE
  DeleteCriticalSection(&lock);
  #endif
#else
  pthread_mutex_destroy(&lock);
#endif

  HeapRegionCleanup();
}

// Called by the host app to configure miTLS ahead of creating a connection
int MITLS_CALLCONV FFI_mitls_configure(mitls_state **state, const char *tls_version, const char *host_name)
{
    int ret = 0;

    *state = NULL;

    HEAP_REGION rgn;
    CREATE_HEAP_REGION(&rgn);
    if (!VALID_HEAP_REGION(rgn)) {
        return 0; // out of memory
    }

    Prims_string host = CopyPrimsString(host_name);
    Prims_string version = CopyPrimsString(tls_version);

    TLSConstants_config config = FFI_ffiConfig(version, (FStar_Bytes_bytes){.data=host,.length=strlen(host_name)});

    // Allocate space on the heap, to store an OCaml value
    mitls_state *s = (mitls_state*)KRML_HOST_MALLOC(sizeof(mitls_state));
    s->cfg = config;
    s->rgn = rgn;
    *state = s;
    ret = 1;

    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        DESTROY_HEAP_REGION(rgn);
        ret = 0;
    }
    return ret;
}

int MITLS_CALLCONV FFI_mitls_set_ticket_key(const char *alg, const unsigned char *tk, size_t klen)
{
    int b = 0;
    LOCK_MUTEX(&lock);
    ENTER_GLOBAL_HEAP_REGION();
    FStar_Bytes_bytes key;
    MakeFStar_Bytes_bytes(&key, tk, klen);
    b = FFI_ffiSetTicketKey(alg, key);
    LEAVE_GLOBAL_HEAP_REGION();
    UNLOCK_MUTEX(&lock);
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return (b) ? 1 : 0;
}

int MITLS_CALLCONV FFI_mitls_set_sealing_key(const char *alg, const unsigned char *tk, size_t klen)
{
    int b = 0;
    LOCK_MUTEX(&lock);
    ENTER_GLOBAL_HEAP_REGION();
    FStar_Bytes_bytes key;
    MakeFStar_Bytes_bytes(&key, tk, klen);
    b = FFI_ffiSetSealingKey(alg, key);
    LEAVE_GLOBAL_HEAP_REGION();
    UNLOCK_MUTEX(&lock);
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return (b) ? 1 : 0;
}

int MITLS_CALLCONV FFI_mitls_configure_ticket(mitls_state *state, const mitls_ticket *ticket)
{
    int b = 0;
    ENTER_HEAP_REGION(state->rgn);
    FStar_Bytes_bytes tid, si;
    MakeFStar_Bytes_bytes(&tid, ticket->ticket, ticket->ticket_len);
    MakeFStar_Bytes_bytes(&si, ticket->session, ticket->session_len);
    state->cfg = FFI_ffiSetTicket(state->cfg, tid, si);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return (b) ? 1 : 0;
}

int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char * cs)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetCipherSuites(state->cfg, cs);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char * sa)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetSignatureAlgorithms(state->cfg, sa);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char * ng)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetNamedGroups(state->cfg, ng);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return 1;
}

static TLSConstants_alpn alpn_list_of_array(const mitls_alpn *alpn, size_t alpn_count)
{
  TLSConstants_alpn apl = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));
  apl->tag = Prims_Nil;

  for(int i = (alpn_count & 255) - 1; i >= 0; i--)
  {
    TLSConstants_alpn new = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));
    new->tag = Prims_Cons;
    new->hd.length = alpn[i].alpn_len & 255;
    new->hd.data = KRML_HOST_MALLOC(new->hd.length);
    memcpy((unsigned char*)new->hd.data, alpn[i].alpn, new->hd.length);
    new->tl = apl;
    apl = new;
  }

  return apl;
}

int MITLS_CALLCONV FFI_mitls_configure_alpn(/* in */ mitls_state *state, const mitls_alpn *alpn, size_t alpn_count)
{
    ENTER_HEAP_REGION(state->rgn);
    TLSConstants_alpn apl = alpn_list_of_array(alpn, alpn_count);
    state->cfg = FFI_ffiSetALPN(state->cfg, apl);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_custom_extensions(/* in */ mitls_state *state, const mitls_extension *exts, size_t exts_count)
{
  ENTER_HEAP_REGION(state->rgn);
  for(size_t i = 0; i < exts_count; i++)
  {
    char *c = KRML_HOST_MALLOC(exts->ext_data_len);
    memcpy(c, exts->ext_data, exts->ext_data_len);
    state->cfg = FFI_ffiAddCustomExtension(state->cfg, exts->ext_type, (FStar_Bytes_bytes){.data = c, .length = exts->ext_data_len});
    exts++;
  }
  LEAVE_HEAP_REGION();
  if (HAD_OUT_OF_MEMORY) {
    return 0;
  }
  return 1;
}


typedef struct {
  void* cb_state;
  pfn_FFI_ticket_cb cb;
} wrapped_ticket_cb;

static void ticket_cb_proxy(FStar_Dyn_dyn cbs, Prims_string sni, FStar_Bytes_bytes ticket, TLSConstants_ticketInfo info, FStar_Bytes_bytes rawkey)
{
  wrapped_ticket_cb *cb = (wrapped_ticket_cb*)cbs;
  FStar_Bytes_bytes session = FFI_ffiTicketInfoBytes(info, rawkey);
  mitls_ticket t = {
    .ticket_len = ticket.length,
    .ticket = (unsigned char*)ticket.data,
    .session_len = session.length,
    .session = (unsigned char*)session.data
  };

  cb->cb(cb->cb_state, sni, &t);
}

int MITLS_CALLCONV FFI_mitls_configure_ticket_callback(/* in */ mitls_state *state, void *cb_state, pfn_FFI_ticket_cb ticket_cb)
{
    ENTER_HEAP_REGION(state->rgn);
    wrapped_ticket_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_ticket_cb));
    cbs->cb_state = cb_state;
    cbs->cb = ticket_cb;
    state->cfg = FFI_ffiSetTicketCallback(state->cfg, (void*)cbs, ticket_cb_proxy);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return 1;
}

typedef struct {
  void* cb_state;
  pfn_FFI_nego_cb cb;
} wrapped_nego_cb;

static mitls_version convert_pv(Parsers_ProtocolVersion_protocolVersion pv)
{
  switch(pv.tag)
  {
    case Parsers_ProtocolVersion_SSL_3p0:
      return TLS_SSL3;
    case Parsers_ProtocolVersion_TLS_1p0:
      return TLS_1p0;
    case Parsers_ProtocolVersion_TLS_1p1:
      return TLS_1p1;
    case Parsers_ProtocolVersion_TLS_1p2:
      return TLS_1p2;
    case Parsers_ProtocolVersion_TLS_1p3:
      return TLS_1p3;
    default:
      return TLS_SSL3;
  }
  return TLS_SSL3; // unreachable
}

static TLSConstants_nego_action nego_cb_proxy(FStar_Dyn_dyn cbs, Parsers_ProtocolVersion_protocolVersion pv,
  FStar_Bytes_bytes extb, FStar_Pervasives_Native_option__FStar_Bytes_bytes cookie)
{
  wrapped_nego_cb *cb = (wrapped_nego_cb*)cbs;
  unsigned char *app_cookie = NULL, *c;
  mitls_extension *extra_exts = NULL;
  size_t i, app_cookie_len = 0, extra_exts_len = 0;
  TLSConstants_nego_action a;
  TLSConstants_custom_extensions cexts;

  if(cookie.tag == FStar_Pervasives_Native_Some)
  {
    app_cookie = (unsigned char *)cookie.v.data;
    if(app_cookie == NULL) app_cookie = (unsigned char*)""; // None vs Some empty_bytes / NULL
    app_cookie_len = cookie.v.length;
  }

  mitls_nego_action r = cb->cb(cb->cb_state, convert_pv(pv), (const unsigned char*)extb.data, extb.length,
    &extra_exts, &extra_exts_len, &app_cookie, &app_cookie_len);

  switch(r)
  {
    case TLS_nego_abort:
      a.tag = TLSConstants_Nego_abort;
      break;
    case TLS_nego_accept:
      a.tag = TLSConstants_Nego_accept;
      cexts = TLSConstants_empty_custom_extensions();
      if(extra_exts != NULL && extra_exts_len > 0)
      {
        for(i=0; i<extra_exts_len; i++)
        {
          cexts = TLSConstants_add_custom_extension(cexts, extra_exts->ext_type,
            (FStar_Bytes_bytes){.data = (const char*)extra_exts->ext_data, .length = extra_exts->ext_data_len});
          extra_exts++;
        }
      }
      a.val.case_Nego_accept = cexts;
      break;
    case TLS_nego_retry:
      a.tag = TLSConstants_Nego_retry;
      c = KRML_HOST_MALLOC(app_cookie_len);
      if(app_cookie != NULL) memcpy(c, app_cookie, app_cookie_len);
      a.val.case_Nego_retry = (FStar_Bytes_bytes){.data = (const char*)c, .length = app_cookie_len};
      break;
    default:
      KRML_HOST_PRINTF("mitls_nego_action: unsupported (%04x)\n", r);
      KRML_HOST_EXIT(1);
  }

  return a;
}

int MITLS_CALLCONV FFI_mitls_configure_nego_callback(mitls_state *state, void *cb_state, pfn_FFI_nego_cb nego_cb)
{
  ENTER_HEAP_REGION(state->rgn);
  wrapped_nego_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_nego_cb));
  cbs->cb_state = cb_state;
  cbs->cb = nego_cb;
  state->cfg = FFI_ffiSetNegoCallback(state->cfg, (void*)cbs, nego_cb_proxy);
  LEAVE_HEAP_REGION();
  if (HAD_OUT_OF_MEMORY) {
    return 0;
  }
  return 1;
}

typedef struct {
  void* cb_state;
  pfn_FFI_cert_select_cb select;
  pfn_FFI_cert_format_cb format;
  pfn_FFI_cert_sign_cb sign;
  pfn_FFI_cert_verify_cb verify;
} wrapped_cert_cb;

static Parsers_SignatureScheme_signatureScheme_tags tls_of_pki(mitls_signature_scheme sa)
{
  switch(sa)
  {
    //  rsa_pkcs1_sha1(0x0201),
    case 0x0201: return Parsers_SignatureScheme_Rsa_pkcs1_sha1;
    //  rsa_pkcs1_sha256(0x0401),
    case 0x0401: return Parsers_SignatureScheme_Rsa_pkcs1_sha256;
    //  rsa_pkcs1_sha384(0x0501),
    case 0x0501: return Parsers_SignatureScheme_Rsa_pkcs1_sha384;
    //  rsa_pkcs1_sha512(0x0601),
    case 0x0601: return Parsers_SignatureScheme_Rsa_pkcs1_sha512;
    //  rsa_pss_sha256(0x0804),
    case 0x0804: return Parsers_SignatureScheme_Rsa_pss_rsae_sha256;
    //  rsa_pss_sha384(0x0805),
    case 0x0805: return Parsers_SignatureScheme_Rsa_pss_rsae_sha384;
    //  rsa_pss_sha512(0x0806),
    case 0x0806: return Parsers_SignatureScheme_Rsa_pss_rsae_sha512;
    //  ecdsa_sha1(0x0203),
    case 0x0203: return Parsers_SignatureScheme_Ecdsa_sha1;
    //  ecdsa_secp256r1_sha256(0x0403),
    case 0x0403: return Parsers_SignatureScheme_Ecdsa_secp256r1_sha256;
    //  ecdsa_secp384r1_sha384(0x0503),
    case 0x0503: return Parsers_SignatureScheme_Ecdsa_secp384r1_sha384;
    //  ecdsa_secp521r1_sha512(0x0603),
    case 0x0603: return Parsers_SignatureScheme_Ecdsa_secp521r1_sha512;
    //  ed25519(0x0807),
    //  ed448(0x0808),
    default:
      KRML_HOST_PRINTF("tls_of_pki: unsupported (%04x)\n", sa);
      KRML_HOST_EXIT(1);
  }
}

static mitls_signature_scheme pki_of_tls(Parsers_SignatureScheme_signatureScheme_tags sa)
{
  switch(sa)
  {
    //  rsa_pkcs1_sha1(0x0201),
    case Parsers_SignatureScheme_Rsa_pkcs1_sha1: return 0x0201;
    //  rsa_pkcs1_sha256(0x0401),
    case Parsers_SignatureScheme_Rsa_pkcs1_sha256: return 0x0401;
    //  rsa_pkcs1_sha384(0x0501),
    case Parsers_SignatureScheme_Rsa_pkcs1_sha384: return 0x0501;
    //  rsa_pkcs1_sha512(0x0601),
    case Parsers_SignatureScheme_Rsa_pkcs1_sha512: return 0x0601;
    //  rsa_pss_sha256(0x0804),
    case Parsers_SignatureScheme_Rsa_pss_rsae_sha256: return 0x0804;
    //  rsa_pss_sha384(0x0805),
    case Parsers_SignatureScheme_Rsa_pss_rsae_sha384: return 0x0805;
    //  rsa_pss_sha512(0x0806),
    case Parsers_SignatureScheme_Rsa_pss_rsae_sha512: return 0x0806;
    //  ecdsa_sha1(0x0203),
    case Parsers_SignatureScheme_Ecdsa_sha1: return 0x0203;
    //  ecdsa_secp256r1_sha256(0x0403),
    case Parsers_SignatureScheme_Ecdsa_secp256r1_sha256: return 0x0403;
    //  ecdsa_secp384r1_sha384(0x0503),
    case Parsers_SignatureScheme_Ecdsa_secp384r1_sha384: return 0x0503;
    //  ecdsa_secp521r1_sha512(0x0603),
    case Parsers_SignatureScheme_Ecdsa_secp521r1_sha512: return 0x0603;
    //  ed25519(0x0807), ed448(0x0808),
    default:
      KRML_HOST_PRINTF("pki_of_tls: unsupported (%d)\n", sa);
      KRML_HOST_EXIT(1);
  }
}

static size_t list_sa_len(Prims_list__Parsers_SignatureScheme_signatureScheme *l)
{
  if (l->tag == Prims_Cons)
  {
    return 1 + list_sa_len(l->tl);
  }
  return 0;
}

static FStar_Pervasives_Native_option__K___uint64_t_Parsers_SignatureScheme_signatureScheme
  wrapped_select(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st, Parsers_ProtocolVersion_protocolVersion pv,
    FStar_Bytes_bytes sni, FStar_Bytes_bytes alpn,
    Prims_list__Parsers_SignatureScheme_signatureScheme *sal)
{
  wrapped_cert_cb* s = (wrapped_cert_cb*)cbs;
  size_t sigalgs_len = list_sa_len(sal);
  mitls_signature_scheme selected;
  mitls_signature_scheme *sigalgs = alloca(sigalgs_len*sizeof(mitls_signature_scheme));
  Prims_list__Parsers_SignatureScheme_signatureScheme *cur = sal;

  for(size_t i = 0; i < sigalgs_len; i++)
  {
    sigalgs[i] = pki_of_tls(cur->hd.tag);
    cur = cur->tl;
  }

  FStar_Pervasives_Native_option__K___uint64_t_Parsers_SignatureScheme_signatureScheme res;
  void* chain = s->select(s->cb_state, convert_pv(pv),
    (const unsigned char*)sni.data, sni.length,
    (const unsigned char*)alpn.data, alpn.length,
    sigalgs, sigalgs_len, &selected);

  if(chain == NULL) {
    res.tag = FStar_Pervasives_Native_None;
  } else {
    K___uint64_t_Parsers_SignatureScheme_signatureScheme sig;
    // silence a GCC warning about sig.snd._0.length possibly uninitialized
    memset(&sig, 0, sizeof(sig));
    res.tag = FStar_Pervasives_Native_Some;
    sig.fst = (uint64_t)chain;
    sig.snd.tag = tls_of_pki(selected);
    res.v = sig;
  }
  return res;
}

static Prims_list__FStar_Bytes_bytes* wrapped_format(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st, uint64_t cert)
{
  wrapped_cert_cb* s = (wrapped_cert_cb*)cbs;
  unsigned char *buffer = KRML_HOST_MALLOC(MAX_CHAIN_LEN);
  size_t r = s->format(s->cb_state, (const void *)(size_t)cert, buffer);
  FStar_Bytes_bytes b = {.length = r, .data = (const char*)buffer};
  return FFI_ffiSplitChain(b);
}


static FStar_Pervasives_Native_option__FStar_Bytes_bytes wrapped_sign(
  FStar_Dyn_dyn cbs, FStar_Dyn_dyn st, uint64_t cert,
  Parsers_SignatureScheme_signatureScheme sa, FStar_Bytes_bytes tbs)
{
  wrapped_cert_cb* s = (wrapped_cert_cb*)cbs;
  unsigned char* sig = KRML_HOST_MALLOC(MAX_SIGNATURE_LEN);
  FStar_Pervasives_Native_option__FStar_Bytes_bytes res = {.tag = FStar_Pervasives_Native_None};
  mitls_signature_scheme sigalg = pki_of_tls(sa.tag);

  size_t slen = s->sign(s->cb_state, (const void *)(size_t)cert, sigalg,
    (const unsigned char*)tbs.data, tbs.length, sig);

  if(slen > 0) {
    res.tag = FStar_Pervasives_Native_Some;
    res.v = (FStar_Bytes_bytes){.length = slen, .data = (const char*)sig};
  }

  return res;
}

static bool wrapped_verify(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st,
  Prims_list__FStar_Bytes_bytes *certs, Parsers_SignatureScheme_signatureScheme sa,
  FStar_Bytes_bytes tbs, FStar_Bytes_bytes sig)
{
  wrapped_cert_cb* s = (wrapped_cert_cb*)cbs;
  FStar_Bytes_bytes chain = Cert_certificateListBytes(certs);
  mitls_signature_scheme sigalg = pki_of_tls(sa.tag);

  int r = (s->verify(s->cb_state,
    (const unsigned char*)chain.data, chain.length, sigalg,
    (const unsigned char*)tbs.data, tbs.length,
    (const unsigned char*)sig.data, sig.length) != 0);

  return r;
}

int MITLS_CALLCONV FFI_mitls_configure_cert_callbacks(/* in */ mitls_state *state, void *cb_state, mitls_cert_cb *cert_cb)
{
  ENTER_HEAP_REGION(state->rgn);
  wrapped_cert_cb* cbs = KRML_HOST_MALLOC(sizeof(wrapped_cert_cb));

  cbs->cb_state = cb_state;
  cbs->select = cert_cb->select;
  cbs->format = cert_cb->format;
  cbs->sign = cert_cb->sign;
  cbs->verify = cert_cb->verify;

  TLSConstants_cert_cb cb = {
    .app_context = (void*)cbs,
    .cert_select_ptr = NULL,
    .cert_select_cb = wrapped_select,
    .cert_format_ptr = NULL,
    .cert_format_cb = wrapped_format,
    .cert_sign_ptr = NULL,
    .cert_sign_cb = wrapped_sign,
    .cert_verify_ptr = NULL,
    .cert_verify_cb = wrapped_verify
  };

  state->cfg = FFI_ffiSetCertCallbacks(state->cfg, cb);
  LEAVE_HEAP_REGION();
  if (HAD_OUT_OF_MEMORY) {
    return 0;
  }
  return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_early_data(/* in */ mitls_state *state, uint32_t max_early_data)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetEarlyData(state->cfg, max_early_data);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return 1;
}

// Called by the host app to free a mitls_state allocated by FFI_mitls_configure()
void MITLS_CALLCONV FFI_mitls_close(mitls_state *state)
{
    if (state) {
        HEAP_REGION rgn = state->rgn;
        KRML_HOST_FREE(state);
        DESTROY_HEAP_REGION(rgn);
    }
}

void MITLS_CALLCONV FFI_mitls_free(/* in */ mitls_state *state, void* pv)
{
    ENTER_HEAP_REGION(state->rgn);
    KRML_HOST_FREE(pv);
    LEAVE_HEAP_REGION();
}

typedef struct {
  void* send_recv_ctx;
  pfn_FFI_send send;
  pfn_FFI_recv recv;
} wrapped_transport_cb;

static int32_t wrapped_send(void* ctx, uint8_t* buffer, uint32_t buffer_size)
{
  wrapped_transport_cb* tcb = (wrapped_transport_cb*) ctx;
  return (int32_t)tcb->send(tcb->send_recv_ctx, (const void*)buffer, (size_t)buffer_size);
}

static int32_t wrapped_recv(void* ctx, uint8_t* buffer, uint32_t len)
{
  wrapped_transport_cb* tcb = (wrapped_transport_cb*) ctx;
  return (int32_t)tcb->recv(tcb->send_recv_ctx, (void*)buffer, (size_t)len);
}

// Called by the host app to create a TLS connection.
int MITLS_CALLCONV FFI_mitls_connect(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state)
{
    int ret = 0;
    LOCK_MUTEX(&lock);
    ENTER_HEAP_REGION(state->rgn);

    wrapped_transport_cb* tcb = KRML_HOST_MALLOC(sizeof(wrapped_transport_cb));
    tcb->send_recv_ctx = send_recv_ctx;
    tcb->send = psend;
    tcb->recv = precv;

    K___Connection_connection_Prims_int result = FFI_connect((FStar_Dyn_dyn)tcb, wrapped_send, wrapped_recv, state->cfg);
    state->cxn = result.fst;
    ret = (result.snd == 0);

    LEAVE_HEAP_REGION();
    UNLOCK_MUTEX(&lock);
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return ret;
}

// Called by the host server app, after a client has connected to a socket and the calling server has accepted the TCP connection.
int MITLS_CALLCONV FFI_mitls_accept_connected(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state)
{
    int ret = 0;
    LOCK_MUTEX(&lock);
    ENTER_HEAP_REGION(state->rgn);

    wrapped_transport_cb* tcb = KRML_HOST_MALLOC(sizeof(wrapped_transport_cb));
    tcb->send_recv_ctx = send_recv_ctx;
    tcb->send = psend;
    tcb->recv = precv;

    K___Connection_connection_Prims_int result = FFI_ffiAcceptConnected((FStar_Dyn_dyn)tcb, wrapped_send, wrapped_recv, state->cfg);
    state->cxn = result.fst;
    ret = (result.snd == 0) ? 1 : 0; // return success (1) if result.snd is 0.

    LEAVE_HEAP_REGION();
    UNLOCK_MUTEX(&lock);
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }
    return ret;
}

// Called by the host app transmit a packet
int MITLS_CALLCONV FFI_mitls_send(/* in */ mitls_state *state, const unsigned char *buffer, size_t buffer_size)
{
    int ret;

    ENTER_HEAP_REGION(state->rgn);
    LOCK_MUTEX(&lock);
    ret = FFI_ffiSend(state->cxn, (FStar_Bytes_bytes){.data = (const char*)buffer, .length = buffer_size});
    UNLOCK_MUTEX(&lock);
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
        return 0;
    }

    return 1;
}

// Called by the host app to receive a packet
unsigned char *MITLS_CALLCONV FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size)
{
    unsigned char *p = NULL;
    FStar_Bytes_bytes ret = {.data=NULL,.length=0};
    *packet_size = 0;

    LOCK_MUTEX(&lock);
    ENTER_HEAP_REGION(state->rgn);

    ret = FFI_ffiRecv(state->cxn);
    if (ret.length) {
      p = KRML_HOST_MALLOC(ret.length);
      memcpy((char*)p, ret.data, ret.length);
    }
    LEAVE_HEAP_REGION();
    UNLOCK_MUTEX(&lock);
    if (HAD_OUT_OF_MEMORY) {
        return NULL;
    }
    *packet_size = ret.length;
    return p;
}

static int get_exporter(Connection_connection cxn, int early, /* out */ mitls_secret *secret)
{
  FStar_Pervasives_Native_option__K___Spec_Hash_Definitions_hash_alg_EverCrypt_aead_alg_FStar_Bytes_bytes ret;

  ret = FFI_ffiGetExporter(cxn, (early) ? true : false);
  if (ret.tag != FStar_Pervasives_Native_Some) {
     KRML_HOST_PRINTF("the requested secret is not yet available");
     return 0;
  }
  secret->hash = ret.v.fst;
  secret->ae = ret.v.snd;
  size_t len=ret.v.thd.length;
  if (len > sizeof(secret->secret)) {
    KRML_HOST_PRINTF("Unexpected secret length");
    KRML_HOST_EXIT(1);
  }
  memcpy(secret->secret, ret.v.thd.data, len);
  return 1;
}


int MITLS_CALLCONV FFI_mitls_get_exporter(/* in */ mitls_state *state, int early, /* out */ mitls_secret *secret)
{
  int ret=0;
  ENTER_HEAP_REGION(state->rgn);
  ret = get_exporter(state->cxn, early, secret);
  LEAVE_HEAP_REGION();
  if (HAD_OUT_OF_MEMORY) {
    return 0;
  }
  return ret;
}

void *MITLS_CALLCONV FFI_mitls_get_cert(/* in */ mitls_state *state, /* out */ size_t *cert_size)
{
    FStar_Bytes_bytes ret = {.length = 0, .data = NULL};
    ENTER_HEAP_REGION(state->rgn);
    ret = FFI_getCert(state->cxn);
    *cert_size = ret.length;
    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY) {
      return NULL;
    }
    return (void*)ret.data; // bugbug: casting away const
}

/*************************************************************************
* QUIC API
**************************************************************************/

typedef struct quic_state {
   HEAP_REGION rgn;
   uint8_t is_server;
   uint8_t is_complete;
   uint8_t is_post_hs;
   Old_Handshake_hs hs;
} quic_state;

static TLSConstants_config quic_set_config(TLSConstants_config c0, const quic_config *cfg)
{
    TLSConstants_config c = c0;

    if(cfg->enable_0rtt) {
      c = FFI_ffiSetEarlyData(c, 0xffffffff);
    }
 
    if (cfg->cipher_suites) {
       Prims_string str = CopyPrimsString(cfg->cipher_suites);
       c = FFI_ffiSetCipherSuites(c, str);
    }

    if (cfg->named_groups) {
       Prims_string str = CopyPrimsString(cfg->named_groups);
       c = FFI_ffiSetNamedGroups(c, str);
    }

    if (cfg->signature_algorithms) {
       Prims_string str = CopyPrimsString(cfg->signature_algorithms);
       c = FFI_ffiSetSignatureAlgorithms(c, str);
    }

    if (cfg->alpn) {
       TLSConstants_alpn apl = alpn_list_of_array(cfg->alpn, cfg->alpn_count);
       c = FFI_ffiSetALPN(c, apl);
    }

    if(cfg->exts != NULL && cfg->exts_count > 0)
    {
      mitls_extension *cur = (mitls_extension*)cfg->exts;
      for(size_t i = 0; i < cfg->exts_count; i++, cur++)
      {
        char *ext = KRML_HOST_MALLOC(cur->ext_data_len);
        memcpy(ext, cur->ext_data, cur->ext_data_len);
        c = FFI_ffiAddCustomExtension(c, cur->ext_type,
          (FStar_Bytes_bytes){.data = ext, .length = cur->ext_data_len});
      }
    }

    if(cfg->ticket_enc_alg && cfg->ticket_key) {
        FStar_Bytes_bytes key;
        bool b;
        MakeFStar_Bytes_bytes(&key, cfg->ticket_key, cfg->ticket_key_len);
        LOCK_MUTEX(&lock);
        FFI_ffiSetTicketKey(cfg->ticket_enc_alg, key);
        UNLOCK_MUTEX(&lock);
    }

    if(cfg->server_ticket && cfg->server_ticket->ticket_len > 0) {
      FStar_Bytes_bytes tid, si;
      MakeFStar_Bytes_bytes(&tid, cfg->server_ticket->ticket, cfg->server_ticket->ticket_len);
      MakeFStar_Bytes_bytes(&si, cfg->server_ticket->session, cfg->server_ticket->session_len);
      c = FFI_ffiSetTicket(c, tid, si);
    }

    if (cfg->ticket_callback) {
      wrapped_ticket_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_ticket_cb));
      cbs->cb_state = cfg->callback_state;
      cbs->cb = cfg->ticket_callback;
      c = FFI_ffiSetTicketCallback(c, (void*)cbs, ticket_cb_proxy);
    }

    if (cfg->nego_callback) {
      wrapped_nego_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_nego_cb));
      cbs->cb_state = cfg->callback_state;
      cbs->cb = cfg->nego_callback;
      c = FFI_ffiSetNegoCallback(c, (void*)cbs, nego_cb_proxy);
    }

    if(cfg->cert_callbacks) {
      wrapped_cert_cb* cbs = KRML_HOST_MALLOC(sizeof(wrapped_cert_cb));

      cbs->cb_state = cfg->callback_state;
      cbs->select = cfg->cert_callbacks->select;
      cbs->format = cfg->cert_callbacks->format;
      cbs->sign = cfg->cert_callbacks->sign;
      cbs->verify = cfg->cert_callbacks->verify;

      TLSConstants_cert_cb cb = {
        .app_context = (void*)cbs,
        .cert_select_ptr = NULL,
        .cert_select_cb = wrapped_select,
        .cert_format_ptr = NULL,
        .cert_format_cb = wrapped_format,
        .cert_sign_ptr = NULL,
        .cert_sign_cb = wrapped_sign,
        .cert_verify_ptr = NULL,
        .cert_verify_cb = wrapped_verify
      };

      c = FFI_ffiSetCertCallbacks(c, cb);
    }

    return c;
}

int MITLS_CALLCONV FFI_mitls_quic_create(quic_state **state, const quic_config *cfg)
{
    quic_state* st = NULL;
    *state = NULL;
    HEAP_REGION rgn;

    CREATE_HEAP_REGION(&rgn);
    if (!VALID_HEAP_REGION(rgn)) {
        return 0; // out of memory
    }
    
    st = KRML_HOST_MALLOC(sizeof(quic_state));
    memset(st, 0, sizeof(*st));
    st->is_server = cfg->is_server;

    Prims_string host_name = CopyPrimsString(cfg->host_name != NULL ? cfg->host_name : "");
    TLSConstants_config config = QUIC_ffiConfig((FStar_Bytes_bytes){.data=host_name,.length=strlen(host_name)});
    
    config = quic_set_config(config, cfg);
    st->hs = QUIC_create_hs(st->is_server, config);

    LEAVE_HEAP_REGION();
    if (HAD_OUT_OF_MEMORY || st == NULL) {
      DESTROY_HEAP_REGION(rgn);
      return 0;
    }
    
    st->rgn = rgn;
    *state = st;
    return 1;
}

#ifdef _KERNEL_MODE
typedef struct {
    quic_state *state;
    QUIC_hs_in *in;
    QUIC_hs_result *r;
} quic_process_state;

static VOID quic_process_callout(PVOID Parameter)
{
    quic_process_state *s = (quic_process_state*)Parameter;
    *s->r = QUIC_process_hs(s->state->hs, *s->in);
}
#endif

int MITLS_CALLCONV FFI_mitls_quic_process(quic_state *st, quic_process_ctx *ctx)
{
  int r = 0;
  ENTER_HEAP_REGION(st->rgn);
  unsigned char z = 0;
  
  QUIC_hs_in in;
  in.input = (FStar_Bytes_bytes){
    .data = (char*)(ctx->input == NULL ? &z : ctx->input),
    .length = ctx->input_len
  };
  in.max_output = ctx->output_len;  

#ifdef _KERNEL_MODE
  QUIC_hs_result res;
  quic_process_state s = {.state = st, .in = &in, .r = &res };
  NTSTATUS status = KeExpandKernelStackAndCallout(quic_process_callout, &s, MAXIMUM_EXPANSION_SIZE);
  
  if (!NT_SUCCESS(status)) {
    KRML_HOST_PRINTF("KeExpandKernelCallstackAndCallout for quic_process_callout failed st=%x", status);
    ctx->tls_error = 0x0350; // Internal error
    return 0;
  }
#else
  QUIC_hs_result res = QUIC_process_hs(st->hs, in);
#endif

  ctx->flags = 0;
  if(res.tag == QUIC_HS_SUCCESS)
  {
    QUIC_hs_out out = res.val.case_HS_SUCCESS;
    ctx->consumed_bytes = out.consumed;
    ctx->to_be_written = out.to_be_written;
    ctx->output_len = out.output.length;
    if(ctx->output != NULL && ctx->output_len)
      memcpy(ctx->output, out.output.data, ctx->output_len);
    
    if(out.is_complete) st->is_complete = 1;
    if(out.is_writable) ctx->flags |= QFLAG_APPLICATION_KEY;
    if(out.is_early_rejected) ctx->flags |= QFLAG_REJECTED_0RTT;
    if(out.is_post_handshake) st->is_post_hs = 1;
    r = 1;
  }
  else
  {
    ctx->tls_error = res.val.case_HS_ERROR;
    ctx->output_len = 0;
    ctx->consumed_bytes = 0;
  }

  K___Prims_int_Prims_int epochs = QUIC_get_epochs(st->hs);
  ctx->cur_reader_key = epochs.fst;
  ctx->cur_writer_key = epochs.snd;
  if(st->is_complete) ctx->flags |= QFLAG_COMPLETE;
  if(st->is_post_hs) ctx->flags |= QFLAG_POST_HANDSHAKE;
  
  LEAVE_HEAP_REGION();
  return r;
}

int MITLS_CALLCONV FFI_mitls_quic_get_record_key(quic_state *st, quic_raw_key *key, int32_t epoch, quic_direction rw)
{
  int res = 0;
  FStar_Pervasives_Native_option__QUIC_raw_key r;
  
  ENTER_HEAP_REGION(st->rgn);
  r = QUIC_get_key(st->hs, epoch, (int)rw);
  
  if(r.tag == FStar_Pervasives_Native_Some)
  {
    QUIC_raw_key k = r.v;
    key->alg = CONVERT_AEAD(k.alg);
    memcpy(key->aead_key, k.aead_key.data, k.aead_key.length);
    memcpy(key->aead_iv, k.aead_iv.data, k.aead_iv.length);
    memcpy(key->pne_key, k.pn_key.data, k.pn_key.length);
    res = 1;
  }
  
  LEAVE_HEAP_REGION();
  return res;
}

int MITLS_CALLCONV FFI_mitls_quic_get_record_secrets(quic_state *st, quic_secret *crs, quic_secret *srs)
{
  int res = 0;
  FStar_Pervasives_Native_option__Old_KeySchedule_raw_rekey_secrets r;
  
  ENTER_HEAP_REGION(st->rgn);
  r = QUIC_get_secrets(st->hs);
  
  if(r.tag == FStar_Pervasives_Native_Some)
  {
    Old_KeySchedule_raw_rekey_secrets s = r.v;
    srs->ae = crs->ae = CONVERT_AEAD(s.rekey_aead);
    srs->hash = crs->hash = CONVERT_HASH(s.rekey_hash);
    memcpy(crs->secret, s.rekey_client.data, s.rekey_client.length);
    memcpy(srs->secret, s.rekey_server.data, s.rekey_server.length);
    res = 1;
  }
  
  LEAVE_HEAP_REGION();
  return res;
}

int MITLS_CALLCONV FFI_mitls_quic_send_ticket(quic_state *st, const unsigned char *ticket_data, size_t ticket_data_len)
{
  int r = 0;
  ENTER_HEAP_REGION(st->rgn);
  FStar_Bytes_bytes data = {
   .data = KRML_HOST_MALLOC(ticket_data_len),
   .length = ticket_data_len
  };
  memcpy((unsigned char*)data.data, ticket_data, ticket_data_len);
  r = QUIC_send_ticket(st->hs, data);
  LEAVE_HEAP_REGION();
  return r;
}

void MITLS_CALLCONV FFI_mitls_quic_free(quic_state *state)
{
    HEAP_REGION rgn = state->rgn;
    ENTER_HEAP_REGION(state->rgn);
    KRML_HOST_FREE(state);
    LEAVE_HEAP_REGION();
    DESTROY_HEAP_REGION(rgn);
}


static const unsigned char *FFI_mitls_memmem(
  const unsigned char *b, size_t blen,
  const unsigned char *search, size_t slen)
{
  const unsigned char *cur;
  if (blen < slen) return NULL;
  if (!slen) return b;

	for (cur = b; cur <= b + blen - slen; cur++)
		if (cur[0] == search[0] && !memcmp(cur+1, search+1, slen-1))
			return cur;

	return NULL;
}

int MITLS_CALLCONV FFI_mitls_get_hello_summary(
  const unsigned char *buffer, size_t buffer_len,
  int has_record, mitls_hello_summary *summary,
  unsigned char **cookie, size_t *cookie_len,
  unsigned char **ticket_data, size_t *ticket_data_len)
{
  HEAP_REGION rgn;
  int ret = 0;
  FStar_Pervasives_Native_option__QUIC_chSummary ch;

  *cookie = NULL; *cookie_len = 0;
  *ticket_data = NULL; *ticket_data_len = 0;
  memset(&ch, 0, sizeof(ch));

  CREATE_HEAP_REGION(&rgn);
  if (!VALID_HEAP_REGION(rgn)) {
    return 0;
  }

  FStar_Bytes_bytes b = {.data = (const char*)buffer, .length = buffer_len};
  ch = QUIC_peekClientHello(b, has_record);

  memset(summary, 0, sizeof(mitls_hello_summary));
  if(ch.tag == FStar_Pervasives_Native_Some)
  {
    QUIC_chSummary s = ch.v;
    summary->sni = FFI_mitls_memmem(buffer, buffer_len,
      (const unsigned char*)s.ch_sni.data, s.ch_sni.length);
    summary->sni_len = s.ch_sni.length;

    summary->alpn = FFI_mitls_memmem(buffer, buffer_len,
      (const unsigned char*)s.ch_alpn.data, s.ch_alpn.length);
    summary->alpn_len = s.ch_alpn.length;

    summary->extensions = FFI_mitls_memmem(buffer, buffer_len,
      (const unsigned char*)s.ch_extensions.data, s.ch_extensions.length);
    summary->extensions_len = s.ch_extensions.length;
    ret = 1;
  }
  LEAVE_HEAP_REGION();

  if(ret && ch.v.ch_cookie.tag == FStar_Pervasives_Native_Some)
  {
    ENTER_GLOBAL_HEAP_REGION();
    *cookie_len = ch.v.ch_cookie.v.length;
    *cookie = KRML_HOST_MALLOC(*cookie_len);
    memcpy(*cookie, ch.v.ch_cookie.v.data, *cookie_len);
    LEAVE_GLOBAL_HEAP_REGION();
  }

  if(ret && ch.v.ch_ticket_data.tag == FStar_Pervasives_Native_Some)
  {
    ENTER_GLOBAL_HEAP_REGION();
    *ticket_data_len = ch.v.ch_ticket_data.v.length;
    *ticket_data = KRML_HOST_MALLOC(*ticket_data_len);
    memcpy(*ticket_data, ch.v.ch_ticket_data.v.data, *ticket_data_len);
    LEAVE_GLOBAL_HEAP_REGION();
  }
  
  DESTROY_HEAP_REGION(rgn);
  return ret;
}

int MITLS_CALLCONV FFI_mitls_find_custom_extension(int is_server, const unsigned char *exts, size_t exts_len, uint16_t ext_type, unsigned char **ext_data, size_t *ext_data_len)
{
  HEAP_REGION rgn;
  int ret = 0;

  CREATE_HEAP_REGION(&rgn);
  if (!VALID_HEAP_REGION(rgn)) {
    return 0;
  }

  FStar_Bytes_bytes b = {.data = (const char*)exts, .length = exts_len};
  FStar_Pervasives_Native_option__FStar_Bytes_bytes ob;
  ob = FFI_ffiFindCustomExtension((bool)is_server, b, ext_type);

  *ext_data = NULL; *ext_data_len = 0;
  if(ob.tag == FStar_Pervasives_Native_Some)
  {
    *ext_data_len = ob.v.length;
    *ext_data = (unsigned char*)FFI_mitls_memmem(exts, exts_len, (const unsigned char*)ob.v.data, *ext_data_len);
    ret = 1;
  }

  LEAVE_HEAP_REGION();
  if (HAD_OUT_OF_MEMORY) {
    ret = 0;
  }

  DESTROY_HEAP_REGION(rgn);
  return ret;
}

extern void MITLS_CALLCONV FFI_mitls_global_free(void* pv)
{
  ENTER_GLOBAL_HEAP_REGION();
  KRML_HOST_FREE(pv);
  LEAVE_GLOBAL_HEAP_REGION();
}

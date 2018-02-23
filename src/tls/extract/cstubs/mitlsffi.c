#include <memory.h>
#include <assert.h>
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

#include "FFI.h"    // Kremlin-extracted file
#include "QUIC.h"   // Kremlin-extracted file
#include "mitlsffi.h"
#include "RegionAllocator.h"

// This file is hand-written C code, to wrap the Kremlin-extracted
// code to match the mitlsffi.h interface.
//
// So it uses KRML_HOST_MALLOC and KRML_HOST_FREE in order to
// support the same pluggable heap manager as the rest of miTLS.

extern int CoreCrypto_Initialize(void);
extern void CoreCrypto_Terminate(void);

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
    if (dst) {
        memcpy((char*)dst, src, len);
    }
    return dst;
}

static bool MakeFStar_Bytes_bytes(FStar_Bytes_bytes *b, const char *data, uint32_t length)
{
    b->data = KRML_HOST_MALLOC(length);
    if (!b->data) {
        return false;
    }
    memcpy((char*)b->data, data, length);
    b->length = length;
    return true;
}

void NoPrintf(const char *fmt, ...)
{
}

pfn_mitls_trace_callback trace_callback;

void TracePrintf(const char *fmt, ...)
{
    va_list args;
    va_start (args, fmt);

    char buffer[160];
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
  if (CoreCrypto_Initialize() == 0) {
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
  #else
    InitializeCriticalSection(&lock);
    #if LOG_TO_CHOICE
    if (!g_LogPrint) {
        if (GetEnvironmentVariableA("MITLS_LOG", NULL, 0) == 0) {
            g_LogPrint = (p_log)DbgPrint; // if not set, log to the debugger by default
        } else {
            g_LogPrint = (p_log)printf;
        }
    }
    #endif
  #endif
#else
  if (pthread_mutex_init(&lock, NULL) != 0) {
    CoreCrypto_Terminate();
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

  kremlinit_globals();
  return 1; // success
}

void MITLS_CALLCONV FFI_mitls_cleanup(void)
{
    CoreCrypto_Terminate();
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
    int ret;

    *state = NULL;

    HEAP_REGION rgn;
    CREATE_HEAP_REGION(&rgn);
    if (!VALID_HEAP_REGION(rgn)) {
        return 0;
    }

    Prims_string host = CopyPrimsString(host_name);
    Prims_string version = CopyPrimsString(tls_version);

    TLSConstants_config config = FFI_ffiConfig(version, (FStar_Bytes_bytes){.data=host,.length=strlen(host_name)});

    // Allocate space on the heap, to store an OCaml value
    mitls_state *s = (mitls_state*)KRML_HOST_MALLOC(sizeof(mitls_state));
    if (s) {
        s->cfg = config;
        s->rgn = rgn;
        *state = s;
        ret = 1;
    } else {
        DESTROY_HEAP_REGION(rgn);
        ret = 0;
    }

    LEAVE_HEAP_REGION();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_set_ticket_key(const char *alg, const char *tk, size_t klen)
{
    // bugbug: this uses the global region for heap allocations
    LOCK_MUTEX(&lock);
    FStar_Bytes_bytes key;
    bool b = MakeFStar_Bytes_bytes(&key, tk, klen);
    if(b) b = FFI_ffiSetTicketKey(alg, key);
    UNLOCK_MUTEX(&lock);
    return (b) ? 1 : 0;
}

int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char * cs)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetCipherSuites(state->cfg, cs);
    LEAVE_HEAP_REGION();
    return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char * sa)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetSignatureAlgorithms(state->cfg, sa);
    LEAVE_HEAP_REGION();
    return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char * ng)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetNamedGroups(state->cfg, ng);
    LEAVE_HEAP_REGION();
    return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_alpn(/* in */ mitls_state *state, const char *apl)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetALPN(state->cfg, apl);
    LEAVE_HEAP_REGION();
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
    .ticket = ticket.data,
    .session_len = session.length,
    .session = session.data
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
    return 1;
}

typedef struct {
  void* cb_state;
  pfn_FFI_server_nego_cb cb;
} wrapped_nego_cb;

static mitls_version convert_pv(TLSConstants_protocolVersion_ pv)
{
  switch(pv.tag)
  {
    case TLSConstants_SSL_3p0:
      return TLS_SSL3;
    case TLSConstants_TLS_1p0:
      return TLS_1p0;
    case TLSConstants_TLS_1p1:
      return TLS_1p1;
    case TLSConstants_TLS_1p2:
      return TLS_1p2;
    case TLSConstants_TLS_1p3:
      return TLS_1p3;
    default:
      return TLS_SSL3;
  }
  return TLS_SSL3; // unreachable
}

static TLSConstants_server_nego_action nego_cb_proxy(FStar_Dyn_dyn cbs, TLSConstants_protocolVersion_ pv,
  FStar_Bytes_bytes extb, FStar_Pervasives_Native_option__FStar_Bytes_bytes cookie)
{
  wrapped_nego_cb *cb = (wrapped_nego_cb*)cbs;
  char *app_cookie = NULL, *extra_exts = NULL, *c;
  size_t app_cookie_len = 0, extra_exts_len = 0;

  if(cookie.tag == FStar_Pervasives_Native_Some)
  {
    app_cookie = (char *)cookie.v.data;
    app_cookie_len = cookie.v.length;
  }

  TLSConstants_server_nego_action a;
  mitls_nego_action r = cb->cb(cb->cb_state, convert_pv(pv), extb.data, extb.length,
    &extra_exts, &extra_exts_len, &app_cookie, &app_cookie_len);

  switch(r)
  {
    case TLS_nego_abort:
      a.tag = TLSConstants_Nego_abort;
      break;
    case TLS_nego_accept:
      a.tag = TLSConstants_Nego_accept;
      c = KRML_HOST_MALLOC(extra_exts_len);
      memcpy(c, extra_exts, extra_exts_len);
      a.val.case_Nego_accept = (FStar_Bytes_bytes){.data = c, .length = extra_exts_len};
      break;
    case TLS_nego_retry:
      a.tag = TLSConstants_Nego_retry;
      c = KRML_HOST_MALLOC(app_cookie_len);
      if(app_cookie != NULL) memcpy(c, app_cookie, app_cookie_len);
      a.val.case_Nego_retry = (FStar_Bytes_bytes){.data = c, .length = app_cookie_len};
      break;
  }

  return a;
}

int MITLS_CALLCONV FFI_mitls_configure_server_nego_callback(mitls_state *state, void *cb_state, pfn_FFI_server_nego_cb nego_cb)
{
  ENTER_HEAP_REGION(state->rgn);
  wrapped_nego_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_nego_cb));
  cbs->cb_state = cb_state;
  cbs->cb = nego_cb;
  state->cfg = FFI_ffiSetNegoCallback(state->cfg, (void*)cbs, nego_cb_proxy);
  LEAVE_HEAP_REGION();
  return 1;
}

typedef struct {
  void* cb_state;
  pfn_FFI_cert_select_cb select;
  pfn_FFI_cert_format_cb format;
  pfn_FFI_cert_sign_cb sign;
  pfn_FFI_cert_verify_cb verify;
} wrapped_cert_cb;

static TLSConstants_signatureScheme_tags tls_of_pki(mitls_signature_scheme sa)
{
  switch(sa)
  {
    //  rsa_pkcs1_sha1(0x0201),
    case 0x0201: return TLSConstants_RSA_PKCS1_SHA1;
    //  rsa_pkcs1_sha256(0x0401),
    case 0x0401: return TLSConstants_RSA_PKCS1_SHA256;
    //  rsa_pkcs1_sha384(0x0501),
    case 0x0501: return TLSConstants_RSA_PKCS1_SHA384;
    //  rsa_pkcs1_sha512(0x0601),
    case 0x0601: return TLSConstants_RSA_PKCS1_SHA512;
    //  rsa_pss_sha256(0x0804),
    case 0x0804: return TLSConstants_RSA_PSS_SHA256;
    //  rsa_pss_sha384(0x0805),
    case 0x0805: return TLSConstants_RSA_PSS_SHA384;
    //  rsa_pss_sha512(0x0806),
    case 0x0806: return TLSConstants_RSA_PSS_SHA512;
    //  ecdsa_sha1(0x0203),
    case 0x0203: return TLSConstants_ECDSA_SHA1;
    //  ecdsa_secp256r1_sha256(0x0403),
    case 0x0403: return TLSConstants_ECDSA_SECP256R1_SHA256;
    //  ecdsa_secp384r1_sha384(0x0503),
    case 0x0503: return TLSConstants_ECDSA_SECP384R1_SHA384;
    //  ecdsa_secp521r1_sha512(0x0603),
    case 0x0603: return TLSConstants_ECDSA_SECP521R1_SHA512;
    //  ed25519(0x0807),
    //  ed448(0x0808),
    default:
      KRML_HOST_PRINTF("tls_of_pki: unsupported (%04x)\n", sa);
      KRML_HOST_EXIT(1);
  }
}

static mitls_signature_scheme pki_of_tls(TLSConstants_signatureScheme_tags sa)
{
  switch(sa)
  {
    //  rsa_pkcs1_sha1(0x0201),
    case TLSConstants_RSA_PKCS1_SHA1: return 0x0201;
    //  rsa_pkcs1_sha256(0x0401),
    case TLSConstants_RSA_PKCS1_SHA256: return 0x0401;
    //  rsa_pkcs1_sha384(0x0501),
    case TLSConstants_RSA_PKCS1_SHA384: return 0x0501;
    //  rsa_pkcs1_sha512(0x0601),
    case TLSConstants_RSA_PKCS1_SHA512: return 0x0601;
    //  rsa_pss_sha256(0x0804),
    case TLSConstants_RSA_PSS_SHA256: return 0x0804;
    //  rsa_pss_sha384(0x0805),
    case TLSConstants_RSA_PSS_SHA384: return 0x0805;
    //  rsa_pss_sha512(0x0806),
    case TLSConstants_RSA_PSS_SHA512: return 0x0806;
    //  ecdsa_sha1(0x0203),
    case TLSConstants_ECDSA_SHA1: return 0x0203;
    //  ecdsa_secp256r1_sha256(0x0403),
    case TLSConstants_ECDSA_SECP256R1_SHA256: return 0x0403;
    //  ecdsa_secp384r1_sha384(0x0503),
    case TLSConstants_ECDSA_SECP384R1_SHA384: return 0x0503;
    //  ecdsa_secp521r1_sha512(0x0603),
    case TLSConstants_ECDSA_SECP521R1_SHA512: return 0x0603;
    //  ed25519(0x0807), ed448(0x0808),
    default:
      KRML_HOST_PRINTF("pki_of_tls: unsupported (%d)\n", sa);
      KRML_HOST_EXIT(1);
  }
}

static size_t list_sa_len(Prims_list__TLSConstants_signatureScheme *l)
{
  if (l->tag == Prims_Cons)
  {
    return 1 + list_sa_len(l->tl);
  }
  return 0;
}

static FStar_Pervasives_Native_option__K___uint64_t_TLSConstants_signatureScheme
  wrapped_select(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st, FStar_Bytes_bytes sni,
    Prims_list__TLSConstants_signatureScheme *sal)
{
  wrapped_cert_cb* s = (wrapped_cert_cb*)cbs;
  size_t sigalgs_len = list_sa_len(sal);
  mitls_signature_scheme selected;
  mitls_signature_scheme *sigalgs = alloca(sigalgs_len*sizeof(mitls_signature_scheme));
  Prims_list__TLSConstants_signatureScheme *cur = sal;

  for(size_t i = 0; i < sigalgs_len; i++)
  {
    sigalgs[i] = pki_of_tls(cur->hd.tag);
    cur = cur->tl;
  }
  FStar_Pervasives_Native_option__K___uint64_t_TLSConstants_signatureScheme res;
  void* chain = s->select(s->cb_state, sni.data, sni.length, sigalgs, sigalgs_len, &selected);

  if(chain == NULL) {
    res.tag = FStar_Pervasives_Native_None;
  } else {
    K___uint64_t_TLSConstants_signatureScheme sig;
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
  char *buffer = KRML_HOST_MALLOC(MAX_CHAIN_LEN);
  size_t r = s->format(s->cb_state, (const void *)(size_t)cert, buffer);
  FStar_Bytes_bytes b = {.length = r, .data = buffer};
  return FFI_ffiSplitChain(b);
}


static FStar_Pervasives_Native_option__FStar_Bytes_bytes wrapped_sign(
  FStar_Dyn_dyn cbs, FStar_Dyn_dyn st, uint64_t cert,
  TLSConstants_signatureScheme sa, FStar_Bytes_bytes tbs)
{
  wrapped_cert_cb* s = (wrapped_cert_cb*)cbs;
  char* sig = KRML_HOST_MALLOC(MAX_SIGNATURE_LEN);
  FStar_Pervasives_Native_option__FStar_Bytes_bytes res = {.tag = FStar_Pervasives_Native_None};
  mitls_signature_scheme sigalg = pki_of_tls(sa.tag);

  size_t slen = s->sign(s->cb_state, (const void *)(size_t)cert, sigalg, tbs.data, tbs.length, sig);

  if(slen > 0) {
    res.tag = FStar_Pervasives_Native_Some;
    res.v = (FStar_Bytes_bytes){.length = slen, .data = sig};
  }

  return res;
}

static bool wrapped_verify(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st,
  Prims_list__FStar_Bytes_bytes *certs, TLSConstants_signatureScheme sa,
  FStar_Bytes_bytes tbs, FStar_Bytes_bytes sig)
{
  wrapped_cert_cb* s = (wrapped_cert_cb*)cbs;
  FStar_Bytes_bytes chain = Cert_certificateListBytes(certs);
  mitls_signature_scheme sigalg = pki_of_tls(sa.tag);

  // ADL the extra copy is a workaround for the const of sig.data
  // FIXME should probably add a const in mitlsffi.h
  char *sig0 = KRML_HOST_MALLOC(sig.length);
  if(sig0 == NULL) return 0;
  memcpy(sig0, sig.data, sig.length);

  int r = (s->verify(s->cb_state, chain.data, chain.length, sigalg,
    tbs.data, tbs.length, sig0, sig.length) != 0);

  KRML_HOST_FREE(sig0);
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
  return 1;
}

int MITLS_CALLCONV FFI_mitls_configure_early_data(/* in */ mitls_state *state, uint32_t max_early_data)
{
    ENTER_HEAP_REGION(state->rgn);
    state->cfg = FFI_ffiSetEarlyData(state->cfg, max_early_data);
    LEAVE_HEAP_REGION();
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

void MITLS_CALLCONV FFI_mitls_free_packet(/* in */ mitls_state *state, void *packet)
{
    ENTER_HEAP_REGION(state->rgn);
    KRML_HOST_FREE(packet);
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
   ENTER_HEAP_REGION(state->rgn);
   LOCK_MUTEX(&lock);

   wrapped_transport_cb* tcb = KRML_HOST_MALLOC(sizeof(wrapped_transport_cb));
   Prims_list__FStar_Bytes_bytes *psks = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));

   tcb->send_recv_ctx = send_recv_ctx;
   tcb->send = psend;
   tcb->recv = precv;
   psks->tag = Prims_Nil;

    // No psks this FFI_connect() call
    K___Connection_connection_Prims_int result = FFI_connect((FStar_Dyn_dyn)tcb, wrapped_send, wrapped_recv, state->cfg, psks);
    state->cxn = result.fst;

    UNLOCK_MUTEX(&lock);
    LEAVE_HEAP_REGION();
    return (result.snd == 0);
}

int MITLS_CALLCONV FFI_mitls_resume(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket)
{
    ENTER_HEAP_REGION(state->rgn);
    LOCK_MUTEX(&lock);
    wrapped_transport_cb* tcb = KRML_HOST_MALLOC(sizeof(wrapped_transport_cb));
    tcb->send_recv_ctx = send_recv_ctx;
    tcb->send = psend;
    tcb->recv = precv;

    Prims_list__FStar_Bytes_bytes *head;
    head = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));
    if (!head) {
        UNLOCK_MUTEX(&lock);
        return 1;
    }

    if (ticket->ticket_len) {

        Prims_list__FStar_Bytes_bytes *tail = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));
        Prims_list__FStar_Bytes_bytes *nil = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));
        if (!tail || !nil) {
            UNLOCK_MUTEX(&lock);
            KRML_HOST_FREE(head);
            KRML_HOST_FREE(tail);
            LEAVE_HEAP_REGION();
            return 1;
        }

        if (!MakeFStar_Bytes_bytes(&head->hd, ticket->ticket, ticket->ticket_len)) {
            UNLOCK_MUTEX(&lock);
            KRML_HOST_FREE(head);
            KRML_HOST_FREE(tail);
            LEAVE_HEAP_REGION();
            return 1;
        }
        if (!MakeFStar_Bytes_bytes(&tail->hd, ticket->session, ticket->session_len)) {
            UNLOCK_MUTEX(&lock);
            KRML_HOST_FREE((char*)head->hd.data);
            KRML_HOST_FREE(tail);
            KRML_HOST_FREE(head);
            LEAVE_HEAP_REGION();
            return 1;
        }

        head->tag = Prims_Cons;
        head->tl = tail;
        tail->tag = Prims_Cons;
        tail->tl = nil;
        nil->tag = Prims_Nil;
    } else {
        head->tag = Prims_Nil;
    }

    K___Connection_connection_Prims_int result = FFI_connect((FStar_Dyn_dyn)tcb, wrapped_send, wrapped_recv, state->cfg, head);
    state->cxn = result.fst;
    UNLOCK_MUTEX(&lock);
    LEAVE_HEAP_REGION();

    return (result.snd == 0);
}

// Called by the host server app, after a client has connected to a socket and the calling server has accepted the TCP connection.
int MITLS_CALLCONV FFI_mitls_accept_connected(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state)
{
    ENTER_HEAP_REGION(state->rgn);
    LOCK_MUTEX(&lock);

    wrapped_transport_cb* tcb = KRML_HOST_MALLOC(sizeof(wrapped_transport_cb));
    tcb->send_recv_ctx = send_recv_ctx;
    tcb->send = psend;
    tcb->recv = precv;

    K___Connection_connection_Prims_int ret = FFI_ffiAcceptConnected((FStar_Dyn_dyn)tcb, wrapped_send, wrapped_recv, state->cfg);
    state->cxn = ret.fst;

    UNLOCK_MUTEX(&lock);
    LEAVE_HEAP_REGION();
    return (ret.snd == 0) ? 1 : 0; // return success (1) if ret.snd is 0.
}

// Called by the host app transmit a packet
int MITLS_CALLCONV FFI_mitls_send(/* in */ mitls_state *state, const void* buffer, size_t buffer_size)
{
    int ret;

    ENTER_HEAP_REGION(state->rgn);
    LOCK_MUTEX(&lock);
    ret = FFI_ffiSend(state->cxn, (FStar_Bytes_bytes){.data = buffer, .length = buffer_size});
    UNLOCK_MUTEX(&lock);
    LEAVE_HEAP_REGION();

    return 1;
}

// Called by the host app to receive a packet
void * MITLS_CALLCONV FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size)
{
    void *p;
    *packet_size = 0;

    ENTER_HEAP_REGION(state->rgn);
    LOCK_MUTEX(&lock);
    FStar_Bytes_bytes ret = FFI_ffiRecv(state->cxn);
    UNLOCK_MUTEX(&lock);

    if(!ret.length) {
        LEAVE_HEAP_REGION();
        return NULL;
    }
    p = KRML_HOST_MALLOC(ret.length);
    if(p != NULL) {
        memcpy(p, ret.data, ret.length);
    }
    LEAVE_HEAP_REGION();
    return p;
}

static int get_exporter(Connection_connection cxn, int early, /* out */ mitls_secret *secret)
{
  FStar_Pervasives_Native_option__K___Hashing_Spec_alg_CryptoTypes_aead_cipher_FStar_Bytes_bytes ret;

  ret = FFI_ffiGetExporter(cxn, (early) ? true : false);
  if (ret.tag != FStar_Pervasives_Native_Some) {
     KRML_HOST_PRINTF("the requested secret is not yet available");
     return 0;
  }
  secret->hash = ret.v.fst;
  secret->ae = ret.v.snd;
  size_t len=ret.v.thd.length;
  assert(len <= sizeof(secret->secret));
  memcpy(secret->secret, ret.v.thd.data, len);
  return 1;
}


int MITLS_CALLCONV FFI_mitls_get_exporter(/* in */ mitls_state *state, int early, /* out */ mitls_secret *secret)
{
  ENTER_HEAP_REGION(state->rgn);
  int ret = get_exporter(state->cxn, early, secret);
  LEAVE_HEAP_REGION();
  return ret;
}

void *MITLS_CALLCONV FFI_mitls_get_cert(/* in */ mitls_state *state, /* out */ size_t *cert_size)
{
    ENTER_HEAP_REGION(state->rgn);
    FStar_Bytes_bytes ret = FFI_getCert(state->cxn);
    *cert_size = ret.length;
    LEAVE_HEAP_REGION();
    return (void*)ret.data; // bugbug: casting away const
}

/*************************************************************************
* QUIC FFI
**************************************************************************/

typedef struct quic_state {
   HEAP_REGION rgn;
   int is_server;
   char* in_buffer;
   uint32_t in_buffer_size;
   uint32_t in_buffer_used;
   char* out_buffer;
   uint32_t out_buffer_size;
   uint32_t out_buffer_used;
   TLSConstants_config cfg;
   Connection_connection cxn;
} quic_state;

int32_t quic_send(void* ctx, uint8_t* buffer, uint32_t buffer_size)
{
  quic_state* s = (quic_state*)ctx;

  if(!s->out_buffer) {
    KRML_HOST_PRINTF("QUIC_send(): out_buffer is NULL");
    return -1;
  }

  // ADL FIXME better error management
  if(buffer_size <= s->out_buffer_size - s->out_buffer_used) {
    memcpy(s->out_buffer + s->out_buffer_used, buffer, buffer_size);
    s->out_buffer_used += buffer_size;
    return buffer_size;
  }

  KRML_HOST_PRINTF("QUIC_send():  Insufficient space in out_buffer");
  return -1;
}

int32_t quic_recv(void* ctx, uint8_t* buffer, uint32_t len)
{
  quic_state* s = (quic_state*)ctx;

  if(!s->in_buffer || buffer == NULL) {
    KRML_HOST_PRINTF("QUIC_recv():  in_buffer or buffer is NULL");
    return -1;
  }

  if(len > s->in_buffer_size - s->in_buffer_used)
    len = s->in_buffer_size - s->in_buffer_used; // may be 0

  memcpy(buffer, s->in_buffer + s->in_buffer_used, len);

  s->in_buffer_used += len;
  return len;
}

#ifdef _KERNEL_MODE
typedef struct {
    quic_config *cfg;
    quic_state* st;
} quic_create_state;

void quic_create_callout(PVOID Parameter)
{
    quic_create_state *s = (quic_create_state*)Parameter;

    if(s->cfg->is_server) {
      s->st->cxn = QUIC_ffiAcceptConnected(s->st, quic_send, quic_recv, s->st->cfg);
    } else {
      FStar_Pervasives_Native_option__K___FStar_Bytes_bytes_FStar_Bytes_bytes ticket;

      if(s->cfg->server_ticket && s->cfg->server_ticket->ticket_len > 0) {
          ticket.tag = FStar_Pervasives_Native_Some;

          // BUGBUG: Handle OOM
          MakeFStar_Bytes_bytes(&ticket.v.fst, s->cfg->server_ticket->ticket, s->cfg->server_ticket->ticket_len);
          MakeFStar_Bytes_bytes(&ticket.v.snd, s->cfg->server_ticket->session, s->cfg->server_ticket->session_len);
      }
      else {
          ticket.tag = FStar_Pervasives_Native_None;
      }

      // Protect the write to the PSK table (WIP)
      LOCK_MUTEX(&lock);
      s->st->cxn = QUIC_ffiConnect((FStar_Dyn_dyn)s->st, quic_send, quic_recv, s->st->cfg, ticket);
      UNLOCK_MUTEX(&lock);
    }
}
#endif

int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg)
{
    *state = NULL;
    HEAP_REGION rgn;
    CREATE_HEAP_REGION(&rgn);
    if (!VALID_HEAP_REGION(rgn)) {
        return 0; // out of memory
    }
    quic_state* st = KRML_HOST_MALLOC(sizeof(quic_state));

    if (!st) {
      DESTROY_HEAP_REGION(rgn);
      return 0;
    }

    memset(st, 0, sizeof(*st));
    st->is_server = cfg->is_server;

    Prims_string host_name = CopyPrimsString(cfg->host_name != NULL ? cfg->host_name : "");
    if (host_name == NULL) {
        KRML_HOST_FREE(st);
        DESTROY_HEAP_REGION(rgn);
        return 0; // failure
    }

    st->cfg = QUIC_ffiConfig((FStar_Bytes_bytes){.data=host_name,.length=strlen(host_name)});

    if (cfg->cipher_suites) {
       Prims_string str = CopyPrimsString(cfg->cipher_suites);
       // BUGBUG: Handle OOM
       st->cfg = FFI_ffiSetCipherSuites(st->cfg, str);
    }

    if (cfg->named_groups) {
       Prims_string str = CopyPrimsString(cfg->named_groups);
       // BUGBUG: Handle OOM
       st->cfg = FFI_ffiSetNamedGroups(st->cfg, str);
    }

    if (cfg->signature_algorithms) {
       Prims_string str = CopyPrimsString(cfg->signature_algorithms);
       // BUGBUG: Handle OOM
       st->cfg = FFI_ffiSetSignatureAlgorithms(st->cfg, str);
    }

    if (cfg->alpn) {
       Prims_string str = CopyPrimsString(cfg->alpn);
       // BUGBUG: Handle OOM
       st->cfg = FFI_ffiSetALPN(st->cfg, str);
    }

    if(cfg->ticket_enc_alg && cfg->ticket_key) {
        FStar_Bytes_bytes key;
        bool b = MakeFStar_Bytes_bytes(&key, cfg->ticket_key, cfg->ticket_key_len);
        LOCK_MUTEX(&lock);
        if(b) b = FFI_ffiSetTicketKey(cfg->ticket_enc_alg, key);
        UNLOCK_MUTEX(&lock);
        if (!b) {
            KRML_HOST_FREE(st);
            DESTROY_HEAP_REGION(rgn);
            return 0; // failure
        }
    }

    if (cfg->enable_0rtt) {
       st->cfg = FFI_ffiSetEarlyData(st->cfg, 0xffffffff);
    }

    if (cfg->ticket_callback) {
      wrapped_ticket_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_ticket_cb));
      cbs->cb_state = cfg->callback_state;
      cbs->cb = cfg->ticket_callback;
      st->cfg = FFI_ffiSetTicketCallback(st->cfg, (void*)cbs, ticket_cb_proxy);
    }

    if (cfg->nego_callback) {
      wrapped_nego_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_nego_cb));
      cbs->cb_state = cfg->callback_state;
      cbs->cb = cfg->nego_callback;
      st->cfg = FFI_ffiSetNegoCallback(st->cfg, (void*)cbs, nego_cb_proxy);
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

      st->cfg = FFI_ffiSetCertCallbacks(st->cfg, cb);
    }

#ifdef _KERNEL_MODE
    // A call to QUIC_ffiConnect() may consume 0x2400 bytes.
    quic_create_state s = {.cfg = cfg, .st = st };
    NTSTATUS status = KeExpandKernelStackAndCallout(quic_create_callout, &s, MAXIMUM_EXPANSION_SIZE);
    if (!NT_SUCCESS(status)) {
        KRML_HOST_PRINTF("KeExpandKernelCallstackAndCallout for quic_create_callout failed st=%x", status);
        LEAVE_HEAP_REGION();
        return 0;
    }
#else
    if(cfg->is_server) {
      st->cxn = QUIC_ffiAcceptConnected(st, quic_send, quic_recv, st->cfg);
    } else {
      FStar_Pervasives_Native_option__K___FStar_Bytes_bytes_FStar_Bytes_bytes ticket;

      if(cfg->server_ticket && cfg->server_ticket->ticket_len > 0) {
          ticket.tag = FStar_Pervasives_Native_Some;

          // BUGBUG: Handle OOM
          MakeFStar_Bytes_bytes(&ticket.v.fst, cfg->server_ticket->ticket, cfg->server_ticket->ticket_len);
          MakeFStar_Bytes_bytes(&ticket.v.snd, cfg->server_ticket->session, cfg->server_ticket->session_len);
      }
      else {
          ticket.tag = FStar_Pervasives_Native_None;
      }

      // Protect the write to the PSK table (WIP)
      LOCK_MUTEX(&lock);
      st->cxn = QUIC_ffiConnect((FStar_Dyn_dyn)st, quic_send, quic_recv, st->cfg, ticket);
      UNLOCK_MUTEX(&lock);
    }
#endif

    LEAVE_HEAP_REGION();
    st->rgn = rgn;
    *state = st;
    return 1;
}

#ifdef _KERNEL_MODE
typedef struct {
    quic_state *state;
    QUIC_result r;
} quic_process_state;

VOID quic_process_callout(PVOID Parameter)
{
    quic_process_state *s = (quic_process_state*)Parameter;

    s->r = QUIC_recv(s->state->cxn);
}
#endif

quic_result MITLS_CALLCONV FFI_mitls_quic_process(
  /* in */ quic_state *state,
  /*in*/ char* inBuf,
  /*inout*/ size_t *pInBufLen,
  /*out*/ char *outBuf,
  /*inout*/ size_t *pOutBufLen)
{
    quic_result ret = TLS_error_other;
    ENTER_HEAP_REGION(state->rgn);
    LOCK_MUTEX(&lock);

    // Update the buffers for the QUIC_* callbacks
    state->in_buffer = inBuf;
    state->in_buffer_used = 0;
    state->in_buffer_size = *pInBufLen;
    state->out_buffer = outBuf;
    state->out_buffer_used = 0;
    state->out_buffer_size = *pOutBufLen;

#ifdef _KERNEL_MODE
    // A call to QUIC_recv() may consume 0x4b00 bytes.
    quic_process_state s = {.state = state, .r = TLS_error_other };
    NTSTATUS status = KeExpandKernelStackAndCallout(quic_process_callout, &s, MAXIMUM_EXPANSION_SIZE);
    QUIC_result r = s.r;
    if (!NT_SUCCESS(status)) {
        KRML_HOST_PRINTF("KeExpandKernelCallstackAndCallout for quic_process_callout failed st=%x", status);
        r.code = TLS_error_other;
    }
#else
    QUIC_result r = QUIC_recv(state->cxn);
#endif

    if ((int)r.code <= (int)TLS_server_complete) {
        ret = (quic_result) r.code;
    }
    // BUGBUG: the r.error value is currently discarded.

    *pInBufLen = state->in_buffer_used;
    *pOutBufLen = state->out_buffer_used;

    UNLOCK_MUTEX(&lock);
    LEAVE_HEAP_REGION();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_quic_get_exporter(
  /* in */ quic_state *state,
  int early,
  quic_secret *secret)
{
  ENTER_HEAP_REGION(state->rgn);
  int ret = get_exporter(state->cxn, early, secret);
  LEAVE_HEAP_REGION();
  return ret;
}

void MITLS_CALLCONV FFI_mitls_quic_free(quic_state *state)
{
    HEAP_REGION rgn = state->rgn;
    ENTER_HEAP_REGION(state->rgn);
    KRML_HOST_FREE(state);
    LEAVE_HEAP_REGION();
    DESTROY_HEAP_REGION(rgn);
}

int MITLS_CALLCONV FFI_mitls_get_transport_parameters(const char *cexts, size_t cexts_len, char **qtp, size_t *qtp_len)
{
  FStar_Bytes_bytes b = {.data = cexts, .length = cexts_len};
  FStar_Pervasives_Native_option__FStar_Bytes_bytes ob = QUIC_get_transport_parameters(b);
  *qtp = NULL; *qtp_len = 0;

  if(ob.tag == FStar_Pervasives_Native_Some)
  {
    *qtp_len = ob.v.length;
    *qtp = KRML_HOST_MALLOC(*qtp_len);
    memcpy(*qtp, ob.v.data, *qtp_len);
    return 1;
  }
  return 0;
}

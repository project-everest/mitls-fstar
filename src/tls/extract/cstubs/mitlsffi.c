#include <memory.h>
#include <assert.h>
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
    extern void DbgPrint(const char *, ...);
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

#if LOG_TO_CHOICE
typedef void (*p_log)(const char *fmt, ...);
p_log g_LogPrint;
#endif

struct mitls_state {
  HEAP_REGION rgn;
  TLSConstants_config cfg;
  Connection_connection cxn;
};

static bool isRegistered;

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

//
// Initialize miTLS.
//
//  Called once ahead of using miTLS
//
//  Returns:  0 for error, nonzero for success
//
int MITLS_CALLCONV FFI_mitls_init(void)
{
  if (isRegistered) {
    return FFI_mitls_thread_register();
  }
#if IS_WINDOWS
  #ifdef _KERNEL_MODE
    ExInitializeFastMutex(&lock);
    #if LOG_TO_CHOICE
    g_LogPrint = DbgPrint;
    #endif
  #else
    InitializeCriticalSection(&lock);
    #if LOG_TO_CHOICE
    if (GetEnvironmentVariableA("MITLS_LOG", NULL, 0) == 0) {
        g_LogPrint = DbgPrint; // if not set, log to the debugger by default
    } else {
        g_LogPrint = printf;
    }
    #endif
  #endif
#else
  if (pthread_mutex_init(&lock, NULL) != 0) {
    return 0;
  }
  #if LOG_TO_CHOICE
  if (getenv("MITLS_LOG") == NULL) {
    g_LogPrint = NoPrintf; // default to no logging
  } else {
    g_LogPrint = printf;
  }
  #endif
#endif

  if (HeapRegionInitialize() == 0) {
      return 0;
  }
  kremlinit_globals();
  isRegistered = 1;
  return 1; // success
}

void MITLS_CALLCONV FFI_mitls_cleanup(void)
{
#if IS_WINDOWS
    #ifndef _KERNEL_MODE
    DeleteCriticalSection(&lock);
    #endif
#else
    pthread_mutex_destroy(&lock);
#endif
    HeapRegionCleanup();
    isRegistered = 0;
}

// Called by the host app to configure miTLS ahead of creating a connection
int MITLS_CALLCONV FFI_mitls_configure(mitls_state **state, const char *tls_version, const char *host_name, char **outmsg, char **errmsg)
{
    int ret;
    
    *state = NULL;
    *outmsg = NULL;
    *errmsg = NULL;

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
    
    FStar_Bytes_bytes key;
    bool b = MakeFStar_Bytes_bytes(&key, tk, klen);
    if(b) b = FFI_ffiSetTicketKey(alg, key);
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
  void* chain = s->select(s->cb_state, sni.data, sigalgs, sigalgs_len, &selected);

  if(chain == NULL) {
    res.tag = FStar_Pervasives_Native_None;
  } else {
    K___uint64_t_TLSConstants_signatureScheme sig;
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
  size_t r = s->format(s->cb_state, (const void *)cert, buffer);
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

  size_t slen = s->sign(s->cb_state, (const void *)cert, sigalg, tbs.data, tbs.length, sig);

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

void MITLS_CALLCONV FFI_mitls_free_msg(char *msg)
{
    // do nothing.  no msg is returned in the Kremlin build.
}

void MITLS_CALLCONV FFI_mitls_free_packet(void *packet)
{
    // bugbug: free the packet.
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
int MITLS_CALLCONV FFI_mitls_connect(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
   *outmsg = NULL;
   *errmsg = NULL;
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

int MITLS_CALLCONV FFI_mitls_resume(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket, /* out */ char **errmsg)
{
    *errmsg = NULL;
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
int MITLS_CALLCONV FFI_mitls_accept_connected(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    *outmsg = NULL;
    *errmsg = NULL;
    
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
int MITLS_CALLCONV FFI_mitls_send(/* in */ mitls_state *state, const void* buffer, size_t buffer_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    int ret;
    *outmsg = NULL;
    *errmsg = NULL;

    ENTER_HEAP_REGION(state->rgn);
    LOCK_MUTEX(&lock);
    ret = FFI_ffiSend(state->cxn, (FStar_Bytes_bytes){.data = buffer, .length = buffer_size});
    UNLOCK_MUTEX(&lock);
    LEAVE_HEAP_REGION();

    return 1;
}

// Called by the host app to receive a packet
void * MITLS_CALLCONV FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    void *p;
    *outmsg = NULL;
    *errmsg = NULL;
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

static int get_exporter(Connection_connection cxn, int early, /* out */ mitls_secret *secret, /* out */ char **errmsg)
{
  *errmsg = NULL;

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


int MITLS_CALLCONV FFI_mitls_get_exporter(/* in */ mitls_state *state, int early, /* out */ mitls_secret *secret, /* out */ char **errmsg)
{
  ENTER_HEAP_REGION(state->rgn);
  int ret = get_exporter(state->cxn, early, secret, errmsg);
  LEAVE_HEAP_REGION();
  return ret;
}

void *MITLS_CALLCONV FFI_mitls_get_cert(/* in */ mitls_state *state, /* out */ size_t *cert_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    *outmsg = NULL;
    *errmsg = NULL;

    ENTER_HEAP_REGION(state->rgn);
    FStar_Bytes_bytes ret = FFI_getCert(state->cxn);
    *cert_size = ret.length;
    LEAVE_HEAP_REGION();
    return (void*)ret.data; // bugbug: casting away const
}

// Register the calling thread, so it can call miTLS.  Returns 1 for success, 0 for error.
int MITLS_CALLCONV FFI_mitls_thread_register(void)
{
    return 1;
}

// Unregister the calling thread, so it can no longer call miTLS.  Returns 1 for success, 0 for error.
int MITLS_CALLCONV FFI_mitls_thread_unregister(void)
{
    return 1;
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

static void free_last_version_element(Prims_list__uint32_t *l)
{
    // Find the last element of the list
    Prims_list__uint32_t *prev = NULL;
    while (l->tl) {
        prev = l;
        l = l->tl;
    }
    // Set the prev pointer to NULL
    prev->tl = NULL;
    // Free the last element
    KRML_HOST_FREE(l);
}

static void free_version_list(Prims_list__uint32_t *l)
{
    if (l) {
        while (l->tl) {
            free_last_version_element(l);
        }
        KRML_HOST_FREE(l);
    }
}

static Prims_list__uint32_t *alloc_version_list(const uint32_t *list, size_t len)
{
  Prims_list__uint32_t *result = KRML_HOST_MALLOC(sizeof(Prims_list__uint32_t));

  if(result == NULL) return result;
  result->tag = FStar_Pervasives_Native_None;

  for(size_t i = 0; i < len; i++) {
    Prims_list__uint32_t *r = KRML_HOST_MALLOC(sizeof(Prims_list__uint32_t));
    if (r == NULL) {
        free_version_list(result);
        return NULL;
    }
    r->tag = FStar_Pervasives_Native_Some;
    r->hd = list[len - i - 1];
    r->tl = result;
    result = r;
  }

  return result;
}

int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg, /* out */ char **errmsg)
{
    *errmsg = NULL;
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

    FStar_Bytes_bytes qp;
    if (!MakeFStar_Bytes_bytes(&qp, cfg->qp.tp_data, cfg->qp.tp_len)) {
        KRML_HOST_FREE(st);
        DESTROY_HEAP_REGION(rgn);
        return 0; // failure
    }

    Prims_list__uint32_t *versions = alloc_version_list(cfg->supported_versions, cfg->supported_versions_len);
    if (versions == NULL) {
        KRML_HOST_FREE((char*)qp.data);
        KRML_HOST_FREE(st);
        DESTROY_HEAP_REGION(rgn);
        return 0; // failure
    }

    Prims_string host_name = CopyPrimsString(cfg->host_name != NULL ? cfg->host_name : "");
    if (host_name == NULL) {
        KRML_HOST_FREE((char*)qp.data);
        KRML_HOST_FREE(st);
        DESTROY_HEAP_REGION(rgn);
        return 0; // failure
    }

    st->cfg = QUIC_ffiConfig(qp, versions, (FStar_Bytes_bytes){.data=host_name,.length=strlen(host_name)});

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
        if(b) b = FFI_ffiSetTicketKey(cfg->ticket_enc_alg, key);
        if (!b) {
            KRML_HOST_FREE((char*)qp.data);
            KRML_HOST_FREE(st);
            DESTROY_HEAP_REGION(rgn);
            return 0; // failure
        }
    }

    if (cfg->enable_0rtt) {
       st->cfg = FFI_ffiSetEarlyData(st->cfg, 0x01000000);
    }

    if (cfg->ticket_callback) {
      wrapped_ticket_cb *cbs = KRML_HOST_MALLOC(sizeof(wrapped_ticket_cb));
      cbs->cb_state = cfg->callback_state;
      cbs->cb = cfg->ticket_callback;
      st->cfg = FFI_ffiSetTicketCallback(st->cfg, (void*)cbs, ticket_cb_proxy);
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

      st->cxn = QUIC_ffiConnect((FStar_Dyn_dyn)st, quic_send, quic_recv, st->cfg, ticket);
    }

    LEAVE_HEAP_REGION();
    st->rgn = rgn;
    *state = st;
    return 1;
}

quic_result MITLS_CALLCONV FFI_mitls_quic_process(
  /* in */ quic_state *state,
  /*in*/ char* inBuf,
  /*inout*/ size_t *pInBufLen,
  /*out*/ char *outBuf,
  /*inout*/ size_t *pOutBufLen,
  /* out */ char **errmsg)
{
    *errmsg = NULL;
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

    QUIC_result r = QUIC_recv(state->cxn);

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

int MITLS_CALLCONV FFI_mitls_quic_get_peer_parameters(
  /* in */ quic_state *state,
  /* out */ uint32_t *ver,
  /* out */ quic_transport_parameters *qp,
  /* out */ char **errmsg)
{
  *errmsg = NULL;
  ENTER_HEAP_REGION(state->rgn);
  assert(qp);

  K___uint32_t_FStar_Bytes_bytes result = QUIC_get_peer_parameters(state->cxn);

  *ver = result.fst;
  if (qp->tp_data) {
      if (qp->tp_len < result.snd.length) {
          // Insufficient buffer
          KRML_HOST_PRINTF("tp_len is too small");
          LEAVE_HEAP_REGION();
          return 0;
      }
      memcpy((char*)qp->tp_data, result.snd.data, result.snd.length); // bugbug: casting away const
      qp->tp_len = result.snd.length;
  } else {
      qp->tp_len = result.snd.length;
  }
  LEAVE_HEAP_REGION();
  return 1;
}

int MITLS_CALLCONV FFI_mitls_quic_get_exporter(
  /* in */ quic_state *state,
  int early,
  quic_secret *secret,
  /* out */ char **errmsg)
{
  ENTER_HEAP_REGION(state->rgn);
  int ret = get_exporter(state->cxn, early, secret, errmsg);
  LEAVE_HEAP_REGION();
  return ret;
}

void MITLS_CALLCONV FFI_mitls_quic_free(quic_state *state)
{
    HEAP_REGION rgn = state->rgn;
    ENTER_HEAP_REGION(state->rgn);
    KRML_HOST_FREE(state);
    DESTROY_HEAP_REGION(rgn);
}

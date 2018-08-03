#include <stdio.h>
#include <memory.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/cdefs.h>
#if __APPLE__
#include <sys/errno.h> // OS/X only provides include/sys/errno.h
#else
#include <errno.h> // MinGW only provides include/errno.h
#include <malloc.h>
#endif
#include <caml/callback.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/threads.h>
#include <caml/printexc.h>
#include <caml/fail.h>
#include "mitlsffi.h"

#define MITLS_FFI_LIST \
  MITLS_FFI_ENTRY(Config) \
  MITLS_FFI_ENTRY(SetTicketKey) \
  MITLS_FFI_ENTRY(SetSealingKey) \
  MITLS_FFI_ENTRY(SetCipherSuites) \
  MITLS_FFI_ENTRY(SetSignatureAlgorithms) \
  MITLS_FFI_ENTRY(SetNamedGroups) \
  MITLS_FFI_ENTRY(SetALPN) \
  MITLS_FFI_ENTRY(SetEarlyData) \
  MITLS_FFI_ENTRY(SetTicketCallback) \
  MITLS_FFI_ENTRY(SetCertCallbacks) \
  MITLS_FFI_ENTRY(Connect) \
  MITLS_FFI_ENTRY(AcceptConnected) \
  MITLS_FFI_ENTRY(Send) \
  MITLS_FFI_ENTRY(Recv) \
  MITLS_FFI_ENTRY(GetCert) \
  MITLS_FFI_ENTRY(GetExporter) \
  MITLS_FFI_ENTRY(QuicConfig) \
  MITLS_FFI_ENTRY(QuicCreateClient) \
  MITLS_FFI_ENTRY(QuicCreateServer) \
  MITLS_FFI_ENTRY(QuicProcess)
  //MITLS_FFI_ENTRY(QuicGetPeerParameters)
  //MITLS_FFI_ENTRY(TicketCallback)
  //MITLS_FFI_ENTRY(CertSelectCallback)
  //MITLS_FFI_ENTRY(CertFormatCallback)
  //MITLS_FFI_ENTRY(CertSignCallback)
  //MITLS_FFI_ENTRY(CertVerifyCallback)

// Pointers to ML code.  Initialized in FFI_mitls_init().  Invoke via caml_callback()
#define MITLS_FFI_ENTRY(x) value* g_mitls_FFI_##x;
MITLS_FFI_LIST
#undef MITLS_FFI_ENTRY

// We store C pointers in garbage-collected int64, which
// is guaranteed to hold 64 bits (unlike int which holds 63 at best)
_Static_assert(sizeof(size_t) <= 8, "OCaml int64 cannot hold a C pointer on this platform");
#define PtrToValue(p) caml_copy_int64((size_t)p)
#define ValueToPtr(v) (void*)(Int64_val(v))

#define Val_none Val_int(0)
#define Some_val(v) Field(v,0)

static value Val_some(value mlvalue) {
    CAMLparam1(mlvalue);
    CAMLlocal1(aout);

    aout = caml_alloc(1, 0);
    Store_field(aout, 0, mlvalue);

    CAMLreturn(aout);
}

typedef struct mitls_state {
    value fstar_state;    // a GC root representing an F*-side state object
} mitls_state;

static int isRegistered;

// A default print callback that logs to stdout
void MITLS_CALLCONV default_trace(const char *msg)
{
    printf("%s\n", msg);
}

static pfn_mitls_trace_callback trace_callback = default_trace;

//
// Hosts may provide a callback function for debug tracing.
//
void MITLS_CALLCONV FFI_mitls_set_trace_callback(pfn_mitls_trace_callback cb)
{
    trace_callback = cb;
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
        caml_c_thread_register();
        return 1;
    }

    char *Argv[2];
    char empty[2] = {0, 0};

    // Build a stub argv[] to satisfy caml_Startup()
    Argv[0] = empty;
    Argv[1] = NULL;

    // Initialize the OCaml runtime
    caml_startup(Argv);

    // Bind to functions registered via Callback.register from ML
#define MITLS_FFI_ENTRY(x) \
    g_mitls_FFI_##x = caml_named_value("MITLS_FFI_" # x); \
    if (!g_mitls_FFI_##x) { \
        return 0; \
    }
 MITLS_FFI_LIST
 #undef MITLS_FFI_ENTRY

    // On return from caml_startup(), this thread continues to own
    // the OCaml global runtime lock as if it was running OCaml code.
    // Release it, so other threads can call into OCaml.
    caml_release_runtime_system();

    isRegistered = 1;

    return 1; // success
}

void MITLS_CALLCONV FFI_mitls_cleanup(void)
{
    // Nothing to do.  The OCaml runtime has no graceful shutdown.
}

static void report_error(const char *msg)
{
    if (msg == NULL) {
        return;
    }
    (*default_trace)(msg);
}

// Input:  v - an OCaml exception
// Return:
//         nothing
static void report_caml_exception(value v)
{
    char * msg = caml_format_exception(Extract_exception(v));
    report_error(msg);
    free(msg);
}

// The OCaml runtime system must be acquired before calling this
static int FFI_mitls_configure_caml(mitls_state **state, const char *tls_version, const char *host_name)
{
    CAMLparam0();
    CAMLlocal3(config, version, host);
    int ret = 0;

    version = caml_copy_string(tls_version);
    host = caml_copy_string(host_name);
    config = caml_callback2_exn(*g_mitls_FFI_Config, version, host);
    if (Is_exception_result(config)) {
        report_caml_exception(config);
    } else {
        mitls_state * s;

        // Allocate space on the heap, to store an OCaml value
        s = (mitls_state*)malloc(sizeof(mitls_state));
        if (s) {
            // Tell the OCaml GC about the heap address, so it is treated
            // as a GC root, keeping the config object live.
            s->fstar_state = config;
            caml_register_generational_global_root(&s->fstar_state);
            *state = s;
            ret = 1;
        }
    }

    CAMLreturnT(int, ret);
}

// Called by the host app to configure miTLS ahead of creating a connection
int MITLS_CALLCONV FFI_mitls_configure(mitls_state **state, const char *tls_version, const char *host_name)
{
    int ret;

    *state = NULL;

    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = FFI_mitls_configure_caml(state, tls_version, host_name);
    caml_release_runtime_system();
    caml_c_thread_unregister();

    return ret;
}

// Helper routine to set a string-based value in the config object
// The OCaml runtime system must be acquired before calling this
static int configure_common_caml(/* in */ mitls_state *state, const char * str, value* function)
{
    CAMLparam0();
    CAMLlocal2(config, camlvalue);
    int ret = 0;

    camlvalue = caml_copy_string(str);
    config = caml_callback2_exn(*function, state->fstar_state, camlvalue);
    if (Is_exception_result(config)) {
        report_caml_exception(config);
    } else {
        state->fstar_state = config;
        ret = 1;
    }


    CAMLreturnT(int,ret);
}

// The OCaml runtime system must be acquired before calling this
static int ocaml_set_global_key(int sealing, const char *alg, const unsigned char *ticketkey, size_t klen)
{
    int ret;
    value *setter = sealing ? g_mitls_FFI_SetSealingKey : g_mitls_FFI_SetTicketKey;
    CAMLparam0();
    CAMLlocal3(r, a, tkey);
    tkey = caml_alloc_string(klen);
    memcpy(String_val(tkey), ticketkey, klen);

    a = caml_copy_string(alg);
    r = caml_callback2_exn(*setter, a, tkey);

    if (Is_exception_result(r)) {
      report_caml_exception(r);
      ret = 0;
    } else {
      ret = Int_val(r);
    }
    CAMLreturnT(int, ret);
}

int MITLS_CALLCONV FFI_mitls_set_ticket_key(const char *alg, const unsigned char *tk, size_t klen)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = ocaml_set_global_key(0, alg, tk, klen);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_set_sealing_key(const char *alg, const unsigned char *tk, size_t klen)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = ocaml_set_global_key(1, alg, tk, klen);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char * cs)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, cs, g_mitls_FFI_SetCipherSuites);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char * sa)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, sa, g_mitls_FFI_SetSignatureAlgorithms);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char * ng)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, ng, g_mitls_FFI_SetNamedGroups);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

static value alpn_list_of_array(const mitls_alpn *alpn, size_t alpn_count)
{
  CAMLparam0();
  CAMLlocal3(apl, cur, str);
  apl = Val_int(0);

  for(int i = (alpn_count & 255) - 1; i >= 0; i--)
  {
    cur = caml_alloc(2, 0);
    str = caml_alloc_string(alpn[i].alpn_len);
    memcpy(String_val(str), alpn[i].alpn, alpn[i].alpn_len);
    Field(cur, 0) = str;
    Field(cur, 1) = apl;
    apl = cur;
  }

  CAMLreturn(apl);
}

static int ocaml_set_alpn(/* in */ mitls_state *state, const mitls_alpn *alpn, size_t alpn_count)
{
    CAMLparam0();
    CAMLlocal2(config, camlvalue);
    int ret = 0;

    camlvalue = alpn_list_of_array(alpn, alpn_count);
    config = caml_callback2_exn(*g_mitls_FFI_SetALPN, state->fstar_state, camlvalue);
    if (Is_exception_result(config)) {
        report_caml_exception(config);
    } else {
        state->fstar_state = config;
        ret = 1;
    }

    CAMLreturnT(int,ret);
}

int MITLS_CALLCONV FFI_mitls_configure_alpn(/* in */ mitls_state *state, const mitls_alpn *alpn, size_t alpn_count)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = ocaml_set_alpn(state, alpn, alpn_count);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

// Called by Handshake when receiving a new ticket (1.3)
// and a ticket callback was configured in the FFI
CAMLprim value ocaml_ticket_cb(value st, value fp, value sni, value ticket, value session)
{
  CAMLparam5(st, fp, sni, ticket, session);
  pfn_FFI_ticket_cb cb = (pfn_FFI_ticket_cb)ValueToPtr(fp);
  mitls_ticket t;
  t.ticket_len = caml_string_length(ticket);
  t.session_len = caml_string_length(session);
  t.ticket = (unsigned char*)String_val(ticket);
  t.session = (unsigned char*)String_val(session);
  cb((void*)ValueToPtr(st), String_val(sni), &t);
  CAMLreturn(Val_unit);
}

static int ocaml_set_ticket_callback(/* in */ mitls_state *state, void *cb_state, pfn_FFI_ticket_cb ticket_cb)
{
    CAMLparam0();
    CAMLlocal4(config, cb, cbs, ocb);
    int ret = 0;

#if 0    // bugbug: ticket callbacks are no longer present in the OCaml build
    cb = PtrToValue(ticket_cb); // Address of the C callback
    cbs = PtrToValue(cb_state); // Callback state

    // This is a partial application of ocaml_ticket_cb, defined above
    // ocb is a string -> string -> string -> unit function that represents calling ticket_cb from OCaml
    ocb = caml_callback2_exn(*g_mitls_FFI_TicketCallback, cbs, cb);

    if (!Is_exception_result(ocb)) {
      config = caml_callback2_exn(*g_mitls_FFI_SetTicketCallback, state->fstar_state, ocb);
      if (!Is_exception_result(config)) {
        state->fstar_state = config;
        ret = 1;
      }
    }
#endif

    CAMLreturnT(int, ret);
}

int MITLS_CALLCONV FFI_mitls_configure_ticket_callback(/* in */ mitls_state *state, void *cb_state, pfn_FFI_ticket_cb ticket_cb)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = ocaml_set_ticket_callback(state, cb_state, ticket_cb);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

static int ocaml_set_cert_callbacks(/* in */ mitls_state *state, void *cb_state, mitls_cert_cb *cb)
{
    CAMLparam0();
    CAMLlocal3(config, cbs, ocb);
    CAMLlocal4(select, format, sign, verify);
    int ret = 0;

#if 0    // BUGBUG:  cert callbacks are no longer implemented
    cbs = PtrToValue(cb_state);

    // These are partial applications and won't raise an exception
    select = caml_callback2(*g_mitls_FFI_CertSelectCallback, cbs, PtrToValue(cb->select));
    format = caml_callback2(*g_mitls_FFI_CertFormatCallback, cbs, PtrToValue(cb->format));
    sign = caml_callback2(*g_mitls_FFI_CertSignCallback, cbs, PtrToValue(cb->sign));
    verify = caml_callback2(*g_mitls_FFI_CertVerifyCallback, cbs, PtrToValue(cb->verify));

    ocb = caml_alloc_tuple(9);
    Store_field(ocb, 0, cbs);
    Store_field(ocb, 1, PtrToValue(cb->select));
    Store_field(ocb, 2, PtrToValue(g_mitls_FFI_CertSelectCallback));

    Store_field(ocb, 3, PtrToValue(cb->format));
    Store_field(ocb, 4, PtrToValue(g_mitls_FFI_CertSelectCallback));

    Store_field(ocb, 5, PtrToValue(cb->format));
    Store_field(ocb, 6, PtrToValue(g_mitls_FFI_CertSignCallback));

    Store_field(ocb, 7, PtrToValue(cb->verify));
    Store_field(ocb, 8, PtrToValue(g_mitls_FFI_CertVerifyCallback));

    config = caml_callback2_exn(*g_mitls_FFI_SetCertCallbacks, state->fstar_state, ocb);
    if (!Is_exception_result(config)) {
      state->fstar_state = config;
      ret = 1;
    }
#endif

    CAMLreturnT(int, ret);
}

int MITLS_CALLCONV FFI_mitls_configure_cert_callbacks(/* in */ mitls_state *state, void *cb_state, mitls_cert_cb *cert_cb)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = ocaml_set_cert_callbacks(state, cb_state, cert_cb);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

// The OCaml runtime system must be acquired before calling this
static int configure_common_bool_caml(/* in */ mitls_state *state, value b, value* function)
{
    CAMLparam0();
    CAMLlocal2(config, camlvalue);
    int ret = 0;

    camlvalue = b;
    config = caml_callback2_exn(*function, state->fstar_state, camlvalue);
    if (Is_exception_result(config)) {
        report_caml_exception(config);
    } else {
        state->fstar_state = config;
        ret = 1;
    }

    CAMLreturnT(int,ret);
}

int MITLS_CALLCONV FFI_mitls_configure_early_data(/* in */ mitls_state *state, uint32_t max_early_data)
{
    int ret;
    value max_ed = Val_int(max_early_data);
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = configure_common_bool_caml(state, max_ed, g_mitls_FFI_SetEarlyData);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

// Called by the host app to free a mitls_state allocated by FFI_mitls_configure()
void MITLS_CALLCONV FFI_mitls_close(mitls_state *state)
{
    if (state) {
        caml_c_thread_register();
        caml_acquire_runtime_system();
        caml_remove_generational_global_root(&state->fstar_state);
        caml_release_runtime_system();
        caml_c_thread_unregister();
        state->fstar_state = 0;
        free(state);
    }
}

void MITLS_CALLCONV FFI_mitls_free(mitls_state *state, void* pv)
{
    // state is ignored in the OCaml build
    free(pv);
}

void * copypacket(value packet, /* out */ size_t *packet_size)
{
    void *p;
    mlsize_t size;

    size = caml_string_length(packet);
    p = malloc(size);
    if (p) {
        memcpy(p, String_val(packet), size);
        *packet_size = size;
    }
    return p;
}

static int FFI_mitls_connect_caml(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket)
{
    CAMLparam0();
    CAMLlocal4(result, tticket, session, oticket);
    int ret;

    // ticket: option (bytes * bytes)
    if(ticket->ticket_len > 0) {
      tticket = caml_alloc_string(ticket->ticket_len);
      memcpy(String_val(tticket), ticket->ticket, ticket->ticket_len);
      session = caml_alloc_string(ticket->session_len);
      memcpy(String_val(session), ticket->session, ticket->session_len);
      result = caml_alloc_tuple(2);
      Store_field(result, 0, tticket);
      Store_field(result, 1, session);

      oticket = caml_alloc(1, 0);
      Store_field(oticket, 0, result);
    }
    else {
      oticket = Val_none;
    }

    value args[] = {
      PtrToValue(send_recv_ctx),
      PtrToValue(psend),
      PtrToValue(precv),
      state->fstar_state,
      oticket
    };

    result = caml_callbackN_exn(*g_mitls_FFI_Connect, 5, args);
    if (Is_exception_result(result)) {
        report_caml_exception(result);
        ret = 0;
    } else {
        // Connect returns back (Connection.connection * int)
        value connection = Field(result, 0);
        ret = Int_val(Field(result, 1));
        if (ret == 0) {
            caml_modify_generational_global_root(&state->fstar_state, connection);
            ret = 1;
        } else {
            ret = 0;
        }
    }
    CAMLreturnT(int, ret);
}

// Called by the host app to create a TLS connection.
int MITLS_CALLCONV FFI_mitls_connect(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state)
{
    int ret;
    mitls_ticket ticket = {0};

    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = FFI_mitls_connect_caml(send_recv_ctx, psend, precv, state, &ticket);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_resume(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket)
{
    int ret;

    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = FFI_mitls_connect_caml(send_recv_ctx, psend, precv, state, ticket);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

static int FFI_mitls_accept_connected_caml(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state)
{
    CAMLparam0();
    CAMLlocal1(result);
    int ret;

    value args[] = {
      PtrToValue(send_recv_ctx),
      PtrToValue(psend),
      PtrToValue(precv),
      state->fstar_state
    };

    result = caml_callbackN_exn(*g_mitls_FFI_AcceptConnected, 4, args);
    if (Is_exception_result(result)) {
        report_caml_exception(result);
        ret = 0;
    } else {
        // AcceptConnected returns back (Connection.connection * int)
        value connection = Field(result, 0);
        ret = Int_val(Field(result, 1));
        if (ret == 0) {
            caml_modify_generational_global_root(&state->fstar_state, connection);
            ret = 1;
        } else {
            ret = 0;
        }
    }
    CAMLreturnT(int, ret);
}

// Called by the host server app, after a client has connected to a socket and the calling server has accepted the TCP connection.
int MITLS_CALLCONV FFI_mitls_accept_connected(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state)
{
    int ret;

    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = FFI_mitls_accept_connected_caml(send_recv_ctx, psend, precv, state);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}



static int FFI_mitls_send_caml(/* in */ mitls_state *state, const void* buffer, size_t buffer_size)
{
    CAMLparam0();
    CAMLlocal2(buffer_value, result);
    int ret;

    buffer_value = caml_alloc_string(buffer_size);
    memcpy(Bp_val(buffer_value), buffer, buffer_size);

    result = caml_callback2_exn(*g_mitls_FFI_Send, state->fstar_state, buffer_value);
    if (Is_exception_result(result)) {
        report_caml_exception(result);
        ret = 0;
    } else {
        ret = 1;
    }

    CAMLreturnT(int, ret);
}

// Called by the host app transmit a packet
int MITLS_CALLCONV FFI_mitls_send(/* in */ mitls_state *state, const unsigned char *buffer, size_t buffer_size)
{
    int ret;

    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = FFI_mitls_send_caml(state, buffer, buffer_size);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return ret;
}

static unsigned char *FFI_mitls_receive_caml(/* in */ mitls_state *state, /* out */ size_t *packet_size)
{
    CAMLparam0();
    CAMLlocal1(result);
    void *p = NULL;

    result = caml_callback_exn(*g_mitls_FFI_Recv, state->fstar_state);
    if (Is_exception_result(result)) {
        report_caml_exception(result);
        p = NULL;
    } else {
        // Return the plaintext data
        p = copypacket(result, packet_size);
    }

    CAMLreturnT(void*, p);
}

// Called by the host app to receive a packet
unsigned char *MITLS_CALLCONV FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size)
{
    void *p;

    caml_c_thread_register();
    caml_acquire_runtime_system();
    p = FFI_mitls_receive_caml(state, packet_size);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return p;
}

// The OCaml runtime system must be acquired before calling this
static int ocaml_get_exporter(
  /* in */ mitls_state *state,
  int early,
  mitls_secret *secret)
{
    CAMLparam0();
    CAMLlocal2(result, tmp);

    result = caml_callback2_exn(*g_mitls_FFI_GetExporter,
                                state->fstar_state,
                                early ? Val_true : Val_false);

    if (Is_exception_result(result)) {
        report_caml_exception(result);
        CAMLreturnT(int, 0);
    }

    // Secret not available
    if(result == Val_none)
    {
      report_error("the requested secret is not yet available\n");
      CAMLreturnT(int, 0);
    }

    result = Some_val(result);
    secret->hash = Int_val(Field(result, 0));
    secret->ae = Int_val(Field(result, 1));
    tmp = Field(result, 2);
    size_t len = caml_string_length(tmp);
    assert(len <= 64);
    memcpy(secret->secret, String_val(tmp), len);

    CAMLreturnT(int, 1);
}

int MITLS_CALLCONV FFI_mitls_get_exporter(/* in */ mitls_state *state, int early, /* out */ mitls_secret *secret)
{
  int ret;

  caml_c_thread_register();
  caml_acquire_runtime_system();
  ret = ocaml_get_exporter(state, early, secret);
  caml_release_runtime_system();
  caml_c_thread_unregister();
  return ret;
}

static void * FFI_mitls_get_cert_caml(/* in */ mitls_state *state, /* out */ size_t *cert_size)
{
    CAMLparam0();
    CAMLlocal1(result);
    void *p = NULL;

    result = caml_callback_exn(*g_mitls_FFI_GetCert, state->fstar_state);
    if (Is_exception_result(result)) {
        report_caml_exception(result);
        p = NULL;
    } else {
        // Return the certificate bytes
        p = copypacket(result, cert_size);
    }

    CAMLreturnT(void*, p);
}

void *MITLS_CALLCONV FFI_mitls_get_cert(/* in */ mitls_state *state, /* out */ size_t *cert_size)
{
    void *p;

    caml_c_thread_register();
    caml_acquire_runtime_system();
    p = FFI_mitls_get_cert_caml(state, cert_size);
    caml_release_runtime_system();
    caml_c_thread_unregister();
    return p;
}

/*************************************************************************
* QUIC FFI
**************************************************************************/

#if 0 // FIXME: update to draft 13 API

// ADL yikes!! can't we just expose the mitls_state to the callback??
#define CONTAINING_RECORD(address, type, field) ((type *)((char*)(address) - (size_t)(&((type *)0)->field)))

typedef struct quic_state {
   value fstar_state; // a GC root representing an F*-side state object
   int is_server;
   const unsigned char* in_buffer;
   size_t in_buffer_size;
   size_t in_buffer_used;
   unsigned char* out_buffer;
   size_t out_buffer_size;
   size_t out_buffer_used;
} quic_state;

 int QUIC_send(void *ctx, const void *buffer, size_t buffer_size)
 {
//   FILE *fp = fopen("send_log", "a");
//   fprintf(fp, "CALLBACK: send %u\n", buffer_size);
   quic_state* s = (quic_state*)ctx;
//   fprintf(fp, "Current %s state: IN=%u/%u OUT=%u/%u\n", s->is_server ? "server" : "client", s->in_buffer_used, s->in_buffer_size, s->out_buffer_used, s->out_buffer_size);
//   fclose(fp);
   if(!s->out_buffer)
   {
       report_error("QUIC_send():  out_buffer is NULL");
       return -1;
   }

   // ADL FIXME better error management
   if(buffer_size <= s->out_buffer_size - s->out_buffer_used)
   {
     memcpy(s->out_buffer + s->out_buffer_used, buffer, buffer_size);
     s->out_buffer_used += buffer_size;
     return buffer_size;
   }

   report_error("QUIC_send():  Insufficient space in out_buffer");
   return -1;
 }

 int QUIC_recv(void *ctx, void *buffer, size_t len)
 {
//   FILE *fp = fopen("recv_log", "a");
//   fprintf(fp, "CALLBACK: recv %u\n", len);
   quic_state* s = (quic_state*)ctx;
//   fprintf(fp, "Current %s state: IN=%u/%u OUT=%u/%u\n", s->is_server ? "server" : "client", s->in_buffer_used, s->in_buffer_size, s->out_buffer_used, s->out_buffer_size);
//   fclose(fp);

   if(!s->in_buffer || buffer == NULL)
   {
       report_error("QUIC_recv():  in_buffer or buffer is NULL");
       return -1;
   }

   if(len > s->in_buffer_size - s->in_buffer_used)
     len = s->in_buffer_size - s->in_buffer_used; // may be 0

   memcpy(buffer, s->in_buffer + s->in_buffer_used, len);
   s->in_buffer_used += len;
   return len;
 }

// The OCaml runtime system must be acquired before calling this
static int FFI_mitls_quic_create_caml(quic_state **st, quic_config *cfg)
{
    CAMLparam0();
    CAMLlocal4(result, host, others, versions);
    CAMLlocal3(tticket, session, oticket);

    *st = NULL;
    quic_state* state = malloc(sizeof(quic_state));
    if(!state) {
      report_error("failed to allocate QUIC state");
      CAMLreturnT(int, 0);
    }
    memset(state, 0, sizeof(*state));
    *st = state;

    state->is_server = cfg->is_server;

    if(cfg->host_name)
      host = caml_copy_string(cfg->host_name);
    else
      host = caml_alloc_string(0);

    result = caml_callback_exn(*g_mitls_FFI_QuicConfig, host);
    if (Is_exception_result(result)) {
      report_caml_exception(result);
      CAMLreturnT(int,0);
    }

    // config
    state->fstar_state = result;
    caml_register_generational_global_root(&state->fstar_state);
    mitls_state ms = {.fstar_state = result};

    if(!configure_common_bool_caml(&ms, Val_int(0xFFFFFFFF), g_mitls_FFI_SetEarlyData))
    {
      report_error("FFI_mitls_quic_create_caml: can't enable early_data");
      CAMLreturnT(int, 0);
    }

    if(cfg->cipher_suites) {
       if(!configure_common_caml(&ms, cfg->cipher_suites, g_mitls_FFI_SetCipherSuites))
       {
         report_error("FFI_mitls_quic_create_caml: cipher suite list");
         CAMLreturnT(int, 0);
       }
    }

    if(cfg->named_groups) {
       if(!configure_common_caml(&ms, cfg->named_groups, g_mitls_FFI_SetNamedGroups))
       {
         report_error("FFI_mitls_quic_create_caml: supported groups list");
         CAMLreturnT(int, 0);
       }
    }

    if(cfg->signature_algorithms) {
       if(!configure_common_caml(&ms, cfg->signature_algorithms, g_mitls_FFI_SetSignatureAlgorithms))
       {
         report_error("FFI_mitls_quic_create_caml: signature algorithms list");
         CAMLreturnT(int, 0);
       }
    }

    if(cfg->alpn && cfg->alpn_count) {
      if(!ocaml_set_alpn(&ms, cfg->alpn, cfg->alpn_count))
      {
        report_error("FFI_mitls_quic_create_caml: failed to set application-level protocols");
        CAMLreturnT(int, 0);
      }
    }

    if(cfg->ticket_enc_alg && cfg->ticket_key) {
       if(!ocaml_set_global_key(0, cfg->ticket_enc_alg, cfg->ticket_key, cfg->ticket_key_len))
       {
         report_error("FFI_mitls_quic_create_caml: set ticket key");
         CAMLreturnT(int, 0);
       }
    }

    if(cfg->ticket_callback) {
      if(!ocaml_set_ticket_callback(&ms, cfg->callback_state, cfg->ticket_callback))
      {
        report_error("FFI_mitls_quic_create_caml: failed to set ticket callback");
        CAMLreturnT(int, 0);
      }
    }

    if(cfg->cert_callbacks) {
      if(!ocaml_set_cert_callbacks(&ms, cfg->callback_state, cfg->cert_callbacks))
      {
        report_error("FFI_mitls_quic_create_caml: failed to set certificate callbacks");
        CAMLreturnT(int, 0);
      }
    }

    if(cfg->is_server) {
      value args[] = {
        PtrToValue(state),
        PtrToValue(QUIC_send),
        PtrToValue(QUIC_recv),
        ms.fstar_state // config
      };
      // call QUIC.ffiAcceptConnected
      result = caml_callbackN_exn(*g_mitls_FFI_QuicCreateServer, 4, args);
    } else {

      // Create ticket:option (t:bytes * si:bytes)
      if(cfg->server_ticket && cfg->server_ticket->ticket_len > 0) {
        tticket = caml_alloc_string(cfg->server_ticket->ticket_len);
        memcpy(String_val(tticket), cfg->server_ticket->ticket, cfg->server_ticket->ticket_len);
        session = caml_alloc_string(cfg->server_ticket->session_len);
        memcpy(String_val(session), cfg->server_ticket->session, cfg->server_ticket->session_len);
        result = caml_alloc_tuple(2);
        Store_field(result, 0, tticket);
        Store_field(result, 1, session);

        oticket = caml_alloc(1, 0);
        Store_field(oticket, 0, result);
      }
      else {
        oticket = Val_none;
      }

      value args[] = {
        PtrToValue(state),
        PtrToValue(QUIC_send),
        PtrToValue(QUIC_recv),
        ms.fstar_state, // config
        oticket
      };
      // Call QUIC.ffiConnect
      result = caml_callbackN_exn(*g_mitls_FFI_QuicCreateClient, 5, args);
    }

    if (Is_exception_result(result)) {
      report_caml_exception(result);
      CAMLreturnT(int, 0);
    }

    // Replace config with connection in state->fstar_state
    caml_modify_generational_global_root(&state->fstar_state, result);

    CAMLreturnT(int, 1);
}

int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg)
{
    int ret;
    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_create_caml(state, cfg);
    caml_release_runtime_system();
    caml_c_thread_unregister();

    return ret;
}

// The OCaml runtime system must be acquired before calling this
static quic_result FFI_mitls_quic_process_caml(
  /* in */ quic_state *state,
  /*in*/ const unsigned char* inBuf,
  /*inout*/ size_t *pInBufLen,
  /*out*/ unsigned char *outBuf,
  /*inout*/ size_t *pOutBufLen)
{
    CAMLparam0();
    CAMLlocal1(result);
    quic_result ret = TLS_error_other;

    // Update the buffers for the QUIC_* callbacks
    state->in_buffer = inBuf;
    state->in_buffer_used = 0;
    state->in_buffer_size = *pInBufLen;
    state->out_buffer = outBuf;
    state->out_buffer_used = 0;
    state->out_buffer_size = *pOutBufLen;

    // Call QUIC.recv
    result = caml_callback_exn(*g_mitls_FFI_QuicProcess, state->fstar_state);

    if (Is_exception_result(result)) {
        report_caml_exception(result);
    } else {
        int rc = Int_val(Field(result, 0));
//        int errorcode = Int_val(Field(result, 1));
//        FIXME: interpret error code
        if (rc <= TLS_server_complete) {
            ret = (quic_result) rc;
        }
    }

    *pInBufLen = state->in_buffer_used;
    *pOutBufLen = state->out_buffer_used;
    CAMLreturnT(quic_result, ret);
}

quic_result MITLS_CALLCONV FFI_mitls_quic_process(
  /* in */ quic_state *state,
  /*in*/ const unsigned char* inBuf,
  /*inout*/ size_t *pInBufLen,
  /*out*/ unsigned char *outBuf,
  /*inout*/ size_t *pOutBufLen)
{
    quic_result ret;

    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_process_caml(state, inBuf, pInBufLen, outBuf, pOutBufLen);
    caml_release_runtime_system();
    caml_c_thread_unregister();

    return ret;
}

int MITLS_CALLCONV FFI_mitls_quic_get_exporter(
  /* in */ quic_state *state,
  int early,
  quic_secret *secret)
{
    int ret;
    mitls_state tls_state = {.fstar_state = state->fstar_state};

    caml_c_thread_register();
    caml_acquire_runtime_system();
    ret = ocaml_get_exporter(&tls_state, early, secret);
    caml_release_runtime_system();
    caml_c_thread_unregister();

    return ret;
}

void MITLS_CALLCONV FFI_mitls_quic_close(quic_state *state)
{
    if (state != NULL) {
        caml_c_thread_register();
        caml_acquire_runtime_system();
        caml_remove_generational_global_root(&state->fstar_state);
        caml_release_runtime_system();
        caml_c_thread_unregister();
        state->fstar_state = 0;
        free(state);
    }
}

#endif

// Certificate selection callback
CAMLprim value ocaml_cert_select_cb(value st, value fp, value pv, value sni_alpn, value sal)
{
  CAMLparam5(st, fp, pv, sni_alpn, sal);
  CAMLlocal3(sni, alpn, ret);
  pfn_FFI_cert_select_cb cb = (pfn_FFI_cert_select_cb)ValueToPtr(fp);

  // We get the list of of offered signature schemes in network format
  // We convert to an array of uint16_t before passing to the callback function
  size_t i, n = caml_string_length(sal)>>1;
  const char *b = String_val(sal);
  uint16_t selected, sigalgs[n];
  for(i=0; i<n; i++) sigalgs[i] = (b[2*i] << 8) + b[2*i+1];

  sni = Field(sni_alpn, 0);
  alpn = Field(sni_alpn, 1);

  // The callback returns a unspecified pointer to the selected certificate
  // and updates the selected signature algorithm (passed by reference)
  void* cert = cb((void*)ValueToPtr(st), (mitls_version)Int_val(pv),
    (unsigned char*)String_val(sni), caml_string_length(sni),
    (unsigned char*)String_val(alpn), caml_string_length(alpn),
    sigalgs, n, &selected);

  if(cert == NULL) CAMLreturn(Val_none);

  ret = caml_alloc_small(2, 0);
  Field(ret, 0) = PtrToValue(cert);
  Field(ret, 1) = Val_int(selected); // UInt16.t is int in OCaml

  CAMLreturn(Val_some(ret));
}

// Certificate formatting callback - this is assumed not to fail.
// FIXME(adl) maybe option bytes would be better for error control?
CAMLprim value ocaml_cert_format_cb(value st, value fp, value cert)
{
  CAMLparam3(st, fp, cert);
  CAMLlocal1(ret);
  pfn_FFI_cert_format_cb cb = (pfn_FFI_cert_format_cb)ValueToPtr(fp);

  unsigned char *buffer = malloc(MAX_CHAIN_LEN);
  if(buffer == NULL) caml_failwith("ocaml_cert_format_cb: failed to allocate certificate chain buffer");

  size_t len = cb((void*)ValueToPtr(st), (void*)ValueToPtr(cert), buffer);
  if(!len) caml_failwith("ocaml_cert_format_cb: certificate formatting callback returned an empty chain");

  ret = caml_alloc_string(len);
  memcpy(String_val(ret), buffer, len);
  free(buffer);

  CAMLreturn(ret);
}

// Signature callback, returns an option bytes
CAMLprim value ocaml_cert_sign_cb(value st, value fp, value cert, value sigalg, value tbs)
{
  CAMLparam5(st, fp, cert, sigalg, tbs);
  CAMLlocal1(ret);
  pfn_FFI_cert_sign_cb cb = (pfn_FFI_cert_sign_cb)ValueToPtr(fp);

  unsigned char *buffer = malloc(MAX_SIGNATURE_LEN);
  if(buffer == NULL) CAMLreturn(Val_none);

  size_t len = cb((void*)ValueToPtr(st), (void*)ValueToPtr(cert), (uint16_t)Int_val(sigalg),
    (const unsigned char*)String_val(tbs), caml_string_length(tbs), buffer);
  if(!len) CAMLreturn(Val_none);

  ret = caml_alloc_string(len);
  memcpy(String_val(ret), buffer, len);
  free(buffer);

  CAMLreturn(Val_some(ret));
}

// Signature callback, returns a bool
// TODO(adl): do we need finer grained error control?
// for now I assume that the application manages the details of validation errors
CAMLprim value ocaml_cert_verify_cb(value st, value fp, value chain, value sigalg, value tbs_sig)
{
  CAMLparam5(st, fp, chain, sigalg, tbs_sig);
  pfn_FFI_cert_verify_cb cb = (pfn_FFI_cert_verify_cb)ValueToPtr(fp);

  // This is to work around the OCaml limitation of 5 arguments
  value tbs = Field(tbs_sig, 0);
  value sig = Field(tbs_sig, 1);

  int success = cb((void*)ValueToPtr(st),
    (const unsigned char*)String_val(chain), caml_string_length(chain),
    (uint16_t)Int_val(sigalg),
    (const unsigned char*)String_val(tbs), caml_string_length(tbs),
    (const unsigned char*)String_val(sig), caml_string_length(sig));

  CAMLreturn(success ? Val_true : Val_false);
}

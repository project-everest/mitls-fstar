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
  MITLS_FFI_ENTRY(QuicProcess) \
  MITLS_FFI_ENTRY(QuicGetPeerParameters) \
  MITLS_FFI_ENTRY(TicketCallback) \
  MITLS_FFI_ENTRY(CertSelectCallback) \
  MITLS_FFI_ENTRY(CertFormatCallback) \
  MITLS_FFI_ENTRY(CertSignCallback) \
  MITLS_FFI_ENTRY(CertVerifyCallback)

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

    char *Argv[2];

    // Build a stub argv[] to satisfy caml_Startup()
    Argv[0] = "";
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

// Input:  msg - an error message string to log
//         errmsg - in/out pointer to the current error log string, may
//                  point to NULL
// Return:
//         nothing
//         *errmsg updated by realloc and appending the exception text.
//                 On out-of-memory, the new message is discarded and
//                 the current error log string is returned unmodified.
static void report_error(const char *msg, char **errmsg)
{
    if (msg == NULL) {
        return;
    }
    if (*errmsg == NULL) {
        *errmsg = strdup(msg);
    } else {
        char *newerrmsg = malloc(strlen(*errmsg) + strlen(msg) + 2);
        if (newerrmsg) {
            strcpy(newerrmsg, *errmsg);
            strcat(newerrmsg, "\n");
            strcat(newerrmsg, msg);
            free(*errmsg);
            *errmsg = newerrmsg;
        }
    }
}

// Input:  v - an OCaml exception
//         errmsg - in/out pointer to the current error log string, may
//                  point to NULL
// Return:
//         nothing
//         *errmsg updated by realloc and appending the exception text.
//                 On out-of-memory, the new exception is discarded and
//                 the current error log string is returned unmodified.
static void report_caml_exception(value v, char **errmsg)
{
    if (errmsg) {
        char * msg = caml_format_exception(Extract_exception(v));
        report_error(msg, errmsg);
        free(msg);
    }
}

// The OCaml runtime system must be acquired before calling this
static int FFI_mitls_configure_caml(mitls_state **state, const char *tls_version, const char *host_name, char **outmsg, char **errmsg)
{
    CAMLparam0();
    CAMLlocal3(config, version, host);
    int ret = 0;

    version = caml_copy_string(tls_version);
    host = caml_copy_string(host_name);
    config = caml_callback2_exn(*g_mitls_FFI_Config, version, host);
    if (Is_exception_result(config)) {
        report_caml_exception(config, errmsg);
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
int MITLS_CALLCONV FFI_mitls_configure(mitls_state **state, const char *tls_version, const char *host_name, char **outmsg, char **errmsg)
{
    int ret;

    *state = NULL;
    *outmsg = NULL;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_configure_caml(state, tls_version, host_name, outmsg, errmsg);
    caml_release_runtime_system();

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
        report_caml_exception(config, NULL); // bugbug: pass in errmsg
    } else {
        state->fstar_state = config;
        ret = 1;
    }


    CAMLreturnT(int,ret);
}

// The OCaml runtime system must be acquired before calling this
static int ocaml_set_ticket_key(const char *alg, const char *ticketkey, size_t klen)
{
    int ret;
    CAMLparam0();
    CAMLlocal3(r, a, tkey);
    tkey = caml_alloc_string(klen);
    memcpy(String_val(tkey), ticketkey, klen);

    a = caml_copy_string(alg);
    r = caml_callback2_exn(*g_mitls_FFI_SetTicketKey, a, tkey);

    if (Is_exception_result(r)) {
      report_caml_exception(r, NULL); // bugbug: pass in errmsg
      ret = 0;
    } else {
      ret = Int_val(r);
    }
    CAMLreturnT(int, ret);
}

int MITLS_CALLCONV FFI_mitls_set_ticket_key(const char *alg, const char *tk, size_t klen)
{
    int ret;
    caml_acquire_runtime_system();
    ret = ocaml_set_ticket_key(alg, tk, klen);
    caml_release_runtime_system();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char * cs)
{
    int ret;
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, cs, g_mitls_FFI_SetCipherSuites);
    caml_release_runtime_system();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char * sa)
{
    int ret;
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, sa, g_mitls_FFI_SetSignatureAlgorithms);
    caml_release_runtime_system();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char * ng)
{
    int ret;
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, ng, g_mitls_FFI_SetNamedGroups);
    caml_release_runtime_system();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_alpn(/* in */ mitls_state *state, const char *apl)
{
    int ret;
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, apl, g_mitls_FFI_SetALPN);
    caml_release_runtime_system();
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
  t.ticket = String_val(ticket);
  t.session = String_val(session);
  cb((void*)ValueToPtr(st), String_val(sni), &t);
  CAMLreturn(Val_unit);
}

static int ocaml_set_ticket_callback(/* in */ mitls_state *state, void *cb_state, pfn_FFI_ticket_cb ticket_cb)
{
    CAMLparam0();
    CAMLlocal4(config, cb, cbs, ocb);
    int ret = 0;

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

    CAMLreturnT(int, ret);
}

int MITLS_CALLCONV FFI_mitls_configure_ticket_callback(/* in */ mitls_state *state, void *cb_state, pfn_FFI_ticket_cb ticket_cb)
{
    int ret;
    caml_acquire_runtime_system();
    ret = ocaml_set_ticket_callback(state, cb_state, ticket_cb);
    caml_release_runtime_system();
    return ret;
}

static int ocaml_set_cert_callbacks(/* in */ mitls_state *state, void *cb_state, mitls_cert_cb *cb)
{
    CAMLparam0();
    CAMLlocal3(config, cbs, ocb);
    CAMLlocal4(select, format, sign, verify);
    int ret = 0;

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

    CAMLreturnT(int, ret);
}

int MITLS_CALLCONV FFI_mitls_configure_cert_callbacks(/* in */ mitls_state *state, void *cb_state, mitls_cert_cb *cert_cb)
{
    int ret;
    caml_acquire_runtime_system();
    ret = ocaml_set_cert_callbacks(state, cb_state, cert_cb);
    caml_release_runtime_system();
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
        report_caml_exception(config, NULL); // bugbug: pass in errmsg
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
    caml_acquire_runtime_system();
    ret = configure_common_bool_caml(state, max_ed, g_mitls_FFI_SetEarlyData);
    caml_release_runtime_system();
    return ret;
}

// Called by the host app to free a mitls_state allocated by FFI_mitls_configure()
void MITLS_CALLCONV FFI_mitls_close(mitls_state *state)
{
    if (state) {
        caml_acquire_runtime_system();
        caml_remove_generational_global_root(&state->fstar_state);
        caml_release_runtime_system();
        state->fstar_state = 0;
        free(state);
    }
}

void MITLS_CALLCONV FFI_mitls_free_msg(char *msg)
{
    free(msg);
}

void MITLS_CALLCONV FFI_mitls_free_packet(void *packet)
{
    free(packet);
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

// Called from FStar code to send via TCP
CAMLprim value ocaml_send_tcp(value cookie, value bytes)
{
    mlsize_t buffer_size;
    char *buffer;
    int retval;
    struct _FFI_mitls_callbacks *callbacks;
    char *localbuffer;

    CAMLparam2(cookie, bytes);

    callbacks = (struct _FFI_mitls_callbacks *)ValueToPtr(cookie);
    buffer = Bp_val(bytes);
    buffer_size = caml_string_length(bytes);
    // Copy the buffer out of the OCaml heap into a local buffer on the stack
    localbuffer = (char*)alloca(buffer_size);
    memcpy(localbuffer, buffer, buffer_size);

    caml_release_runtime_system();
    // All pointers into the OCaml heap are now off-limits until the
    // runtime_system lock has been re-aquired.
    retval = (*callbacks->send)(callbacks, localbuffer, buffer_size);
    caml_acquire_runtime_system();

    CAMLreturn(Val_int(retval));
}

// Called from FStar code to receive via TCP
CAMLprim value ocaml_recv_tcp(value cookie, value bytes)
{
    mlsize_t buffer_size;
    char *buffer;
    ssize_t retval;
    struct _FFI_mitls_callbacks *callbacks;
    char *localbuffer;

    CAMLparam2(cookie, bytes);

    callbacks = (struct _FFI_mitls_callbacks *)ValueToPtr(cookie);
    buffer_size = caml_string_length(bytes);
    localbuffer = (char*)alloca(buffer_size);

    caml_release_runtime_system();
    // All pointers into the OCaml heap are now off-limits until the
    // runtime_system lock has been re-aquired.
    retval = (*callbacks->recv)(callbacks, localbuffer, buffer_size);
    caml_acquire_runtime_system();

    buffer = Bp_val(bytes);
    memcpy(buffer, localbuffer, buffer_size);

    CAMLreturn(Val_int(retval));
}

static int FFI_mitls_connect_caml(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket, /* out */ char **errmsg)
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
      state->fstar_state,
      PtrToValue(callbacks),
      oticket
    };

    result = caml_callbackN_exn(*g_mitls_FFI_Connect, 3, args);
    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
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
int MITLS_CALLCONV FFI_mitls_connect(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    int ret;
    mitls_ticket ticket = {0};

    *outmsg = NULL;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_connect_caml(callbacks, state, &ticket, errmsg);
    caml_release_runtime_system();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_resume(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket, /* out */ char **errmsg)
{
    int ret;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_connect_caml(callbacks, state, ticket, errmsg);
    caml_release_runtime_system();
    return ret;
}

static int FFI_mitls_accept_connected_caml(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal1(result);
    int ret;

    result = caml_callback2_exn(*g_mitls_FFI_AcceptConnected, state->fstar_state, PtrToValue(callbacks));
    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
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
int MITLS_CALLCONV FFI_mitls_accept_connected(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    int ret;
    *outmsg = NULL;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_accept_connected_caml(callbacks, state, outmsg, errmsg);
    caml_release_runtime_system();
    return ret;
}



static int FFI_mitls_send_caml(/* in */ mitls_state *state, const void* buffer, size_t buffer_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal2(buffer_value, result);
    int ret;

    buffer_value = caml_alloc_string(buffer_size);
    memcpy(Bp_val(buffer_value), buffer, buffer_size);

    result = caml_callback2_exn(*g_mitls_FFI_Send, state->fstar_state, buffer_value);
    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
        ret = 0;
    } else {
        ret = 1;
    }

    CAMLreturnT(int, ret);
}

// Called by the host app transmit a packet
int MITLS_CALLCONV FFI_mitls_send(/* in */ mitls_state *state, const void* buffer, size_t buffer_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    int ret;
    *outmsg = NULL;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_send_caml(state, buffer, buffer_size, outmsg, errmsg);
    caml_release_runtime_system();
    return ret;
}

static void * FFI_mitls_receive_caml(/* in */ mitls_state *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal1(result);
    void *p = NULL;

    result = caml_callback_exn(*g_mitls_FFI_Recv, state->fstar_state);
    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
        p = NULL;
    } else {
        // Return the plaintext data
        p = copypacket(result, packet_size);
    }

    CAMLreturnT(void*, p);
}

// Called by the host app to receive a packet
void * MITLS_CALLCONV FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    void *p;
    *outmsg = NULL;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    p = FFI_mitls_receive_caml(state, packet_size, outmsg, errmsg);
    caml_release_runtime_system();
    return p;
}

// The OCaml runtime system must be acquired before calling this
static int ocaml_get_exporter(
  /* in */ mitls_state *state,
  int early,
  mitls_secret *secret,
  /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal2(result, tmp);

    result = caml_callback2_exn(*g_mitls_FFI_GetExporter,
                                state->fstar_state,
                                early ? Val_true : Val_false);

    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
        CAMLreturnT(int, 0);
    }

    // Secret not available
    if(result == Val_none)
    {
      *errmsg = strdup("the requested secret is not yet available");
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

int MITLS_CALLCONV FFI_mitls_get_exporter(/* in */ mitls_state *state, int early, /* out */ mitls_secret *secret, /* out */ char **errmsg)
{
  int ret;
  *errmsg = NULL;

  caml_acquire_runtime_system();
  ret = ocaml_get_exporter(state, early, secret, errmsg);
  caml_release_runtime_system();
  return ret;
}

static void * FFI_mitls_get_cert_caml(/* in */ mitls_state *state, /* out */ size_t *cert_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal1(result);
    void *p = NULL;

    result = caml_callback_exn(*g_mitls_FFI_GetCert, state->fstar_state);
    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
        p = NULL;
    } else {
        // Return the certificate bytes
        p = copypacket(result, cert_size);
    }

    CAMLreturnT(void*, p);
}

void *MITLS_CALLCONV FFI_mitls_get_cert(/* in */ mitls_state *state, /* out */ size_t *cert_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    void *p;
    *outmsg = NULL;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    p = FFI_mitls_get_cert_caml(state, cert_size, outmsg, errmsg);
    caml_release_runtime_system();
    return p;
}

// Register the calling thread, so it can call miTLS.  Returns 1 for success, 0 for error.
int MITLS_CALLCONV FFI_mitls_thread_register(void)
{
    return caml_c_thread_register();
}

// Unregister the calling thread, so it can no longer call miTLS.  Returns 1 for success, 0 for error.
int MITLS_CALLCONV FFI_mitls_thread_unregister(void)
{
    return caml_c_thread_unregister();
}

/*************************************************************************
* QUIC FFI
**************************************************************************/

// ADL yikes!! can't we just expose the mitls_state to the callback??
#define CONTAINING_RECORD(address, type, field) ((type *)((char*)(address) - (size_t)(&((type *)0)->field)))

typedef struct quic_state {
   value fstar_state; // a GC root representing an F*-side state object
   struct _FFI_mitls_callbacks ffi_callbacks;
   int is_server;
   char* in_buffer;
   size_t in_buffer_size;
   size_t in_buffer_used;
   char* out_buffer;
   size_t out_buffer_size;
   size_t out_buffer_used;
   char *errmsg;
} quic_state;

 int QUIC_send(struct _FFI_mitls_callbacks *cb, const void *buffer, size_t buffer_size)
 {
//   FILE *fp = fopen("send_log", "a");
//   fprintf(fp, "CALLBACK: send %u\n", buffer_size);
   quic_state* s = CONTAINING_RECORD(cb, quic_state, ffi_callbacks);
//   fprintf(fp, "Current %s state: IN=%u/%u OUT=%u/%u\n", s->is_server ? "server" : "client", s->in_buffer_used, s->in_buffer_size, s->out_buffer_used, s->out_buffer_size);
//   fclose(fp);
   if(!s->out_buffer)
   {
       report_error("QUIC_send():  out_buffer is NULL", &s->errmsg);
       return -1;
   }

   // ADL FIXME better error management
   if(buffer_size <= s->out_buffer_size - s->out_buffer_used)
   {
     memcpy(s->out_buffer + s->out_buffer_used, buffer, buffer_size);
     s->out_buffer_used += buffer_size;
     return buffer_size;
   }

   report_error("QUIC_send():  Insufficient space in out_buffer", &s->errmsg);
   return -1;
 }

 int QUIC_recv(struct _FFI_mitls_callbacks *cb, void *buffer, size_t len)
 {
//   FILE *fp = fopen("recv_log", "a");
//   fprintf(fp, "CALLBACK: recv %u\n", len);
   quic_state* s = CONTAINING_RECORD(cb, quic_state, ffi_callbacks);
//   fprintf(fp, "Current %s state: IN=%u/%u OUT=%u/%u\n", s->is_server ? "server" : "client", s->in_buffer_used, s->in_buffer_size, s->out_buffer_used, s->out_buffer_size);
//   fclose(fp);

   if(!s->in_buffer || buffer == NULL)
   {
       report_error("QUIC_recv():  in_buffer or buffer is NULL", &s->errmsg);
       return -1;
   }

   if(len > s->in_buffer_size - s->in_buffer_used)
     len = s->in_buffer_size - s->in_buffer_used; // may be 0

   memcpy(buffer, s->in_buffer + s->in_buffer_used, len);
   s->in_buffer_used += len;
   return len;
 }

static value ocaml_alloc_version_list(const uint32_t *list, size_t len)
{
  CAMLparam0 ();
  CAMLlocal2 (result, r);

  uint32_t default_ver[] = {0xff000005}; // DRAFT 5
  if(!list || !len){ list = default_ver; len = 1; }
  result = Val_int(0);

  for(size_t i = 0; i < len; i++) {
    r = caml_alloc_small(2, 0);
    Field(r, 0) = Val_int(list[len - i - 1]);
    Field(r, 1) = result;
    result = r;
  }

  CAMLreturn(result);
}

// The OCaml runtime system must be acquired before calling this
static int FFI_mitls_quic_create_caml(quic_state **st, quic_config *cfg, char **errmsg)
{
    CAMLparam0();
    CAMLlocal4(result, host, others, versions);
    CAMLlocal3(tticket, session, oticket);

    *st = NULL;
    quic_state* state = malloc(sizeof(quic_state));
    if(!state) {
      *errmsg = strdup("failed to allocate QUIC state");
      CAMLreturnT(int, 0);
    }
    memset(state, 0, sizeof(*state));
    *st = state;

    state->ffi_callbacks.send = QUIC_send;
    state->ffi_callbacks.recv = QUIC_recv;
    state->is_server = cfg->is_server;

    others = caml_alloc_string(cfg->qp.tp_len);
    memcpy(String_val(others), cfg->qp.tp_data, cfg->qp.tp_len);

    if(cfg->host_name)
      host = caml_copy_string(cfg->host_name);
    else
      host = caml_alloc_string(0);

    value args[] = {
      others,
      ocaml_alloc_version_list(cfg->supported_versions, cfg->supported_versions_len),
      host
    };

    result = caml_callbackN_exn(*g_mitls_FFI_QuicConfig, 3, args);
    if (Is_exception_result(result)) {
      report_caml_exception(result, errmsg);
      CAMLreturnT(int,0);
    }

    // config
    state->fstar_state = result;
    caml_register_generational_global_root(&state->fstar_state);
    mitls_state ms = {.fstar_state = result};

    if(cfg->cipher_suites)
       if(!configure_common_caml(&ms, cfg->cipher_suites, g_mitls_FFI_SetCipherSuites))
       {
         *errmsg = strdup("FFI_mitls_quic_create_caml: cipher suite list");
         CAMLreturnT(int, 0);
       }

    if(cfg->named_groups)
       if(!configure_common_caml(&ms, cfg->named_groups, g_mitls_FFI_SetNamedGroups))
       {
         *errmsg = strdup("FFI_mitls_quic_create_caml: supported groups list");
         CAMLreturnT(int, 0);
       }

    if(cfg->signature_algorithms)
       if(!configure_common_caml(&ms, cfg->signature_algorithms, g_mitls_FFI_SetSignatureAlgorithms))
       {
         *errmsg = strdup("FFI_mitls_quic_create_caml: signature algorithms list");
         CAMLreturnT(int, 0);
       }

    if(cfg->alpn)
      if(!configure_common_caml(&ms, cfg->alpn, g_mitls_FFI_SetALPN))
      {
        *errmsg = strdup("FFI_mitls_quic_create_caml: failed to set application-level protocols");
        CAMLreturnT(int, 0);
      }

    if(cfg->ticket_enc_alg && cfg->ticket_key)
       if(!ocaml_set_ticket_key(cfg->ticket_enc_alg, cfg->ticket_key, cfg->ticket_key_len))
       {
         *errmsg = strdup("FFI_mitls_quic_create_caml: set ticket key");
         CAMLreturnT(int, 0);
       }

    if(cfg->enable_0rtt)
       if(!configure_common_bool_caml(&ms, Val_int(0xFFFFFFFF), g_mitls_FFI_SetEarlyData))
       {
         *errmsg = strdup("FFI_mitls_quic_create_caml: can't enable early_data");
         CAMLreturnT(int, 0);
       }

    if(cfg->ticket_callback)
      if(!ocaml_set_ticket_callback(&ms, cfg->callback_state, cfg->ticket_callback))
      {
        *errmsg = strdup("FFI_mitls_quic_create_caml: failed to set ticket callback");
        CAMLreturnT(int, 0);
      }

    if(cfg->cert_callbacks)
      if(!ocaml_set_cert_callbacks(&ms, cfg->callback_state, cfg->cert_callbacks))
      {
        *errmsg = strdup("FFI_mitls_quic_create_caml: failed to set certificate callbacks");
        CAMLreturnT(int, 0);
      }

    if(cfg->is_server)
      result = caml_callback2_exn(
                                  *g_mitls_FFI_QuicCreateServer,
                                  ms.fstar_state, // config
                                  PtrToValue(&state->ffi_callbacks));
    else {

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
        ms.fstar_state, // config
        oticket,
        PtrToValue(&state->ffi_callbacks) };
      result = caml_callbackN_exn(*g_mitls_FFI_QuicCreateClient, 3, args);
    }

    if (Is_exception_result(result)) {
      report_caml_exception(result, errmsg);
      CAMLreturnT(int, 0);
    }

    // Replace config with connection in state->fstar_state
    caml_modify_generational_global_root(&state->fstar_state, result);

    CAMLreturnT(int, 1);
}

int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg, /* out */ char **errmsg)
{
    int ret;
    *errmsg = NULL;
    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_create_caml(state, cfg, errmsg);
    caml_release_runtime_system();

    return ret;
}

// The OCaml runtime system must be acquired before calling this
static quic_result FFI_mitls_quic_process_caml(
  /* in */ quic_state *state,
  /*in*/ char* inBuf,
  /*inout*/ size_t *pInBufLen,
  /*out*/ char *outBuf,
  /*inout*/ size_t *pOutBufLen,
  /* out */ char **errmsg)
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
    state->errmsg = NULL;

    result = caml_callback_exn(*g_mitls_FFI_QuicProcess, state->fstar_state);

    if (Is_exception_result(result)) {
        report_caml_exception(result, &state->errmsg);
    } else {
        int rc = Int_val(Field(result, 0));
        int errorcode = Int_val(Field(result, 1));
        if (rc <= TLS_server_complete) {
            ret = (quic_result) rc;
        }
    }

    *pInBufLen = state->in_buffer_used;
    *pOutBufLen = state->out_buffer_used;
    *errmsg = state->errmsg;
    state->errmsg = NULL;
    CAMLreturnT(quic_result, ret);
}

quic_result MITLS_CALLCONV FFI_mitls_quic_process(
  /* in */ quic_state *state,
  /*in*/ char* inBuf,
  /*inout*/ size_t *pInBufLen,
  /*out*/ char *outBuf,
  /*inout*/ size_t *pOutBufLen,
  /* out */ char **errmsg)
{
    quic_result ret;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_process_caml(state, inBuf, pInBufLen, outBuf, pOutBufLen, errmsg);
    caml_release_runtime_system();

    return ret;
}

static int FFI_mitls_quic_get_peer_parameters_caml(
  /* in */ quic_state *state,
  /* out */ uint32_t *ver,
  /* out */ quic_transport_parameters *qp,
  /* out */ char **errmsg)
{
  CAMLparam0();
  CAMLlocal2(result, tmp);
  assert(qp);

  result = caml_callback_exn(*g_mitls_FFI_QuicGetPeerParameters, state->fstar_state);

  if (Is_exception_result(result)) {
      report_caml_exception(result, errmsg);
      CAMLreturnT(int, 0);
  }

/*
  tmp = Field(result, 4);
  size_t len = caml_string_length(tmp);
  qp->max_stream_data = Int_val(Field(result, 0));
  qp->max_data = Int_val(Field(result, 1));
  qp->max_stream_id = Int_val(Field(result, 2));
  qp->idle_timeout = Int_val(Field(result, 3));
  qp->others_len = len;
  memcpy(qp->others, String_val(tmp), len);
*/
  *ver = Int_val(Field(result, 0));
  tmp = Field(result, 1);
  qp->tp_len = caml_string_length(tmp);
  if(qp->tp_data) memcpy((char*)qp->tp_data, String_val(tmp), qp->tp_len);

  CAMLreturnT(int, 1);
}

int MITLS_CALLCONV FFI_mitls_quic_get_peer_parameters(
  /* in */ quic_state *state,
  /* out */ uint32_t *ver,
  /* out */ quic_transport_parameters *qp,
  /* out */ char **errmsg)
{
    int ret;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_get_peer_parameters_caml(state, ver, qp, errmsg);
    caml_release_runtime_system();

    return ret;
}

int MITLS_CALLCONV FFI_mitls_quic_get_exporter(
  /* in */ quic_state *state,
  int early,
  quic_secret *secret,
  /* out */ char **errmsg)
{
    int ret;
    mitls_state tls_state = {.fstar_state = state->fstar_state};
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = ocaml_get_exporter(&tls_state, early, secret, errmsg);
    caml_release_runtime_system();

    return ret;
}

void MITLS_CALLCONV FFI_mitls_quic_free(quic_state *state)
{
    if (state != NULL) {
        caml_acquire_runtime_system();
        caml_remove_generational_global_root(&state->fstar_state);
        caml_release_runtime_system();
        state->fstar_state = 0;
        free(state);
    }
}

// Certificate selection callback
CAMLprim value ocaml_cert_select_cb(value st, value fp, value sni, value sal)
{
  CAMLparam4(st, fp, sni, sal);
  CAMLlocal1(ret);
  pfn_FFI_cert_select_cb cb = (pfn_FFI_cert_select_cb)ValueToPtr(fp);

  // We get the list of of offered signature schemes in network format
  // We convert to an array of uint16_t before passing to the callback function
  size_t i, n = caml_string_length(sal)>>1;
  const char *b = String_val(sal);
  uint16_t selected, sigalgs[n];
  for(i=0; i<n; i++) sigalgs[i] = (b[2*i] << 8) + b[2*i+1];

  // The callback returns a unspecified pointer to the selected certificate
  // and updates the selected signature algorithm (passed by reference)
  void* cert = cb((void*)ValueToPtr(st), String_val(sni), sigalgs, n, &selected);
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

  char *buffer = malloc(MAX_CHAIN_LEN);
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

  char *buffer = malloc(MAX_SIGNATURE_LEN);
  if(buffer == NULL) CAMLreturn(Val_none);

  size_t len = cb((void*)ValueToPtr(st), (void*)ValueToPtr(cert), (uint16_t)Int_val(sigalg), String_val(tbs), caml_string_length(tbs), buffer);
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

  int success = cb((void*)ValueToPtr(st), String_val(chain), caml_string_length(chain),
    (uint16_t)Int_val(sigalg),  String_val(tbs), caml_string_length(tbs),
    String_val(sig), caml_string_length(sig));

  CAMLreturn(success ? Val_true : Val_false);
}

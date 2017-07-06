#include <stdio.h>
#include <memory.h>
#include <unistd.h>
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
#include "mitlsffi.h"

#define MITLS_FFI_LIST \
  MITLS_FFI_ENTRY(Config) \
  MITLS_FFI_ENTRY(SetTicketKey) \
  MITLS_FFI_ENTRY(SetCertChainFile) \
  MITLS_FFI_ENTRY(SetPrivateKeyFile) \
  MITLS_FFI_ENTRY(SetCAFile) \
  MITLS_FFI_ENTRY(SetCipherSuites) \
  MITLS_FFI_ENTRY(SetSignatureAlgorithms) \
  MITLS_FFI_ENTRY(SetNamedGroups) \
  MITLS_FFI_ENTRY(SetALPN) \
  MITLS_FFI_ENTRY(SetEarlyData) \
  MITLS_FFI_ENTRY(Connect) \
  MITLS_FFI_ENTRY(AcceptConnected) \
  MITLS_FFI_ENTRY(Send) \
  MITLS_FFI_ENTRY(Recv) \
  MITLS_FFI_ENTRY(GetCert) \
  MITLS_FFI_ENTRY(QuicConfig) \
  MITLS_FFI_ENTRY(QuicCreateClient) \
  MITLS_FFI_ENTRY(QuicCreateServer) \
  MITLS_FFI_ENTRY(QuicProcess) \
  MITLS_FFI_ENTRY(QuicGetParameters) \
  MITLS_FFI_ENTRY(QuicGetExporter) \
  MITLS_FFI_ENTRY(QuicGetTicket)

// Pointers to ML code.  Initialized in FFI_mitls_init().  Invoke via caml_callback()
#define MITLS_FFI_ENTRY(x) value* g_mitls_FFI_##x;
MITLS_FFI_LIST
#undef MITLS_FFI_ENTRY

// Pass a C pointer into F* and recover it back.  OCaml limits integers to 2^30/2^62
// so shift right by 1 before conversion to OCaml.  The low bit must be 0 in order to
// meet structure alignment rules, so this is not lossy.
_Static_assert(sizeof(size_t) <= sizeof(value), "OCaml value isn't large enough to hold a C pointer");
#define PtrToValue(p) Val_long(((size_t)p)>>1)
#define ValueToPtr(v) ((void*)((Long_val(v)<<1)))

typedef struct mitls_state {
    value fstar_state;    // a GC root representing an F*-side state object
} mitls_state;

//
// Initialize miTLS.
//
//  Called once ahead of using miTLS
//
//  Returns:  0 for error, nonzero for success
//
int MITLS_CALLCONV FFI_mitls_init(void)
{
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

    return 1; // success
}

void MITLS_CALLCONV FFI_mitls_cleanup(void)
{
#define MITLS_FFI_ENTRY(x) \
    g_mitls_FFI_##x = NULL;
 MITLS_FFI_LIST
 #undef MITLS_FFI_ENTRY
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

int MITLS_CALLCONV FFI_mitls_configure_cert_chain_file(/* in */ mitls_state *state, const char * file)
{
    int ret;
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, file, g_mitls_FFI_SetCertChainFile);
    caml_release_runtime_system();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_private_key_file(/* in */ mitls_state *state, const char * file)
{
    int ret;
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, file, g_mitls_FFI_SetPrivateKeyFile);
    caml_release_runtime_system();
    return ret;
}

int MITLS_CALLCONV FFI_mitls_configure_ca_file(/* in */ mitls_state *state, const char * file)
{
    int ret;
    caml_acquire_runtime_system();
    ret = configure_common_caml(state, file, g_mitls_FFI_SetCAFile);
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

int MITLS_CALLCONV FFI_mitls_configure_early_data(/* in */ mitls_state *state, int enable_early_data)
{
    int ret;
    value b = (enable_early_data) ? Val_true : Val_false;
    caml_acquire_runtime_system();
    ret = configure_common_bool_caml(state, b, g_mitls_FFI_SetEarlyData);
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

static int FFI_mitls_connect_caml(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal1(result);
    int ret;

    result = caml_callback2_exn(*g_mitls_FFI_Connect, state->fstar_state, PtrToValue(callbacks));
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

    *outmsg = NULL;
    *errmsg = NULL;

    caml_acquire_runtime_system();
    ret = FFI_mitls_connect_caml(callbacks, state, outmsg, errmsg);
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
} quic_state;

 int QUIC_send(struct _FFI_mitls_callbacks *cb, const void *buffer, size_t buffer_size)
 {
//   FILE *fp = fopen("send_log", "a");
//   fprintf(fp, "CALLBACK: send %u\n", buffer_size);
   quic_state* s = CONTAINING_RECORD(cb, quic_state, ffi_callbacks);
//   fprintf(fp, "Current %s state: IN=%u/%u OUT=%u/%u\n", s->is_server ? "server" : "client", s->in_buffer_used, s->in_buffer_size, s->out_buffer_used, s->out_buffer_size);
//   fclose(fp);
   if(!s->out_buffer) return -1;

   // ADL FIXME better error management
   if(buffer_size <= s->out_buffer_size - s->out_buffer_used)
   {
     memcpy(s->out_buffer + s->out_buffer_used, buffer, buffer_size);
     s->out_buffer_used += buffer_size;
     return buffer_size;
   }

   return -1;
 }

 int QUIC_recv(struct _FFI_mitls_callbacks *cb, void *buffer, size_t len)
 {
//   FILE *fp = fopen("recv_log", "a");
//   fprintf(fp, "CALLBACK: recv %u\n", len);
   quic_state* s = CONTAINING_RECORD(cb, quic_state, ffi_callbacks);
//   fprintf(fp, "Current %s state: IN=%u/%u OUT=%u/%u\n", s->is_server ? "server" : "client", s->in_buffer_used, s->in_buffer_size, s->out_buffer_used, s->out_buffer_size);
//   fclose(fp);

   if(!s->in_buffer || buffer == NULL) return -1;

   if(len > s->in_buffer_size - s->in_buffer_used)
     len = s->in_buffer_size - s->in_buffer_used; // may be 0

   memcpy(buffer, s->in_buffer + s->in_buffer_used, len);
   s->in_buffer_used += len;
   return len;
 }


// The OCaml runtime system must be acquired before calling this
static int FFI_mitls_quic_create_caml(quic_state **st, quic_config *cfg, char **errmsg)
{
    CAMLparam0();
    CAMLlocal2(result, host);

    *st = NULL;
    quic_state* state = malloc(sizeof(quic_state));
    if(!state) {
      *errmsg = "failed to allocate QUIC state";
      CAMLreturnT(int, 0);
    }
    *st = state;

    state->ffi_callbacks.send = QUIC_send;
    state->ffi_callbacks.recv = QUIC_recv;
    state->is_server = cfg->is_server;
    state->in_buffer = NULL;
    state->in_buffer_size = 0;
    state->in_buffer_used = 0;
    state->out_buffer = NULL;
    state->out_buffer_size = 0;
    state->out_buffer_used = 0;

    host = caml_copy_string(cfg->host_name);
    value args[] = {
      Int_val(cfg->qp.max_stream_data),
      Int_val(cfg->qp.max_data),
      Int_val(cfg->qp.max_stream_id),
      Int_val(cfg->qp.idle_timeout),
      host
    };

    result = caml_callbackN_exn(*g_mitls_FFI_QuicConfig, 5, args);
    if (Is_exception_result(result)) {
      report_caml_exception(result, errmsg);
      CAMLreturnT(int,0);
    }

    // config
    state->fstar_state = result;
    caml_register_generational_global_root(&state->fstar_state);
    mitls_state ms = {.fstar_state = result};

    // ADL: any of these calls may fail. Need better errors to figure out which
    if(cfg->certificate_chain_file)
      if(!configure_common_caml(&ms, cfg->certificate_chain_file, g_mitls_FFI_SetCertChainFile))
      {
        *errmsg = "FFI_mitls_quic_create_caml: certificate chain file";
        CAMLreturnT(int, 0);
      }

    if(cfg->private_key_file)
       if(!configure_common_caml(&ms, cfg->private_key_file, g_mitls_FFI_SetPrivateKeyFile))
       {
         *errmsg = "FFI_mitls_quic_create_caml: private key file";
         CAMLreturnT(int, 0);
       }

    if(cfg->ca_file)
       if(!configure_common_caml(&ms, cfg->ca_file, g_mitls_FFI_SetCAFile))
       {
         *errmsg = "FFI_mitls_quic_create_caml: CA file";
         CAMLreturnT(int, 0);
       }

    if(cfg->cipher_suites)
       if(!configure_common_caml(&ms, cfg->cipher_suites, g_mitls_FFI_SetCipherSuites))
       {
         *errmsg = "FFI_mitls_quic_create_caml: cipher suite list";
         CAMLreturnT(int, 0);
       }

    if(cfg->named_groups)
       if(!configure_common_caml(&ms, cfg->named_groups, g_mitls_FFI_SetNamedGroups))
       {
         *errmsg = "FFI_mitls_quic_create_caml: supported groups list";
         CAMLreturnT(int, 0);
       }

    if(cfg->signature_algorithms)
       if(!configure_common_caml(&ms, cfg->signature_algorithms, g_mitls_FFI_SetSignatureAlgorithms))
       {
         *errmsg = "FFI_mitls_quic_create_caml: signature algorithms list";
         CAMLreturnT(int, 0);
       }

    if(cfg->ticket_enc_alg && cfg->ticket_key)
       if(!ocaml_set_ticket_key(cfg->ticket_enc_alg, cfg->ticket_key, cfg->ticket_key_len))
       {
         *errmsg = "FFI_mitls_quic_create_caml: set ticket key";
         CAMLreturnT(int, 0);
       }

    if(cfg->enable_0rtt)
       if(!configure_common_bool_caml(&ms, 1, g_mitls_FFI_SetEarlyData))
       {
         *errmsg = "FFI_mitls_quic_create_caml: can't enable early_data";
         CAMLreturnT(int, 0);
       }

    result = caml_callback2_exn(
      cfg->is_server ? *g_mitls_FFI_QuicCreateServer : *g_mitls_FFI_QuicCreateClient,
      ms.fstar_state, // config
      PtrToValue(&state->ffi_callbacks));

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
    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_create_caml(state, cfg, errmsg);
    caml_release_runtime_system();

    return ret;
}

/*
NTSTATUS
QuicTlsRecv(
    _In_                            PQUIC_TLS   pTLS,
    _In_reads_bytes_(inBufLen)      PUCHAR      inBuf,
    _Inout_                         PUINT32     pInBufLen,
    _Out_writes_bytes_(outBufLen)   PUCHAR      outBuf,
    _Inout_                         PUINT32     pOutBufLen
    );
*/

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

    result = caml_callback_exn(*g_mitls_FFI_QuicProcess, state->fstar_state);

    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
        ret = TLS_error_other;
    } else {
        int rc = Int_val(Field(result, 0));
        int errorcode = Int_val(Field(result, 1));
        if (rc <= TLS_server_complete) {
            ret = (quic_result) rc;
        } else {
            ret = TLS_error_other;
        }

        *pInBufLen = state->in_buffer_used;
        *pOutBufLen = state->out_buffer_used;
    }

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

static int FFI_mitls_quic_get_parameters_caml(/* in */ quic_state *state, quic_transport_parameters *qp)
{
    // bugbug: implement.  Need to pass role as a parameter, and sort out
    //         the return type.
    return 0;
}

int MITLS_CALLCONV FFI_mitls_quic_get_parameters(/* in */ quic_state *state, quic_transport_parameters *qp)
{
    int ret;

    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_get_parameters_caml(state, qp);
    caml_release_runtime_system();

    return ret;
}

#define Val_none Val_int(0)
#define Some_val(v) Field(v,0)

static int FFI_mitls_quic_get_exporter_caml(
  /* in */ quic_state *state,
  int early,
  quic_secret *secret,
  /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal2(result, tmp);

    result = caml_callback2_exn(*g_mitls_FFI_QuicGetExporter,
                                state->fstar_state, early ? Val_true : Val_false);

    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
        CAMLreturnT(int, 0);
    }

    // Secret not available
    if(result == Val_none)
    {
      *errmsg = "the requested secret is not yet available";
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

int MITLS_CALLCONV FFI_mitls_quic_get_exporter(
  /* in */ quic_state *state,
  int early,
  quic_secret *secret,
  /* out */ char **errmsg)
{
    int ret;

    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_get_exporter_caml(state, early, secret, errmsg);
    caml_release_runtime_system();

    return ret;
}

static int FFI_mitls_quic_get_ticket_caml(
  /* in */ quic_state *state,
  /* out */ quic_ticket *ticket,
  /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal2(result, tmp);

    result = caml_callback_exn(*g_mitls_FFI_QuicGetTicket,
                                state->fstar_state);

    if (Is_exception_result(result)) {
        report_caml_exception(result, errmsg);
        CAMLreturnT(int, 0);
    }
    if(result == Val_none)
      {
        *errmsg = "the requested ticket is not available";
        CAMLreturnT(int, 0);
      }
    result = Some_val(result);
    tmp = Field(result, 0);
    size_t len = caml_string_length(tmp);

    // Ticket too large
    if (len > MAX_TICKET_LEN)
      {
        *errmsg = "the ticket is too large";
        CAMLreturnT(int, 0);
      }
    
    ticket->len = len;
    memcpy(ticket->ticket, String_val(tmp), len);
    CAMLreturnT(int, 1);
}

int MITLS_CALLCONV FFI_mitls_quic_get_ticket(
  /* in */ quic_state *state,
  quic_ticket *ticket,
  /* out */ char **errmsg)
{
    int ret;

    caml_acquire_runtime_system();
    ret = FFI_mitls_quic_get_ticket_caml(state, ticket, errmsg);
    caml_release_runtime_system();

    return ret;
}

void MITLS_CALLCONV FFI_mitls_quic_free(quic_state *state)
{
    if (state) {
        caml_acquire_runtime_system();
        caml_remove_generational_global_root(&state->fstar_state);
        caml_release_runtime_system();
        state->fstar_state = 0;
        free(state);
    }
}

#include <stdio.h>
#include <memory.h>
#include <sys/stat.h>
#include <caml/callback.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/printexc.h>
#include "mitlsffi.h"

#define MITLS_FFI_LIST \
  MITLS_FFI_ENTRY(Config) \
  MITLS_FFI_ENTRY(PrepareClientHello) \
  MITLS_FFI_ENTRY(HandleServerHello) \
  MITLS_FFI_ENTRY(HandleCertificateVerify12) \
  MITLS_FFI_ENTRY(HandleServerKeyExchange) \
  MITLS_FFI_ENTRY(HandleServerHelloDone) \
  MITLS_FFI_ENTRY(PrepareClientKeyExchange) \
  MITLS_FFI_ENTRY(PrepareChangeCipherSpec) \
  MITLS_FFI_ENTRY(PrepareHandshake) \
  MITLS_FFI_ENTRY(HandleChangeCipherSpec) \
  MITLS_FFI_ENTRY(HandleServerFinished) \
  MITLS_FFI_ENTRY(PrepareSend) \
  MITLS_FFI_ENTRY(HandleReceive) \
  MITLS_FFI_ENTRY(Connect13) \
  MITLS_FFI_ENTRY(PrepareSend13) \
  MITLS_FFI_ENTRY(HandleReceive13) \

 
// Pointers to ML code.  Initialized in FFI_mitls_init().  Invoke via caml_callback()
#define MITLS_FFI_ENTRY(x) value* g_mitls_FFI_##x;
MITLS_FFI_LIST
#undef MITLS_FFI_ENTRY

int FFI_mitls_handle_simple(value* f, /* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, char **outmsg, char **errmsg);

typedef struct {
    char *out_name;
    char *err_name;
    int fd_out_old;
    int fd_err_old;
    int fd_out_new;
    int fd_err_new;
} mitls_redirect;

//
// Initialize miTLS.
//
//  Called once ahead of using miTLS
//
//  Returns:  0 for error, nonzero for success
//
int  FFI_mitls_init(void)
{
    char*Argv[2];
    value str;
    value ret;
    
    // Build a stub argv[] to satisfy caml_Startup()
    Argv[0] = "";
    Argv[1] = NULL;
    
    // Initialize the OCaml runtime
    caml_startup(Argv);
    
    // Bind to functions registered via Callback.register from ML
#define MITLS_FFI_ENTRY(x) \
    g_mitls_FFI_##x = caml_named_value("MITLS_FFI_" # x); \
    if (!g_mitls_FFI_##x) { \
        printf("Failed to bind to Caml callback MITLS_FFI_" # x "\n"); \
        return 0; \
    }
 MITLS_FFI_LIST  
 #undef MITLS_FFI_ENTRY
    
    return 1; // success
}

void FFI_mitls_cleanup(void)
{
#define MITLS_FFI_ENTRY(x) \
    g_mitls_FFI_##x = NULL;
 MITLS_FFI_LIST  
 #undef MITLS_FFI_ENTRY
}

char * read_stdio_file(int fd)
{
    struct stat st;
    char *data;
    
    fstat(fd, &st);
    // If no data was written, or a huge amount of data was written, ignore the file.
    if (st.st_size == 0 || st.st_size > 10*1024*1024) {
        return NULL;
    }
    
    lseek(fd, SEEK_SET, 0);
    data = malloc(st.st_size + 1); // The +1 is safe from integer overflow due to the above size check
    if (!data) {
        return NULL;
    }
    read(fd, data, st.st_size);
    data[st.st_size] = '\0'; // Null-terminate into a C string
    
    return data;
}

void restore_stdio(/* in */ mitls_redirect *r, /* out */ char **outmsg, /* out */ char **errmsg)
{
    char *msg;
    int result;
    
    *outmsg = NULL;
    *errmsg = NULL;
 
    if (r->fd_out_new == -1) {
        return;
    }
    
    fflush(stdout);
    fflush(stderr);
    
    // Restore stdout/stderr back to their original files
    dup2(r->fd_out_old, STDOUT_FILENO);
    dup2(r->fd_err_old, STDERR_FILENO);
    
    msg = read_stdio_file(r->fd_out_new);
    if (msg) {
        *outmsg = msg;
    }
    close(r->fd_out_new);
    result = unlink(r->out_name);
    if (result != 0) {
        fprintf(stderr, "unlink %s failed errno=%d ", r->out_name, errno); perror("failed");
    }
    free(r->out_name);
    
    msg = read_stdio_file(r->fd_err_new);
    if (msg) {
        *errmsg = msg;
    }
    close(r->fd_err_new);
    result = unlink(r->err_name);
    if (result != 0) {
        fprintf(stderr, "unlink %s failed errno=%d ", r->out_name, errno); perror("failed");
    }
    free(r->err_name);
}


void redirect_stdio(/* out */ mitls_redirect *r)
{
    int fdout;
    int fderr;
    static const char template[] = "/mitlscurlXXXXXX";
    char *tmp;
    char *out_name;
    char *err_name;
    size_t tmp_len;
    
    // Assume failure
    r->fd_out_new = -1;
    r->fd_err_new = -1;
    
    fflush(stdout);
    fflush(stderr);
    
    tmp = getenv("TMP");
    if (!tmp) {
        tmp = getenv("TEMP");
        if (!tmp) {
            tmp = ".";
        }
    }
    
    tmp_len = strlen(tmp);
    out_name = (char*)malloc(tmp_len + sizeof(template));
    if (!out_name) {
        return;
    }
    strcpy(out_name, tmp);
    strcpy(out_name+tmp_len, template);
    
    err_name = strdup(out_name);
    if (!err_name) {
        free(out_name);
        return;
    }

    // Create temp files
    fdout = mkstemp(out_name);
    if (fdout == -1) {
        free(out_name);
        free(err_name);
        return;
    }
    fderr = mkstemp(err_name);
    if (fderr == -1) {
        close(fdout);
        free(out_name);
        free(err_name);
        return;
    }
    r->fd_out_new = fdout;
    r->fd_err_new = fderr;
    r->out_name = out_name;
    r->err_name = err_name;
    
    // Capture current stdout/stderr
    r->fd_out_old = dup(STDOUT_FILENO);
    r->fd_err_old = dup(STDERR_FILENO);
    
    // Redirect stdout and stderr to the temp files
    dup2(fdout, STDOUT_FILENO);
    dup2(fderr, STDERR_FILENO);
}

#define C_ASSERT(e) typedef char __C_ASSERT__[(e)?1:-1]
C_ASSERT(sizeof(size_t) == sizeof(value));

void FFI_mitls_config(size_t *configptr, const char *tls_version, const char *host_name, char **outmsg, char **errmsg)
{
    CAMLlocal3(config, version, host);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    version = caml_copy_string(tls_version);  
    host = caml_copy_string(host_name);
    config = caml_callback2_exn(*g_mitls_FFI_Config, version, host);
    if (Is_exception_result(config)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(config)));
        *configptr = 0;
    } else {
        value * heapconfig;
        
        // Allocate space on the heap, to store an OCaml value
        heapconfig = (value*)malloc(sizeof(value));
        if (heapconfig == NULL) {
            *configptr = 0;
        } else {
            // Tell the OCaml GC about the heap address, so it is treated
            // as a GC root, keeping the config object live.
            *heapconfig = config; 
            caml_register_generational_global_root(heapconfig);
            *configptr = (size_t)heapconfig;
        }
    }
    
    restore_stdio(&r, outmsg, errmsg);
}

void FFI_mitls_release_value(size_t *v)
{
    if (v && *v) {
        value* pv = *(value**)v;
        // Remove the root from the OCaml GC tracker, so the object can be collected.
        caml_remove_generational_global_root(pv);
        free(pv);
        *v = 0;
    }
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

void FFI_mitls_free_packet(void *packet)
{
    free(packet);
}

void FFI_mitls_free_msg(char *msg)
{
    free(msg);
}

void * FFI_mitls_prepare_simple(value *f, /* in out */ size_t *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    value* pstate = *(value**)state;
    value state_value = *pstate;
    void *p = NULL;
    CAMLparam1(state_value);
    CAMLlocal1(ret);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
  
    ret = caml_callback_exn(*f, state_value);
    if (Is_exception_result(ret)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(ret)));
        p = NULL;
    } else {
        // The return value is a tuple containing the packet and the new config object
        *pstate = Field(ret, 1);
        p = copypacket(Field(ret, 0), packet_size);
    }
    restore_stdio(&r, outmsg, errmsg);
    
    CAMLreturnT(void*,p);
}

void * FFI_mitls_prepare_client_hello(/* in out */ size_t *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    void *p;
    p = FFI_mitls_prepare_simple(g_mitls_FFI_PrepareClientHello, state, packet_size, outmsg, errmsg);
    return p;
}

int FFI_mitls_handle_simple(value* f, /* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    value* pstate = *(value**)state;
    value state_value = *pstate;
    int ret = 0;
    CAMLparam1(state_value);
    CAMLlocal3(header_value, record_value, result);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);

    header_value = caml_alloc_string(header_size);
    memcpy(Bp_val(header_value), header, header_size);
    
    record_value = caml_alloc_string(record_size);
    memcpy(Bp_val(record_value), record, record_size);
    
    result = caml_callback3_exn(*f, state_value, header_value, record_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        ret = 0;
    } else {
        // The return is a just the updated state
        *pstate = result;
        ret = 1;
    }
    restore_stdio(&r, outmsg, errmsg);
    
    CAMLreturnT(int, ret);
}


int FFI_mitls_handle_server_hello(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, char **outmsg, char **errmsg)
{
    int ret;
    ret = FFI_mitls_handle_simple(g_mitls_FFI_HandleServerHello, state, header, header_size, record, record_size, outmsg, errmsg);
    return ret;
}

int FFI_mitls_handle_certificate_verify12(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, char **outmsg, char **errmsg)
{
    int ret;
    ret = FFI_mitls_handle_simple(g_mitls_FFI_HandleCertificateVerify12, state, header, header_size, record, record_size, outmsg, errmsg);
    return ret;
}

int FFI_mitls_handle_server_key_exchange(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, char **outmsg, char **errmsg)
{
    int ret;
    ret = FFI_mitls_handle_simple(g_mitls_FFI_HandleServerKeyExchange, state, header, header_size, record, record_size, outmsg, errmsg);
    return ret;
}

int FFI_mitls_handle_server_hello_done(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, char **outmsg, char **errmsg)
{
    int ret;
    ret = FFI_mitls_handle_simple(g_mitls_FFI_HandleServerHelloDone, state, header, header_size, record, record_size, outmsg, errmsg);
    return ret;
}

void * FFI_mitls_prepare_client_key_exchange(/* in out */ size_t *state, /* out */ size_t *packet_size, char **outmsg, char **errmsg)
{
    void *p;
    p = FFI_mitls_prepare_simple(g_mitls_FFI_PrepareClientKeyExchange, state, packet_size, outmsg, errmsg);
    return p;
}

void * FFI_mitls_prepare_change_cipher_spec(/* in out */ size_t *state, /* out */ size_t *packet_size, char **outmsg, char **errmsg)
{
    void *p;
    p = FFI_mitls_prepare_simple(g_mitls_FFI_PrepareChangeCipherSpec, state, packet_size, outmsg, errmsg);
    return p;
}

void * FFI_mitls_prepare_handshake(/* in out */ size_t *state, /* out */ size_t *packet_size, char **outmsg, char **errmsg)
{
    void *p;
    p = FFI_mitls_prepare_simple(g_mitls_FFI_PrepareHandshake, state, packet_size, outmsg, errmsg);
    return p;
}

int FFI_mitls_handle_change_cipher_spec(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, char **outmsg, char **errmsg)
{
    int ret;
    ret = FFI_mitls_handle_simple(g_mitls_FFI_HandleChangeCipherSpec, state, header, header_size, record, record_size, outmsg, errmsg);
    return ret;
}

int FFI_mitls_handle_server_finished(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, char **outmsg, char **errmsg)
{
    int ret;
    ret = FFI_mitls_handle_simple(g_mitls_FFI_HandleServerFinished, state, header, header_size, record, record_size, outmsg, errmsg);
    return ret;
}


void * FFI_mitls_prepare_send(/* in out */ size_t *state, const void* buffer, size_t buffer_size, /* out */ size_t *packet_size, char **outmsg, char **errmsg)
{
    value* pstate = *(value**)state;
    value state_value = *pstate;
    void *p = NULL;
    CAMLparam1(state_value);
    CAMLlocal2(buffer_value, result);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    buffer_value = caml_alloc_string(buffer_size);
    memcpy(Bp_val(buffer_value), buffer, buffer_size);
    
    result = caml_callback2_exn(*g_mitls_FFI_PrepareSend, state_value, buffer_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        p = NULL;
    } else {
        // The return the plaintext data
        p = copypacket(result, packet_size);
    }
    
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(void*, p);
    
}

void * FFI_mitls_handle_receive(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ size_t *packet_size, char **outmsg, char **errmsg)
{
    value* pstate = *(value**)state;
    value state_value = *pstate;
    void *p = NULL;
    CAMLparam1(state_value);
    CAMLlocal3(header_value, record_value, result);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);

    header_value = caml_alloc_string(header_size);
    memcpy(Bp_val(header_value), header, header_size);
    
    record_value = caml_alloc_string(record_size);
    memcpy(Bp_val(record_value), record, record_size);
    
    result = caml_callback3_exn(*g_mitls_FFI_HandleReceive, state_value, header_value, record_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        p = NULL;
    } else {
        // Return the plaintext data
        p = copypacket(result, packet_size);
    }
    
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(void*, p);
}

CAMLprim value ocaml_send_tcp(value cookie, value bytes)
{
    mlsize_t buffer_size;
    char *buffer;
    int retval;
    size_t c = Long_val(cookie);
    struct _FFI_mitls_callbacks *callbacks = (struct _FFI_mitls_callbacks *)c;
    CAMLparam2(cookie, bytes);

    buffer = Bp_val(bytes);
    buffer_size = caml_string_length(bytes);
    
    retval = (*callbacks->send)(callbacks, buffer, buffer_size);
    
    return Val_int(retval);
}

CAMLprim value ocaml_recv_tcp(value cookie, value bytes)
{
    mlsize_t buffer_size;
    char *buffer;
    ssize_t retval;
    size_t c = Long_val(cookie);
    struct _FFI_mitls_callbacks *callbacks = (struct _FFI_mitls_callbacks *)c;
    CAMLparam2(cookie, bytes);
    
    buffer = Bp_val(bytes);
    buffer_size = caml_string_length(bytes);
    
    retval = (*callbacks->recv)(callbacks, buffer, buffer_size);
    
    return Val_int(retval);
}

int FFI_mitls_connect13(struct _FFI_mitls_callbacks *callbacks, /* out */ size_t *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    value* pstate = *(value**)state;
    value state_value = *pstate;
    CAMLparam1(state_value);
    CAMLlocal1(result);
    int ret;
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    result = caml_callback2_exn(*g_mitls_FFI_Connect13, state_value, Val_long((size_t)callbacks));
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        ret = 0;
    } else {
        *pstate = result;
        ret = 1;
        
    }
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(int, ret);
}

void * FFI_mitls_prepare_send13(/* in out */ size_t *state, const void* buffer, size_t buffer_size, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    value* pstate = *(value**)state;
    value state_value = *pstate;
    void *p = NULL;
    CAMLparam1(state_value);
    CAMLlocal2(buffer_value, result);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    buffer_value = caml_alloc_string(buffer_size);
    memcpy(Bp_val(buffer_value), buffer, buffer_size);
    
    result = caml_callback2_exn(*g_mitls_FFI_PrepareSend13, state_value, buffer_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        p = NULL;
    } else {
        // The return the plaintext data
        p = copypacket(result, packet_size);
    }
    
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(void*, p);    
}

void * FFI_mitls_handle_receive13(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    value* pstate = *(value**)state;
    value state_value = *pstate;
    void *p = NULL;
    CAMLparam1(state_value);
    CAMLlocal3(header_value, record_value, result);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);

    header_value = caml_alloc_string(header_size);
    memcpy(Bp_val(header_value), header, header_size);
    
    record_value = caml_alloc_string(record_size);
    memcpy(Bp_val(record_value), record, record_size);
    
    result = caml_callback3_exn(*g_mitls_FFI_HandleReceive13, state_value, header_value, record_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        p = NULL;
    } else {
        // Return the plaintext data
        p = copypacket(result, packet_size);
    }
    
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(void*, p);
}

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
  MITLS_FFI_ENTRY(Connect12) \
  MITLS_FFI_ENTRY(PrepareSend12) \
  MITLS_FFI_ENTRY(HandleReceive12) \
  MITLS_FFI_ENTRY(Connect13) \
  MITLS_FFI_ENTRY(PrepareSend13) \
  MITLS_FFI_ENTRY(HandleReceive13) \
 
// Pointers to ML code.  Initialized in FFI_mitls_init().  Invoke via caml_callback()
#define MITLS_FFI_ENTRY(x) value* g_mitls_FFI_##x;
MITLS_FFI_LIST
#undef MITLS_FFI_ENTRY

typedef struct mitls_state {
    value fstar_state;    // a GC root representing an F*-side state object
    value *connect_callback;
    value *prepare_send_callback;
    value *handle_receive_callback;
} mitls_state;

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

// Called by the host app to configure miTLS ahead of creating a connection
int FFI_mitls_configure(mitls_state **state, const char *tls_version, const char *host_name, char **outmsg, char **errmsg)
{
    int ret = 0;
    CAMLlocal3(config, version, host);
    mitls_redirect r;

    *state = NULL;
    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    version = caml_copy_string(tls_version);  
    host = caml_copy_string(host_name);
    config = caml_callback2_exn(*g_mitls_FFI_Config, version, host);
    if (Is_exception_result(config)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(config)));
    } else {
        mitls_state * s;
        
        // Allocate space on the heap, to store an OCaml value
        s = (mitls_state*)malloc(sizeof(mitls_state));
        if (s) {
            // Tell the OCaml GC about the heap address, so it is treated
            // as a GC root, keeping the config object live.
            s->fstar_state = config; 
            caml_register_generational_global_root(&s->fstar_state);
            if (strcmp(tls_version, "1.3") == 0) {
                s->connect_callback = g_mitls_FFI_Connect13;
                s->prepare_send_callback = g_mitls_FFI_PrepareSend13;
                s->handle_receive_callback = g_mitls_FFI_HandleReceive13;
            } else {
                s->connect_callback = g_mitls_FFI_Connect12;
                s->prepare_send_callback = g_mitls_FFI_PrepareSend12;
                s->handle_receive_callback = g_mitls_FFI_HandleReceive12;
            }
            *state = s;
            ret = 1;
        }
    }
    
    restore_stdio(&r, outmsg, errmsg);
    return ret;
}

// Called by the host app to free a mitls_state allocated by FFI_mitls_configure()
void FFI_mitls_close(mitls_state *state)
{
    if (state) {
        caml_remove_generational_global_root(&state->fstar_state);
        state->fstar_state = 0;
        free(state);
    }
}

void FFI_mitls_free_msg(char *msg)
{
    free(msg);
}

void FFI_mitls_free_packet(void *packet)
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
    size_t c = Long_val(cookie);
    struct _FFI_mitls_callbacks *callbacks = (struct _FFI_mitls_callbacks *)c;
    CAMLparam2(cookie, bytes);

    buffer = Bp_val(bytes);
    buffer_size = caml_string_length(bytes);
    
    retval = (*callbacks->send)(callbacks, buffer, buffer_size);
    
    return Val_int(retval);
}

// Called from FStar code to receive via TCP
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

// Called by the host app to create a TLS connection.
int FFI_mitls_connect(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLlocal1(result);
    int ret;
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    result = caml_callback2_exn(*state->connect_callback, state->fstar_state, Val_long((size_t)callbacks));
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        ret = 0;
    } else {
        state->fstar_state = result;
        ret = 1;
        
    }
    restore_stdio(&r, outmsg, errmsg);
    return ret;
}

// Called by the host app to encode a cleartext packet for transmission
void * FFI_mitls_prepare_send(/* in */ mitls_state *state, const void* buffer, size_t buffer_size, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    void *p = NULL;
    CAMLlocal2(buffer_value, result);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    buffer_value = caml_alloc_string(buffer_size);
    memcpy(Bp_val(buffer_value), buffer, buffer_size);
    
    result = caml_callback2_exn(*state->prepare_send_callback, state->fstar_state, buffer_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        p = NULL;
    } else {
        // The return the plaintext data
        p = copypacket(result, packet_size);
    }
    
    restore_stdio(&r, outmsg, errmsg);
    return p;
}

// Called by the host app to decode a packet into cleartext
void * FFI_mitls_handle_receive(/* in */ mitls_state *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    void *p = NULL;
    CAMLlocal3(header_value, record_value, result);
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);

    header_value = caml_alloc_string(header_size);
    memcpy(Bp_val(header_value), header, header_size);
    
    record_value = caml_alloc_string(record_size);
    memcpy(Bp_val(record_value), record, record_size);
    
    result = caml_callback3_exn(*state->handle_receive_callback, state->fstar_state, header_value, record_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        p = NULL;
    } else {
        // Return the plaintext data
        p = copypacket(result, packet_size);
    }
    
    restore_stdio(&r, outmsg, errmsg);
    return p;
}


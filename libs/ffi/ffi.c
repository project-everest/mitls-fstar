#include <stdio.h>
#include <memory.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/cdefs.h>
#if __APPLE__ 
#include <sys/errno.h> // OS/X only provides include/sys/errno.h
#else
#include <errno.h> // MinGW only provides include/errno.h
#endif
#include <caml/callback.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/printexc.h>
#include "mitlsffi.h"

#define REDIRECT_STDIO 1

#define MITLS_FFI_LIST \
  MITLS_FFI_ENTRY(Config) \
  MITLS_FFI_ENTRY(Connect) \
  MITLS_FFI_ENTRY(Send) \
  MITLS_FFI_ENTRY(Recv)
 
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

// Support temporary redirection of stdout and stderr
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

// Read the contents of a file into memory.  The caller is responsible for freeing
// the memory via free().
char * read_stdio_file(int fd)
{
    struct stat st;
    char *data;
    ssize_t result;
    
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
    result = read(fd, data, st.st_size);
    if (result == -1) {
        free(data);
        return NULL;
    }
    data[st.st_size] = '\0'; // Null-terminate into a C string
    
    return data;
}

void restore_stdio(/* in */ mitls_redirect *r, /* out */ char **outmsg, /* out */ char **errmsg)
{
#if REDIRECT_STDIO
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
#else
    r->fd_out_new = -1;
    *outmsg = NULL;
    *errmsg = NULL;
#endif
}


void redirect_stdio(/* out */ mitls_redirect *r)
{
#if REDIRECT_STDIO
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
#else
    r->fd_out_new = -1;
    r->fd_err_new = -1;
#endif    
}

// Called by the host app to configure miTLS ahead of creating a connection
int FFI_mitls_configure(mitls_state **state, const char *tls_version, const char *host_name, char **outmsg, char **errmsg)
{
    CAMLparam0();
    CAMLlocal3(config, version, host);
    int ret = 0;
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
            *state = s;
            ret = 1;
        }
    }
    restore_stdio(&r, outmsg, errmsg);
    
    CAMLreturnT(int,ret);
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
    struct _FFI_mitls_callbacks *callbacks;

    CAMLparam2(cookie, bytes);
    
    callbacks = (struct _FFI_mitls_callbacks *)ValueToPtr(cookie);
    buffer = Bp_val(bytes);
    buffer_size = caml_string_length(bytes);
    
    retval = (*callbacks->send)(callbacks, buffer, buffer_size);
    
    CAMLreturn(Val_int(retval));
}

// Called from FStar code to receive via TCP
CAMLprim value ocaml_recv_tcp(value cookie, value bytes)
{
    mlsize_t buffer_size;
    char *buffer;
    ssize_t retval;
    struct _FFI_mitls_callbacks *callbacks;
    
    CAMLparam2(cookie, bytes);
    
    callbacks = (struct _FFI_mitls_callbacks *)ValueToPtr(cookie);
    buffer = Bp_val(bytes);
    buffer_size = caml_string_length(bytes);
    
    retval = (*callbacks->recv)(callbacks, buffer, buffer_size);
    
    CAMLreturn(Val_int(retval));
}

// Called by the host app to create a TLS connection.
int FFI_mitls_connect(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal1(result);
    int ret;
    mitls_redirect r;
    
    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    result = caml_callback2_exn(*g_mitls_FFI_Connect, state->fstar_state, PtrToValue(callbacks));
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        ret = 0;
    } else {
        // Connect returns back (Connection.connection * int)
        value connection = Field(result,0);
        ret = Int_val(Field(result,1));
        if (ret == 0) {
            caml_modify_generational_global_root(&state->fstar_state, connection);
            ret = 1;
        } else {
            printf("FFI_mitls_connect failed with miTLS error %d\n", ret);
            ret = 0;
        }
        // The result is an integer.  How to deduce the value of 'c' needed for
        // subsequent FFI.read and FFI.write is TBD.
        
    }
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(int,ret);
}

// Called by the host app transmit a packet
int FFI_mitls_send(/* in */ mitls_state *state, const void* buffer, size_t buffer_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal2(buffer_value, result);
    int ret = 0;
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);
    
    buffer_value = caml_alloc_string(buffer_size);
    memcpy(Bp_val(buffer_value), buffer, buffer_size);
    
    result = caml_callback2_exn(*g_mitls_FFI_Send, state->fstar_state, buffer_value);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        ret = 0;
    } else {
        ret = 1;
    }
    
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(int,ret);
}

// Called by the host app to receive a packet
void * FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg)
{
    CAMLparam0();
    CAMLlocal1(result);
    void *p = NULL;
    mitls_redirect r;

    *outmsg = NULL;
    *errmsg = NULL;
    redirect_stdio(&r);

    result = caml_callback_exn(*g_mitls_FFI_Recv, state->fstar_state);
    if (Is_exception_result(result)) {
        printf("Exception!  %s\n", caml_format_exception(Extract_exception(result)));
        p = NULL;
    } else {
        // Return the plaintext data
        p = copypacket(result, packet_size);
    }
    
    restore_stdio(&r, outmsg, errmsg);
    CAMLreturnT(void*,p);
}


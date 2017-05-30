#ifndef HEADER_MITLS_FFI_H
#define HEADER_MITLS_FFI_H

#if defined(_MSC_VER)  // Visual Studio - always use __cdecl keyword
  #define MITLS_CALLCONV __cdecl
#elif defined(__cdecl) // GCC/MinGW targeting Windows 32-bit - use the __cdecl macro
  #define MITLS_CALLCONV __cdecl
#else                  // Targeting other platforms - use the ambient calling convention
  #define MITLS_CALLCONV
#endif

typedef struct mitls_state mitls_state;

// Functions exported from libmitls.dll
//   Functions returning 'int' return 0 for failure, or nonzero for success

// Perform one-time initialization
extern int MITLS_CALLCONV FFI_mitls_init(void);

// Perform one-time termination
extern void MITLS_CALLCONV FFI_mitls_cleanup(void);

// Configure miTLS ahead of connecting
extern int MITLS_CALLCONV FFI_mitls_configure(/* out */ mitls_state **state, const char *tls_version, const char *host_name, /* out */ char **outmsg, /* out */ char **errmsg);

// Set configuration options ahead of connecting
extern int MITLS_CALLCONV FFI_mitls_configure_cert_chain_file(/* in */ mitls_state *state, const char * file);
extern int MITLS_CALLCONV FFI_mitls_configure_private_key_file(/* in */ mitls_state *state, const char * file);
extern int MITLS_CALLCONV FFI_mitls_configure_ca_file(/* in */ mitls_state *state, const char * file);
extern int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char * cs);
extern int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char * sa);
extern int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char * ng);

// Close a miTLS session - either after configure or connect
extern void MITLS_CALLCONV FFI_mitls_close(/* in */ mitls_state *state);

// Callbacks from miTLS to the host application, to send and receive TCP
struct _FFI_mitls_callbacks;
typedef int (*MITLS_CALLCONV pfn_FFI_send)(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size);
typedef int (*MITLS_CALLCONV pfn_FFI_recv)(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size);
struct _FFI_mitls_callbacks {
    pfn_FFI_send send;
    pfn_FFI_recv recv;
};

// Connect to a TLS server
extern int MITLS_CALLCONV FFI_mitls_connect(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);

// Act as a TLS server to a client
extern int MITLS_CALLCONV FFI_mitls_accept_connected(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);

// Send a message
extern int MITLS_CALLCONV FFI_mitls_send(/* in */ mitls_state *state, const void* buffer, size_t buffer_size,
                            /* out */ char **outmsg, /* out */ char **errmsg); // Returns NULL for failure, or a TCP packet to be sent then freed with FFI_mitls_free_packet()
                                    
// Receive a message
extern void *MITLS_CALLCONV FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size, 
                               /* out */ char **outmsg, /* out */ char **errmsg);     // Returns NULL for failure, a plaintext packet to be freed with FFI_mitls_free_packet()

// Free a packet returned FFI_mitls_receive();
extern void MITLS_CALLCONV FFI_mitls_free_packet(void* packet);

// Free an outmsg or errmsg
extern void MITLS_CALLCONV FFI_mitls_free_msg(char *msg);

// Register the calling thread, so it can call miTLS.  Returns 1 for success, 0 for error.
extern int MITLS_CALLCONV FFI_mitls_thread_register(void);

// Unregister the calling thread, so it can no longer call miTLS.  Returns 1 for success, 0 for error.
extern int MITLS_CALLCONV FFI_mitls_thread_unregister(void);

#endif // HEADER_MITLS_FFI_H
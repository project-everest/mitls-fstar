#ifndef HEADER_MITLS_FFI_H
#define HEADER_MITLS_FFI_H

typedef struct mitls_state mitls_state;

// Functions exported from libmitls.dll
//   Functions returning 'int' return 0 for failure, or nonzero for success

// Perform one-time initialization
extern int  FFI_mitls_init(void);

// Perform one-team termination
extern void FFI_mitls_cleanup(void);

// Configure miTLS ahead of connecting
extern int   FFI_mitls_configure(/* out */ mitls_state **state, const char *tls_version, const char *host_name, /* out */ char **outmsg, /* out */ char **errmsg);

// Close a miTLS session - either after configure or connect
extern void FFI_mitls_close(/* in */ mitls_state *state);

// Callbacks from miTLS to the host application, to send and receive TCP, invoked within FFI_mitls_connect() only
struct _FFI_mitls_callbacks;
typedef int (*pfn_FFI_send)(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size);
typedef int (*pfn_FFI_recv)(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size);
struct _FFI_mitls_callbacks {
    pfn_FFI_send send;
    pfn_FFI_recv recv;
};

// Connect to a TLS server
extern int   FFI_mitls_connect(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);

// Prepare a plaintext packet for send over a TLS session
extern void *FFI_mitls_prepare_send(/* in */ mitls_state *state, const void* buffer, size_t buffer_size, /* out */ size_t *packet_size, 
                                    /* out */ char **outmsg, /* out */ char **errmsg); // Returns NULL for failure, or a TCP packet to be sent then freed with FFI_mitls_free_packet()
                                    
// Decrypt a packet received over a TLS session
extern void *FFI_mitls_handle_receive(/* in */ mitls_state *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ size_t *packet_size, 
                                      /* out */ char **outmsg, /* out */ char **errmsg);     // Returns NULL for failure, a plaintext packet to be freed with FFI_mitls_free_packet()

// Free a packet returned from FFI_mitls_prepare_send() or FFI_mitls_handle_receive();
extern void FFI_mitls_free_packet(void* packet);

// Free an outmsg or errmsg
extern void FFI_mitls_free_msg(char *msg);

#endif // HEADER_MITLS_FFI_H
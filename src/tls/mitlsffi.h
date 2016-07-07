#ifndef HEADER_MITLS_FFI_H
#define HEADER_MITLS_FFI_H

// Functions exported from libmitls.dll
//   Functions returning 'int' return 0 for failure, or nonzero for success
extern int  FFI_mitls_init(void);
extern void FFI_mitls_cleanup(void);
extern void FFI_mitls_config(size_t *stateptr, const char *tls_version, const char *host_name, 
                             /* out */ char **outmsg, /* out */ char **errmsg);
extern void FFI_mitls_release_value(size_t *value);
extern void FFI_mitls_free_packet(void *packet);
extern void FFI_mitls_free_msg(char *msg);
extern void * FFI_mitls_prepare_client_hello(/* in out */ size_t *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg); // Returns NULL for failure, or a TCP packet to be sent then freed with FFI_mitls_free_packet()
extern int FFI_mitls_handle_server_hello(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern int FFI_mitls_handle_encrypted_extensions(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern int FFI_mitls_handle_certificate_verify12(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern int FFI_mitls_handle_server_key_exchange(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern int FFI_mitls_handle_server_hello_done(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern void * FFI_mitls_prepare_client_key_exchange(/* in out */ size_t *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg); // Returns NULL for failure, or a TCP packet to be sent then freed with FFI_mitls_free_packet()
extern void * FFI_mitls_prepare_change_cipher_spec(/* in out */ size_t *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern void * FFI_mitls_prepare_handshake(/* in out */ size_t *state, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern int FFI_mitls_handle_change_cipher_spec(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg);
extern int FFI_mitls_handle_server_finished(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ char **outmsg, /* out */ char **errmsg);

extern void * FFI_mitls_prepare_send(/* in out */ size_t *state, const void* buffer, size_t buffer_size, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg); // Returns NULL for failure, or a TCP packet to be sent then freed with FFI_mitls_free_packet()
extern void * FFI_mitls_handle_receive(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ size_t *packet_size, /* out */ char **outmsg, /* out */ char **errmsg);     // Returns NULL for failure, a plaintext packet to be freed with FFI_mitls_free_packet()

struct _FFI_mitls_callbacks;
typedef int (*pfn_FFI_send)(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size);
typedef int (*pfn_FFI_recv)(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size);

struct _FFI_mitls_callbacks {
    pfn_FFI_send send;
    pfn_FFI_recv recv;
};

extern int FFI_mitls_connect13(struct _FFI_mitls_callbacks *callbacks, /* out */ size_t *stateptr, 
                               /* out */ char **outmsg, /* out */ char **errmsg);
extern void * FFI_mitls_prepare_send13(/* in out */ size_t *state, const void* buffer, size_t buffer_size, /* out */ size_t *packet_size, 
                                       /* out */ char **outmsg, /* out */ char **errmsg); // Returns NULL for failure, or a TCP packet to be sent then freed with FFI_mitls_free_packet()
extern void * FFI_mitls_handle_receive13(/* in out */ size_t *state, char* header, size_t header_size, char *record, size_t record_size, /* out */ size_t *packet_size, 
                                         /* out */ char **outmsg, /* out */ char **errmsg);     // Returns NULL for failure, a plaintext packet to be freed with FFI_mitls_free_packet()


#endif // HEADER_MITLS_FFI_H
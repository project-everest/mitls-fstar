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
typedef struct quic_state quic_state;

#define MAX_TICKET_LEN 1020
#define MAX_SESSION_LEN 256
typedef struct {
  size_t ticket_len;
  char ticket[MAX_TICKET_LEN];
  size_t session_len;
  char session[MAX_SESSION_LEN];
} mitls_ticket;

typedef enum {
  TLS_hash_MD5 = 0,
  TLS_hash_SHA1 = 1,
  TLS_hash_SHA224 = 2,
  TLS_hash_SHA256 = 3,
  TLS_hash_SHA384 = 4,
  TLS_hash_SHA512 = 5
} mitls_hash;

typedef enum {
  TLS_aead_AES_128_GCM = 0,
  TLS_aead_AES_256_GCM = 1,
  TLS_aead_CHACHA20_POLY1305 = 2
} mitls_aead;

// Agile secret with static allocation
typedef struct {
  mitls_hash hash;
  mitls_aead ae;
  char secret[64]; // Max possible size, flat allocation
} mitls_secret;

// Functions exported from libmitls.dll
//   Functions returning 'int' return 0 for failure, or nonzero for success

// Perform one-time initialization
extern int MITLS_CALLCONV FFI_mitls_init(void);

// Perform one-time termination
extern void MITLS_CALLCONV FFI_mitls_cleanup(void);

// Configure miTLS ahead of connecting
extern int MITLS_CALLCONV FFI_mitls_configure(/* out */ mitls_state **state, const char *tls_version, const char *host_name, /* out */ char **outmsg, /* out */ char **errmsg);
extern int MITLS_CALLCONV FFI_mitls_set_ticket_key(const char *alg, const char *ticketkey, size_t klen);

// Set configuration options ahead of connecting
extern int MITLS_CALLCONV FFI_mitls_configure_cert_chain_file(/* in */ mitls_state *state, const char * file);
extern int MITLS_CALLCONV FFI_mitls_configure_private_key_file(/* in */ mitls_state *state, const char * file);
extern int MITLS_CALLCONV FFI_mitls_configure_ca_file(/* in */ mitls_state *state, const char * file);
extern int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char * cs);
extern int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char * sa);
extern int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char * ng);
extern int MITLS_CALLCONV FFI_mitls_configure_alpn(/* in */ mitls_state *state, const char *apl);
extern int MITLS_CALLCONV FFI_mitls_configure_early_data(/* in */ mitls_state *state, int enable_early_data);

// Close a miTLS session - either after configure or connect
extern void MITLS_CALLCONV FFI_mitls_close(/* in */ mitls_state *state);

// Callbacks from miTLS to the host application, to send and receive TCP
struct _FFI_mitls_callbacks;
typedef int (MITLS_CALLCONV *pfn_FFI_send)(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size);
typedef int (MITLS_CALLCONV *pfn_FFI_recv)(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size);
struct _FFI_mitls_callbacks {
    pfn_FFI_send send;
    pfn_FFI_recv recv;
};

// Connect to a TLS server
extern int MITLS_CALLCONV FFI_mitls_connect(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);

// Resume a previously-established ticket
extern int MITLS_CALLCONV FFI_mitls_resume(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket, /* out */ char **errmsg);

// Act as a TLS server to a client
extern int MITLS_CALLCONV FFI_mitls_accept_connected(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);

// Get the session ticket for resumption - returns 1 if a ticket has been successfuly stored
extern int MITLS_CALLCONV FFI_mitls_get_ticket(mitls_state *state, mitls_ticket *ticket, char **errmsg);

// Get the exporter secret (set early to true for the early exporter secret). Returns 1 if a secret was written
extern int MITLS_CALLCONV FFI_mitls_get_exporter(/* in */ mitls_state *state, int early, /* out */ mitls_secret *secret, /* out */ char **errmsg);

// Retrieve the server certificate after FFI_mitls_connect() completes
extern void *MITLS_CALLCONV FFI_mitls_get_cert(/* in */ mitls_state *state, /* out */ size_t *cert_size, /* out */ char **outmsg, /* out */ char **errmsg);

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

/*************************************************************************
* QUIC FFI
**************************************************************************/
// bugbug: what about offered_psk to create_client()?
// bugbug: rich results from process

typedef enum {
  TLS_would_block = 0,
  TLS_error_local = 1,
  TLS_error_alert = 2,
  TLS_client_early = 3,
  TLS_client_complete = 4,
  TLS_client_complete_with_early_data = 5,
  TLS_server_accept = 6,
  TLS_server_accept_with_early_data = 7,
  TLS_server_complete = 8,
  TLS_error_other = 0xffff
} quic_result;

typedef mitls_hash quic_hash;
typedef mitls_aead quic_aead;
typedef mitls_secret quic_secret;
typedef mitls_ticket quic_ticket;

// This length is somehow arbitrary
#define MAX_OTHERS_LEN 1024

typedef struct {
  unsigned int max_stream_data;
  unsigned int max_data;
  unsigned int max_stream_id;
  unsigned short idle_timeout;

  // The custom parameters are still in RFC wire format:
  // a sequence of (descriptor: 2; len: 2; data: len) bytes
  size_t others_len;
  char others[MAX_OTHERS_LEN];
} quic_transport_parameters;

typedef struct {
  // NULL terminated hostname (sent in SNI and used to validate certificate)
  int is_server;
  quic_transport_parameters qp;
  const char *cipher_suites; // Colon separated list of ciphersuite or NULL
  const char *signature_algorithms; // Colon separated list of signature schemes or NULL
  const char *named_groups; // Colon separated list of Diffie-Hellman groups or NULL
  int enable_0rtt; // Probably true for QUIC

  // only used by the client
  const char *host_name; // Client only, sent in SNI
  const char *ca_file; // Client only, used to validate server certificate
  quic_ticket server_ticket;

  // only used by the server
  const char *certificate_chain_file; // Server only
  const char *private_key_file; // Server only
  const char *ticket_enc_alg; // one of "AES128-GCM" "AES256-GCM" "CHACHA20-POLY1305", or NULL
  const char *ticket_key; // If NULL a random key will be sampled
  size_t ticket_key_len; // Should be 28 or 44, concatenation of key and static IV
} quic_config;


// pass 0 to leave any of the configuration values undefined
extern int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg, /* out */ char **errmsg);

extern quic_result MITLS_CALLCONV FFI_mitls_quic_process(/* in */ quic_state *state, /*in*/ char* inBuf, /*inout*/ size_t *pInBufLen, /*out*/ char *outBuf, /*inout*/ size_t *pOutBufLen, /* out */ char **errmsg);

extern int MITLS_CALLCONV FFI_mitls_quic_get_peer_parameters(/* in */ quic_state *state, /*out*/ quic_transport_parameters *qp, /* out */ char **errmsg);
extern int MITLS_CALLCONV FFI_mitls_quic_get_exporter(/* in */ quic_state *state, int early, /* out */ quic_secret *secret, /* out */ char **errmsg);
extern int MITLS_CALLCONV FFI_mitls_quic_get_ticket(/* in */ quic_state *state, /*out*/ quic_ticket *ticket , /* out */ char **errmsg);
extern void MITLS_CALLCONV FFI_mitls_quic_free(/* in */ quic_state *state);

#endif // HEADER_MITLS_FFI_H

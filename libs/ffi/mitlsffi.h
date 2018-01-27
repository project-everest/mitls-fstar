#ifndef HEADER_MITLS_FFI_H
#define HEADER_MITLS_FFI_H
#include <stdint.h>

#if defined(_MSC_VER)  // Visual Studio - always use __cdecl keyword
  #define MITLS_CALLCONV __cdecl
#elif defined(__cdecl) // GCC/MinGW targeting Windows 32-bit - use the __cdecl macro
  #define MITLS_CALLCONV __cdecl
#else                  // Targeting other platforms - use the ambient calling convention
  #define MITLS_CALLCONV
#endif

typedef struct mitls_state mitls_state;
typedef struct quic_state quic_state;

typedef struct {
  size_t ticket_len;
  const char *ticket;
  size_t session_len;
  const char *session;
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

typedef uint16_t mitls_signature_scheme;

// Agile secret with static allocation
typedef struct {
  mitls_hash hash;
  mitls_aead ae;
  char secret[64]; // Max possible size, flat allocation
} mitls_secret;

typedef void (MITLS_CALLCONV *pfn_FFI_ticket_cb)(void *cb_state, const char *sni, const mitls_ticket *ticket);

#define MAX_CHAIN_LEN 65536
#define MAX_SIGNATURE_LEN 8192
// Select a certificate based on the given SNI and list of signatures.
// Signature algorithms are represented as 16-bit integers using the TLS 1.3 RFC code points
typedef void* (MITLS_CALLCONV *pfn_FFI_cert_select_cb)(void *cb_state, const char *sni, const mitls_signature_scheme *sigalgs, size_t sigalgs_len, mitls_signature_scheme *selected);
// Write the certificate chain to buffer, returning the number of written bytes.
// The chain should be written by prefixing each certificate by its length encoded over 3 bytes
typedef size_t (MITLS_CALLCONV *pfn_FFI_cert_format_cb)(void *cb_state, const void *cert_ptr, char buffer[MAX_CHAIN_LEN]);
// Tries to sign and write the signature to sig, returning the signature size or 0 if signature failed
typedef size_t (MITLS_CALLCONV *pfn_FFI_cert_sign_cb)(void *cb_state, const void *cert_ptr, const mitls_signature_scheme sigalg, const char *tbs, size_t tbs_len, char *sig);
// Verifies that the chain (given in the same format as above) is valid, and that sig is a valid signature
// of tbs for sigalg using the public key stored in the leaf of the chain.
// N.B. this function must validate the chain (including applcation checks such as hostname matching)
typedef int (MITLS_CALLCONV *pfn_FFI_cert_verify_cb)(void *cb_state, const char* chain, size_t chain_len, const mitls_signature_scheme sigalg, const char *tbs, size_t tbs_len, char *sig, size_t sig_len);

typedef struct {
  pfn_FFI_cert_select_cb select;
  pfn_FFI_cert_format_cb format;
  pfn_FFI_cert_sign_cb sign;
  pfn_FFI_cert_verify_cb verify;
} mitls_cert_cb;

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
extern int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char * cs);
extern int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char * sa);
extern int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char * ng);
extern int MITLS_CALLCONV FFI_mitls_configure_alpn(/* in */ mitls_state *state, const char *apl);
extern int MITLS_CALLCONV FFI_mitls_configure_early_data(/* in */ mitls_state *state, uint32_t max_early_data);
extern int MITLS_CALLCONV FFI_mitls_configure_ticket_callback(mitls_state *state, void *cb_state, pfn_FFI_ticket_cb ticket_cb);
extern int MITLS_CALLCONV FFI_mitls_configure_cert_callbacks(mitls_state *state, void *cb_state, mitls_cert_cb *cert_cb);

// Close a miTLS session - either after configure or connect
extern void MITLS_CALLCONV FFI_mitls_close(/* in */ mitls_state *state);

// Callbacks from miTLS to the host application, to send and receive TCP
typedef int (MITLS_CALLCONV *pfn_FFI_send)(void* ctx, const void *buffer, size_t buffer_size);
typedef int (MITLS_CALLCONV *pfn_FFI_recv)(void *ctx, void *buffer, size_t buffer_size);

// Connect to a TLS server
extern int MITLS_CALLCONV FFI_mitls_connect(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);

// Resume a previously-established ticket
extern int MITLS_CALLCONV FFI_mitls_resume(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* in */ mitls_ticket *ticket, /* out */ char **errmsg);

// Act as a TLS server to a client
extern int MITLS_CALLCONV FFI_mitls_accept_connected(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);

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
  TLS_server_stateless_retry = 9,
  TLS_error_other = 0xffff
} quic_result;

typedef mitls_hash quic_hash;
typedef mitls_aead quic_aead;
typedef mitls_secret quic_secret;
typedef mitls_ticket quic_ticket;

typedef struct {
  size_t tp_len;
  const char* tp_data;
} quic_transport_parameters;

typedef struct {
  int is_server;
  const uint32_t *supported_versions;
  size_t supported_versions_len;
  quic_transport_parameters qp;

  const char *alpn; // Colon separated list of application-level protocols, or NULL
  const char *cipher_suites; // Colon separated list of ciphersuite or NULL
  const char *signature_algorithms; // Colon separated list of signature schemes or NULL
  const char *named_groups; // Colon separated list of Diffie-Hellman groups or NULL
  int enable_0rtt; // Probably true for QUIC

  // only used by the client
  const char *host_name; // Client only, sent in SNI. Can pass NULL for server
  const quic_ticket *server_ticket; // May be NULL

  void *callback_state; // Passed back as the first argument of callbacks, may be NULL
  pfn_FFI_ticket_cb ticket_callback; // May be NULL
  mitls_cert_cb *cert_callbacks; // May be NULL

  // only used by the server
  const char *ticket_enc_alg; // one of "AES128-GCM" "AES256-GCM" "CHACHA20-POLY1305", or NULL
  const char *ticket_key; // If NULL a random key will be sampled
  size_t ticket_key_len; // Should be 28 or 44, concatenation of key and static IV
} quic_config;


// pass 0 to leave any of the configuration values undefined
extern int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg, /* out */ char **errmsg);

extern quic_result MITLS_CALLCONV FFI_mitls_quic_process(/* in */ quic_state *state, /*in*/ char* inBuf, /*inout*/ size_t *pInBufLen, /*out*/ char *outBuf, /*inout*/ size_t *pOutBufLen, /* out */ char **errmsg);

// If the peer is a client, version will be the initial version, otherwise it will be the negotiated version
// If qp->tp_data is NULL, qp->tp_len will still be set to the size of the peer's transport parameters
extern int MITLS_CALLCONV FFI_mitls_quic_get_peer_parameters(/* in */ quic_state *state, /*out*/ uint32_t *version, /*out*/ quic_transport_parameters *qp, /* out */ char **errmsg);

extern int MITLS_CALLCONV FFI_mitls_quic_get_exporter(/* in */ quic_state *state, int early, /* out */ quic_secret *secret, /* out */ char **errmsg);
extern void MITLS_CALLCONV FFI_mitls_quic_free(/* in */ quic_state *state);

#endif // HEADER_MITLS_FFI_H

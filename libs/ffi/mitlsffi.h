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
typedef struct quic12_state quic12_state;

typedef struct {
  size_t ticket_len;
  const unsigned char *ticket;
  size_t session_len;
  const unsigned char *session;
} mitls_ticket;

typedef enum {
  TLS_SSL3 = 0,
  TLS_1p0 = 1,
  TLS_1p1 = 2,
  TLS_1p2 = 3,
  TLS_1p3 = 4
} mitls_version;

typedef struct {
  uint16_t ext_type;
  const unsigned char *ext_data;
  size_t ext_data_len;
} mitls_extension;

typedef struct {
  const unsigned char *alpn;
  size_t alpn_len;
} mitls_alpn;

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

typedef enum {
  TLS_nego_abort = 0,
  TLS_nego_accept = 1,
  TLS_nego_retry = 2
} mitls_nego_action;

typedef uint16_t mitls_signature_scheme;

// Agile secret with static allocation
typedef struct {
  mitls_hash hash;
  mitls_aead ae;
  unsigned char secret[64]; // Max possible size, flat allocation
} mitls_secret;

// Invoked when a TLS clients receives a new TLS ticket
typedef void (MITLS_CALLCONV *pfn_FFI_ticket_cb)(void *cb_state, const char *sni, const mitls_ticket *ticket);

// Invoked when a TLS server is negotiating extensions and stateless retry,
// and when a TLS client is validating the server's negotiated extensions
typedef mitls_nego_action (MITLS_CALLCONV *pfn_FFI_nego_cb)(void *cb_state, mitls_version ver, const unsigned char *exts, size_t exts_len, /*out*/ mitls_extension **custom_exts, /*out*/size_t *custom_exts_len, /*inout*/ unsigned char **cookie, size_t *cookie_len);

#define MAX_CHAIN_LEN 65536
#define MAX_SIGNATURE_LEN 8192
// Select a certificate based on the given SNI and list of signatures.
// Signature algorithms are represented as 16-bit integers using the TLS 1.3 RFC code points
typedef void* (MITLS_CALLCONV *pfn_FFI_cert_select_cb)(void *cb_state, mitls_version ver, const unsigned char *sni, size_t sni_len, const unsigned char *alpn, size_t alpn_len, const mitls_signature_scheme *sigalgs, size_t sigalgs_len, mitls_signature_scheme *selected);
// Write the certificate chain to buffer, returning the number of written bytes.
// The chain should be written by prefixing each certificate by its length encoded over 3 bytes
typedef size_t (MITLS_CALLCONV *pfn_FFI_cert_format_cb)(void *cb_state, const void *cert_ptr, unsigned char buffer[MAX_CHAIN_LEN]);
// Tries to sign and write the signature to sig, returning the signature size or 0 if signature failed
typedef size_t (MITLS_CALLCONV *pfn_FFI_cert_sign_cb)(void *cb_state, const void *cert_ptr, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, unsigned char *sig);
// Verifies that the chain (given in the same format as above) is valid, and that sig is a valid signature
// of tbs for sigalg using the public key stored in the leaf of the chain.
// N.B. this function must validate the chain (including applcation checks such as hostname matching)
typedef int (MITLS_CALLCONV *pfn_FFI_cert_verify_cb)(void *cb_state, const unsigned char* chain, size_t chain_len, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, const unsigned char *sig, size_t sig_len);

typedef struct {
  pfn_FFI_cert_select_cb select;
  pfn_FFI_cert_format_cb format;
  pfn_FFI_cert_sign_cb sign;
  pfn_FFI_cert_verify_cb verify;
} mitls_cert_cb;

// Functions exported from libmitls.dll
//   Functions returning 'int' return 0 for failure, or nonzero for success

// Redirect debug tracing to a callback function.  This is process-wide and can
// be called before or after FFI_mitls_init().
typedef void (MITLS_CALLCONV *pfn_mitls_trace_callback)(const char *msg);
extern void MITLS_CALLCONV FFI_mitls_set_trace_callback(pfn_mitls_trace_callback cb);

// Perform one-time initialization
extern int MITLS_CALLCONV FFI_mitls_init(void);

// Set the global ticket encryption key (used on the server side for tickets and cookies)
// and sealing key (used on the client side to seal session information for resumption)
// alg is one of "AES128-GCM", "AES256-GCM", "CHACHA20-POLY1305", klen must account for
// the key and IV (e.g. 32 + 12). If these keys are not set, fresh random keys will be used.
extern int MITLS_CALLCONV FFI_mitls_set_ticket_key(const char *alg, const unsigned char *ticketkey, size_t klen);
extern int MITLS_CALLCONV FFI_mitls_set_sealing_key(const char *alg, const unsigned char *sealingkey, size_t klen);

// Perform one-time termination
extern void MITLS_CALLCONV FFI_mitls_cleanup(void);

// Configure miTLS ahead of connecting
extern int MITLS_CALLCONV FFI_mitls_configure(/* out */ mitls_state **state, const char *tls_version, const char *host_name);

// Configure a ticket to resume (client only). Can be called more than once to offer multiple 1.3 PSK
extern int MITLS_CALLCONV FFI_mitls_configure_ticket(mitls_state *state, const mitls_ticket *ticket);

// Set configuration options ahead of connecting
extern int MITLS_CALLCONV FFI_mitls_configure_cipher_suites(/* in */ mitls_state *state, const char *cs);
extern int MITLS_CALLCONV FFI_mitls_configure_signature_algorithms(/* in */ mitls_state *state, const char *sa);
extern int MITLS_CALLCONV FFI_mitls_configure_named_groups(/* in */ mitls_state *state, const char *ng);
extern int MITLS_CALLCONV FFI_mitls_configure_alpn(/* in */ mitls_state *state, const mitls_alpn *alpn, size_t alpn_count);
extern int MITLS_CALLCONV FFI_mitls_configure_early_data(/* in */ mitls_state *state, uint32_t max_early_data);
extern int MITLS_CALLCONV FFI_mitls_configure_custom_extensions(/* in */ mitls_state *state, const mitls_extension *exts, size_t exts_count);
extern int MITLS_CALLCONV FFI_mitls_configure_ticket_callback(mitls_state *state, void *cb_state, pfn_FFI_ticket_cb ticket_cb);
extern int MITLS_CALLCONV FFI_mitls_configure_nego_callback(mitls_state *state, void *cb_state, pfn_FFI_nego_cb nego_cb);
extern int MITLS_CALLCONV FFI_mitls_configure_cert_callbacks(mitls_state *state, void *cb_state, mitls_cert_cb *cert_cb);

// Close a miTLS session - either after configure or connect
extern void MITLS_CALLCONV FFI_mitls_close(/* in */ mitls_state *state);

// Callbacks from miTLS to the host application, to send and receive TCP
typedef int (MITLS_CALLCONV *pfn_FFI_send)(void *ctx, const unsigned char *buffer, size_t buffer_size);
typedef int (MITLS_CALLCONV *pfn_FFI_recv)(void *ctx, unsigned char *buffer, size_t buffer_size);

// Connect to a TLS server
extern int MITLS_CALLCONV FFI_mitls_connect(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state);

// Act as a TLS server to a client
extern int MITLS_CALLCONV FFI_mitls_accept_connected(void *send_recv_ctx, pfn_FFI_send psend, pfn_FFI_recv precv, /* in */ mitls_state *state);

// Get the exporter secret (set early to true for the early exporter secret). Returns 1 if a secret was written
extern int MITLS_CALLCONV FFI_mitls_get_exporter(/* in */ mitls_state *state, int early, /* out */ mitls_secret *secret);

// Retrieve the server certificate after FFI_mitls_connect() completes
extern void *MITLS_CALLCONV FFI_mitls_get_cert(/* in */ mitls_state *state, /* out */ size_t *cert_size);

// Send a message
// Returns -1 for failure, or a TCP packet to be sent then freed with FFI_mitls_free()
extern int MITLS_CALLCONV FFI_mitls_send(/* in */ mitls_state *state, const unsigned char *buffer, size_t buffer_size);

// Receive a message
// Returns NULL for failure, a plaintext packet to be freed with FFI_mitls_free_packet()
extern unsigned char *MITLS_CALLCONV FFI_mitls_receive(/* in */ mitls_state *state, /* out */ size_t *packet_size);

// Free a packet returned FFI_mitls_*() family of APIs
extern void MITLS_CALLCONV FFI_mitls_free(/* in */ mitls_state *state, void* pv);

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
  int is_server;

  const char *cipher_suites; // Colon separated list of ciphersuite or NULL
  const char *signature_algorithms; // Colon separated list of signature schemes or NULL
  const char *named_groups; // Colon separated list of Diffie-Hellman groups or NULL

  // only used by the client
  const char *host_name; // Client only, sent in SNI. Can pass NULL for server
  const mitls_alpn *alpn; // Array of ALPN protocols to offer
  size_t alpn_count; // Size of above array
  const quic_ticket *server_ticket; // May be NULL
  const mitls_extension *exts; // Array of custom extensions to offer, may be NULL
  size_t exts_count;           // Size of custom extensions array

  void *callback_state; // Passed back as the first argument of callbacks, may be NULL
  pfn_FFI_ticket_cb ticket_callback; // May be NULL
  pfn_FFI_nego_cb nego_callback; // May be NULL
  mitls_cert_cb *cert_callbacks; // May be NULL

  // only used by the server
  const char *ticket_enc_alg; // one of "AES128-GCM" "AES256-GCM" "CHACHA20-POLY1305", or NULL
  const unsigned char *ticket_key; // If NULL a random key will be sampled
  size_t ticket_key_len; // Should be 28 or 44, concatenation of key and static IV
} quic_config;


// pass 0 to leave any of the configuration values undefined
extern int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg);
extern quic_result MITLS_CALLCONV FFI_mitls_quic_process(quic_state *state, const unsigned char* inBuf, /*inout*/ size_t *pInBufLen, /*out*/ unsigned char *outBuf, /*inout*/ size_t *pOutBufLen);
extern int MITLS_CALLCONV FFI_mitls_quic_get_exporter(quic_state *state, int early, /* out */ quic_secret *secret);
extern void MITLS_CALLCONV FFI_mitls_quic_close(quic_state *state);

typedef struct {
  const unsigned char *sni;
  size_t sni_len;
  const unsigned char *alpn;
  size_t alpn_len;
  const unsigned char *extensions;
  size_t extensions_len;
} mitls_hello_summary;

// N.B. *cookie must be freed with FFI_mitls_global_free as it is allocated in the global region
extern int MITLS_CALLCONV FFI_mitls_get_hello_summary(const unsigned char *buffer, size_t buffer_len, int has_record, mitls_hello_summary *summary, unsigned char **cookie, size_t *cookie_len);

// *ext_data points to a location in exts - no freeing required
extern int MITLS_CALLCONV FFI_mitls_find_custom_extension(int is_server, const unsigned char *exts, size_t exts_len, uint16_t ext_type, unsigned char **ext_data, size_t *ext_data_len);

// Free 'out' variables returned by the FFI_mitls_quic*() family of functions.
extern void MITLS_CALLCONV FFI_mitls_quic_free(quic_state *state, void* pv);

// Free 'out' variables returned by functions that do not have a state as input
extern void MITLS_CALLCONV FFI_mitls_global_free(void* pv);

/*************************************************************************
* QUIC draft 12 API to the TLS handshake
**************************************************************************/

// Convert into a quic_key with quic_crypto_create
typedef struct {
  mitls_aead alg;
  unsigned char aead_key[32];
  unsigned char aead_iv[12];
  unsigned char pne_key[32];
} quic12_key;

typedef struct {
  // == Set by QUIC ==
  const unsigned char *input; // can be NULL, a TLS message fragment read by QUIC
  size_t input_len; // Size of input buffer (can be 0)
  unsigned char *output; // can be NULL, a buffer to store handshake data to send
  size_t output_len; // Size of output buffer (can be 0)

  // == Set by TLS ==
  uint16_t tls_error; // alert code of a locally-generated TLS alert
  size_t consumed_bytes; // how many bytes of the input have been processed - leftover bytes must be processed in the next call
  size_t to_be_written; // how many bytes are left to write (after writing *output)
  const char *tls_error_desc; // meaningful description of the local error
  int32_t cur_reader_key; // current reader epoch, if incremented by TLS, QUIC must switch key BEFORE processing further packets.
  int32_t cur_writer_key; // current writer epoch, if incremented by TLS, QUIC must switch key AFTER writing *output
  uint8_t can_write_data; // Set to 1 if the writer epoch has increased and the new key can be used to send data packets
  uint8_t rejected_0rtt; // Set to 1 on a client when server rejects 0-RTT
  uint8_t complete; // a flag to indicate handshake completion. Not very meaningful as post-handshake messages may still need processing
} quic_process_ctx;

extern int MITLS_CALLCONV FFI_mitls_quic12_create(quic12_state **state, const quic_config *cfg);
extern int MITLS_CALLCONV FFI_mitls_quic12_process(quic12_state *state, quic_process_ctx *ctx);
extern int MITLS_CALLCONV FFI_mitls_quic12_get_record_key(quic12_state *state, quic12_key *key, int32_t epoch, int rw);
extern void MITLS_CALLCONV FFI_mitls_quic12_close(quic12_state *state);

#endif // HEADER_MITLS_FFI_H

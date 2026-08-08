#ifndef TLS13_CLIENT_ENGINE_H
#define TLS13_CLIENT_ENGINE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tls13_client_engine_s tls13_client_engine;

#define TLS13_CLIENT_ENGINE_MAX_SERVER_NAME_LEN ((size_t)255u)
#define TLS13_CLIENT_ENGINE_MAX_TRUST_CONTEXT_LEN ((size_t)65535u)
#define TLS13_CLIENT_ENGINE_MAX_APPLICATION_DATA_LEN ((size_t)16384u)
#define TLS13_CLIENT_ENGINE_NETWORK_OUT_CAPACITY ((size_t)20000u)
#define TLS13_CLIENT_ENGINE_APPLICATION_OUT_CAPACITY ((size_t)16640u)
#define TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_CAPACITY ((size_t)32768u)
#define TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES ((size_t)8u)
#define TLS13_CLIENT_ENGINE_CERTIFICATE_VERIFY_INPUT_CAPACITY ((size_t)256u)
#define TLS13_CLIENT_ENGINE_SIGNATURE_CAPACITY ((size_t)4096u)
/* Must match TLS13.Impl.ConnectionState.Bounds.max_public_key_len: this buffer
   carries a peer leaf certificate DER, and real leaves with large SAN lists
   exceed 4 KiB. */
#define TLS13_CLIENT_ENGINE_PUBLIC_KEY_CAPACITY ((size_t)16384u)

typedef enum tls13_client_engine_error_e {
  TLS13_CLIENT_ENGINE_SUCCESS = 0,
  TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT = 1,
  TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE = 2,
  TLS13_CLIENT_ENGINE_ERROR_ALLOCATION = 3,
  TLS13_CLIENT_ENGINE_ERROR_INTERNAL = 4
} tls13_client_engine_error;

typedef enum tls13_client_engine_action_e {
  TLS13_CLIENT_ENGINE_PROGRESS = 0,
  TLS13_CLIENT_ENGINE_NEED_NETWORK_INPUT = 1,
  TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_VERIFICATION = 2,
  TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_SIGNATURE_VERIFICATION = 3,
  TLS13_CLIENT_ENGINE_NETWORK_OUTPUT = 4,
  TLS13_CLIENT_ENGINE_APPLICATION_DATA = 5,
  TLS13_CLIENT_ENGINE_READY = 6,
  TLS13_CLIENT_ENGINE_CLOSING = 7,
  TLS13_CLIENT_ENGINE_CLOSED = 8,
  TLS13_CLIENT_ENGINE_FAILED = 9
} tls13_client_engine_action;

typedef enum tls13_client_engine_status_e {
  TLS13_CLIENT_ENGINE_STATUS_OK = 0,
  TLS13_CLIENT_ENGINE_STATUS_NEED_MORE_INPUT = 1,
  TLS13_CLIENT_ENGINE_STATUS_DECODE_ERROR = 2,
  TLS13_CLIENT_ENGINE_STATUS_ILLEGAL_TRANSITION = 3,
  TLS13_CLIENT_ENGINE_STATUS_OUTPUT_BUFFER_TOO_SMALL = 4,
  TLS13_CLIENT_ENGINE_STATUS_CONNECTION_FAILED = 5
} tls13_client_engine_status;

typedef struct tls13_client_engine_result_s {
  tls13_client_engine_action action;
  tls13_client_engine_status status;
  size_t consumed_len;
  size_t network_out_len;
  size_t application_out_len;
} tls13_client_engine_result;

typedef struct tls13_client_engine_certificate_chain_s {
  size_t bytes_len;
  size_t certificate_count;
} tls13_client_engine_certificate_chain;

typedef struct tls13_client_engine_certificate_verify_request_s {
  size_t input_len;
  uint16_t signature_scheme;
  size_t signature_len;
} tls13_client_engine_certificate_verify_request;

/*
 * The engine owns no socket. Each operation performs at most one verified TLS
 * step. The caller drains network output, retains unconsumed network input, and
 * polls again to discover the next action. Network input may be fed after
 * NEED_NETWORK_INPUT, while READY, or while CLOSING.
 */
int tls13_client_engine_new(
    tls13_client_engine **out,
    const uint8_t *server_name,
    size_t server_name_len,
    const uint8_t *trust_context,
    size_t trust_context_len,
    size_t validation_time_seconds);

int tls13_client_engine_poll(
    tls13_client_engine *engine,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result);

int tls13_client_engine_feed_network(
    tls13_client_engine *engine,
    const uint8_t *network_input,
    size_t network_input_len,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result);

/*
 * These copy functions are valid only for their corresponding NEED_* action.
 * The chain buffer receives concatenated DER certificates; offsets and lengths
 * identify each certificate within that buffer.
 */
int tls13_client_engine_copy_certificate_chain(
    tls13_client_engine *engine,
    uint8_t *chain_out,
    size_t chain_out_capacity,
    size_t *offsets_out,
    size_t offsets_out_capacity,
    size_t *lengths_out,
    size_t lengths_out_capacity,
    tls13_client_engine_certificate_chain *chain);

int tls13_client_engine_copy_certificate_verify_request(
    tls13_client_engine *engine,
    uint8_t *input_out,
    size_t input_out_capacity,
    uint8_t *signature_out,
    size_t signature_out_capacity,
    tls13_client_engine_certificate_verify_request *request);

/*
 * Calling these completion functions attests that the embedder performed the
 * stated authentication check. Certificate validation must cover the copied
 * chain, server name, trust context, and validation time. Signature validation
 * must cover the copied CertificateVerify request using the same authenticated
 * leaf key. On rejection, free the engine and close the transport.
 */
int tls13_client_engine_complete_certificate_verification(
    tls13_client_engine *engine,
    const uint8_t *authenticated_public_key,
    size_t authenticated_public_key_len,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result);

int tls13_client_engine_complete_certificate_signature_verification(
    tls13_client_engine *engine,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result);

int tls13_client_engine_send_application_data(
    tls13_client_engine *engine,
    const uint8_t *payload,
    size_t payload_len,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result);

int tls13_client_engine_send_close_notify(
    tls13_client_engine *engine,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result);

void tls13_client_engine_free(tls13_client_engine *engine);

#ifdef __cplusplus
}
#endif

#endif

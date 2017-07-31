#ifndef BENCH_TYPES
#define BENCH_TYPES

#include <stdlib.h>
#include <stdint.h>

// TODO: fix these
typedef uint8_t random_bytes[32];

// Fill an array with random bytes.
void mk_random_bytes(random_bytes arr);

typedef int sessionID;

// Not sure about this one
typedef uint8_t valid_cipher_suite[32];

void mk_cipher_suite(valid_cipher_suite cipher);
void mk_cipher_suites(valid_cipher_suite * arr);

typedef int compression;
void mk_compressions(compression * arr);

typedef struct offer {
  // ch_protocol_version: protocolVersion;  // max supported version up to TLS_1p2 (TLS 1.3 uses the supported_versions extension)
  random_bytes ch_client_random;
  sessionID h_sessionID;
  valid_cipher_suite ch_cipher_suites[256];
  compression ch_compressions[256];
  // ch_extensions: option (ce:list extension{List.Tot.length ce < 256});
} offer;

offer mk_offer();

typedef int retryInfo;

typedef struct mode {
    offer n_offer;
    // n_hrr: option (retryInfo n_offer) ->  // optional HRR roundtrip

    // // more from SH (both TLS 1.2 and TLS 1.3)
    // n_protocol_version: protocolVersion ->
    // n_server_random: TLSInfo.random ->
    // n_sessionID: option sessionID {n_sessionID = None <==> n_protocol_version = TLS_1p3} ->
    // n_cipher_suite: cipherSuite ->

    // // redundant with the server extension response?
    // n_pski: option (pski n_offer) -> // only for TLS 1.3, result of a tricky stateful computation

    // // concatenating SH and EE extensions for 1.3, in wire order.
    // n_server_extensions: option (se:list extension{List.Tot.length se < 256}) ->

    // // more from SKE in ...ServerHelloDone (1.2) or SH (1.3)
    // n_server_share: option share ->

    // // more from either ...ServerHelloDone (1.2) or ServerFinished (1.3)
    // n_client_cert_request: option HandshakeMessages.cr ->
    // n_server_cert: option Cert.chain13 ->

    // // more from either CH+SH (1.3) or CKE (1.2)
    // n_client_share: option share ->
} mode;

mode mk_mode(offer n_offer);

typedef int cert;

// TODO: flesh out config
typedef int config;

//TODO: flesh out config
config mk_config();

typedef int resumeInfo;

typedef enum negotationState_tag {
    C_Init,
    C_Offer,
    C_HRR,
    C_WaitFinished1,
    C_Mode,
    C_WaitFinished2,
    C_Complete,
    S_Init,
    S_HRR,
    S_ClientHello,
    S_Mode,
    S_Complete
} negotationState_tag;

typedef struct C_Init_data {
   random_bytes n_client_data;
} C_Init_data;

typedef struct C_Offer_data {
    offer n_offer;
} C_Offer_data;

typedef struct C_HRR_data {
    offer n_offer;
    retryInfo n_hrr;
} C_HRR_data;

typedef struct C_WaitFinished1_data {
    mode n_partial_mode;
} C_WaitFinished1_data;

typedef struct C_Mode_data {
    mode n_mode;
} C_Mode_data;

typedef struct C_WaitFinished2_data {
    mode n_partial_mode;
    cert n_client_certificate;
} C_WaitFinished2_data;

typedef struct C_Complete_data {
    mode n_mode;
    cert n_client_certificate;
} C_Complete_data;

typedef struct S_Init_data {
    random_bytes n_server_random;
} S_Init_data;

typedef struct S_HRR_data {
   offer n_offer;
   retryInfo n_hrr;
} S_HRR_data;

typedef struct S_ClientHello_data {
    mode n_mode;
} S_ClientHello_data;

typedef struct S_Mode_data {
    mode n_mode;
} S_Mode_data;

typedef struct S_Complete_data {
    mode n_mode;
    cert n_client_certificate;
} S_Complete_data;

typedef struct negotationState {
    negotationState_tag tag;
    union {
        C_Init_data c_init_field;
        C_Offer_data c_offer_field;
        C_HRR_data c_hrr_field;
        C_WaitFinished1_data c_wait_finished1_field;
        C_Mode_data c_mode_field;
        C_WaitFinished2_data c_wait_finished2_field;
        C_Complete_data c_complete_field;
        S_Init_data server_init_field;
        S_HRR_data server_hrr_field;
        S_ClientHello_data server_hello_field;
        S_Mode_data server_mode_field;
        S_Complete_data server_complete_field;
    };
} negotationState;

negotationState mk_client_init();
negotationState mk_client_offer();
negotationState mk_client_mode(offer n_offer);
negotationState mk_client_complete(mode n_mode);
negotationState mk_client_hrr(offer n_offer);
negotationState mk_server_init();
negotationState mk_server_client_hello();
negotationState mk_server_mode(mode);
negotationState mk_server_complete(mode);

// negotationState mk_h rr

typedef struct negotationContext {
    config cfg;
    // resumeInfo resume;
    // random_bytes nonce;
    negotationState * state;
} negotationContext;

negotationContext mk_context();

#endif

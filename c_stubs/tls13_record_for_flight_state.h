#ifndef TLS13_RECORD_FOR_FLIGHT_STATE_H
#define TLS13_RECORD_FOR_FLIGHT_STATE_H

#include "TLS13_KeySchedule.h"
#include "TLS13_Handshake_Transcript.h"
#include "TLS13_Record.h"
#include "TLS13_Record_Framing.h"
#include "tls13_crypto_external.h"

#define TLS13_Record_record_state_free(st, erased) TLS13_Record_record_state_free(st)
#define TLS13_Record_install_handshake_keys_runtime(st, key, iv, erased_st, key_bytes, iv_bytes) \
    TLS13_Record_install_handshake_keys_runtime(st, key, iv)
#define TLS13_Record_seal_application_runtime(st, aad, aad_len, plain, plain_len, out, erased_st, aad_bytes, plain_bytes, old_out) \
    TLS13_Record_seal_application_runtime(st, aad, aad_len, plain, plain_len, out)
#define TLS13_Record_open_application_runtime(st, aad, aad_len, cipher, cipher_len, out, erased_st, aad_bytes, cipher_bytes, old_out) \
    TLS13_Record_open_application_runtime(st, aad, aad_len, cipher, cipher_len, out)
#define TLS13_Record_Framing_decode_inner_plaintext_no_padding(inner, inner_len, content_type_out, content_type_out_len, inner_bytes, old_content_type_out) \
    TLS13_Record_Framing_decode_inner_plaintext_no_padding(inner, inner_len, content_type_out, content_type_out_len)
#define TLS13_Handshake_Transcript_hash_client_server_hello(client_hello, client_hello_len, server_hello, server_hello_len, out, client_hello_bytes, server_hello_bytes, old_out) \
    TLS13_Handshake_Transcript_hash_client_server_hello(client_hello, client_hello_len, server_hello, server_hello_len, out)
#define TLS13_Handshake_Transcript_hash_client_server_handshake(client_hello, client_hello_len, server_hello, server_hello_len, server_handshake, server_handshake_len, out, client_hello_bytes, server_hello_bytes, server_handshake_bytes, old_out) \
    TLS13_Handshake_Transcript_hash_client_server_handshake(client_hello, client_hello_len, server_hello, server_hello_len, server_handshake, server_handshake_len, out)
#define TLS13_Handshake_Transcript_equal32(a, b, a_bytes, b_bytes) \
    TLS13_Handshake_Transcript_equal32(a, b)
#define TLS13_KeySchedule_handshake_secret(early, shared, shared_len, out, early_bytes, shared_bytes, old_out) \
    TLS13_KeySchedule_handshake_secret(early, shared, shared_len, out)
#define TLS13_KeySchedule_client_handshake_traffic_secret(handshake, transcript_hash, out, handshake_bytes, hash_bytes, old_out) \
    TLS13_KeySchedule_client_handshake_traffic_secret(handshake, transcript_hash, out)
#define TLS13_KeySchedule_server_handshake_traffic_secret(handshake, transcript_hash, out, handshake_bytes, hash_bytes, old_out) \
    TLS13_KeySchedule_server_handshake_traffic_secret(handshake, transcript_hash, out)
#define TLS13_KeySchedule_derive_traffic_key(traffic_secret, out, secret_bytes, old_out) \
    TLS13_KeySchedule_derive_traffic_key(traffic_secret, out)
#define TLS13_KeySchedule_derive_traffic_iv(traffic_secret, out, secret_bytes, old_out) \
    TLS13_KeySchedule_derive_traffic_iv(traffic_secret, out)
#define TLS13_KeySchedule_finished_verify_data(base_key, transcript_hash, out, base_key_bytes, hash_bytes, old_out) \
    TLS13_KeySchedule_finished_verify_data(base_key, transcript_hash, out)

#endif

#ifndef TLS13_CONNECTION_EXTERNAL_LAYER_H
#define TLS13_CONNECTION_EXTERNAL_LAYER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "TLS13_Record.h"
#include "TLS13_Record_Framing.h"

#define TLS13_Record_record_state_free(st, erased) TLS13_Record_record_state_free(st)
#define TLS13_Record_install_application_keys_runtime(st, key, iv, erased_st, key_bytes, iv_bytes) \
    TLS13_Record_install_application_keys_runtime(st, key, iv)
#define TLS13_Record_seal_application_runtime(st, aad, aad_len, plain, plain_len, out, erased_st, aad_bytes, plain_bytes, old_out) \
    TLS13_Record_seal_application_runtime(st, aad, aad_len, plain, plain_len, out)
#define TLS13_Record_open_application_runtime(st, aad, aad_len, cipher, cipher_len, out, erased_st, aad_bytes, cipher_bytes, old_out) \
    TLS13_Record_open_application_runtime(st, aad, aad_len, cipher, cipher_len, out)
#define TLS13_Record_Framing_decode_inner_plaintext_no_padding(inner, inner_len, content_type_out, content_type_out_len, inner_bytes, old_content_type_out) \
    TLS13_Record_Framing_decode_inner_plaintext_no_padding(inner, inner_len, content_type_out, content_type_out_len)
#define TLS13_Record_Framing_decode_inner_plaintext(inner, inner_len, content_type_out, content_type_out_len, inner_bytes, old_content_type_out) \
    TLS13_Record_Framing_decode_inner_plaintext(inner, inner_len, content_type_out, content_type_out_len)
#define TLS13_Record_Framing_serialize_application_data_header(fragment_len, out, out_len, old_out) \
    TLS13_Record_Framing_serialize_application_data_header(fragment_len, out, out_len)
#define TLS13_Record_Framing_parse_record_header(header, header_len, content_type_out, content_type_out_len, fragment_len_out, fragment_len_out_len, header_bytes, old_content_type_out, old_fragment_len_out) \
    TLS13_Record_Framing_parse_record_header(header, header_len, content_type_out, content_type_out_len, fragment_len_out, fragment_len_out_len)
#define TLS13_Record_Framing_encode_inner_plaintext_no_padding_slice(plain, plain_total_len, plain_offset, plain_len, content_type, out, out_len, plain_bytes, old_out) \
    TLS13_Record_Framing_encode_inner_plaintext_no_padding_slice(plain, plain_total_len, plain_offset, plain_len, content_type, out, out_len)

typedef struct TLS13_IO_channel_s *TLS13_IO_channel;
typedef void *TLS13_X509_Spec_trust_store;
typedef struct TLS13_Connection_External_connection_s *TLS13_Connection_External_connection;

typedef struct TLS13_Connection_External_config_s {
    uint16_t port;
    const char *ca_pem_path;
} TLS13_Connection_External_config;

void Pulse_Lib_Array_memcpy(
    size_t len,
    uint8_t *src,
    uint8_t *dst,
    void *src_bytes,
    void *dst_bytes,
    void *squash);

TLS13_Connection_External_connection TLS13_Connection_External_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_X509_Spec_trust_store trust_store,
    void *hostname_bytes);

void TLS13_Connection_External_client_free(TLS13_Connection_External_connection c);

bool TLS13_Connection_External_client_connect(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch);

bool TLS13_Connection_External_derive_application_keys(
    TLS13_Connection_External_connection c,
    uint8_t *client_key,
    uint8_t *client_iv,
    uint8_t *server_key,
    uint8_t *server_iv,
    void *old_client_key,
    void *old_client_iv,
    void *old_server_key,
    void *old_server_iv);

size_t TLS13_Connection_External_client_write_raw(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *buf_bytes);

size_t TLS13_Connection_External_client_read_raw(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf);

bool TLS13_Connection_External_client_close(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch);

#endif

#ifndef TLS13_HANDSHAKE_EXTERNAL_LAYER_H
#define TLS13_HANDSHAKE_EXTERNAL_LAYER_H

#include "tls13_connection_external.h"
#include "TLS13_Handshake_Framing.h"
#include "TLS13_Record_Framing.h"

#include <stdbool.h>
#include <stddef.h>

#define TLS13_Record_Framing_parse_record_header(header, header_len, content_type_out, content_type_out_len, fragment_len_out, fragment_len_out_len, header_bytes, old_content_type_out, old_fragment_len_out) \
    TLS13_Record_Framing_parse_record_header(header, header_len, content_type_out, content_type_out_len, fragment_len_out, fragment_len_out_len)
#define TLS13_Handshake_Framing_serialize_client_hello_record_header(out, out_len, old_out) \
    TLS13_Handshake_Framing_serialize_client_hello_record_header(out, out_len)
#define TLS13_Handshake_Framing_build_supported_client_hello_localhost(random, key_share, out, out_len, random_bytes, key_share_bytes, old_out) \
    TLS13_Handshake_Framing_build_supported_client_hello_localhost(random, key_share, out, out_len)
#define TLS13_Handshake_Framing_parse_supported_server_hello(input, input_len, random_out, random_out_len, key_share_out, key_share_out_len, input_bytes, old_random, old_key_share) \
    TLS13_Handshake_Framing_parse_supported_server_hello(input, input_len, random_out, random_out_len, key_share_out, key_share_out_len)

typedef struct TLS13_Handshake_External_handshake_context_s
    *TLS13_Handshake_External_handshake_context;

TLS13_Handshake_External_handshake_context TLS13_Handshake_External_context_new(void);

void TLS13_Handshake_External_context_free(
    TLS13_Handshake_External_handshake_context ctx);

bool TLS13_Handshake_External_connect(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

bool TLS13_Handshake_External_store_client_hello(
    TLS13_Handshake_External_handshake_context ctx,
    uint8_t *hello,
    size_t hello_len,
    void *hello_bytes);

size_t TLS13_Handshake_External_read_raw(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf);

size_t TLS13_Handshake_External_write_raw(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *buf_bytes);

bool TLS13_Handshake_External_build_client_finished_record(
    TLS13_Handshake_External_handshake_context ctx,
    uint8_t *out,
    size_t out_len,
    void *old_out);

bool TLS13_Handshake_External_process_server_hello_record(
    TLS13_Handshake_External_handshake_context ctx,
    uint8_t *header,
    size_t header_len,
    uint8_t *fragment,
    size_t fragment_len,
    uint8_t *key_share,
    size_t key_share_len,
    void *header_bytes,
    void *fragment_bytes,
    void *key_share_bytes);

bool TLS13_Handshake_External_recv_encrypted_extensions(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

bool TLS13_Handshake_External_recv_certificate(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

bool TLS13_Handshake_External_validate_certificate(
    TLS13_Handshake_External_handshake_context ctx);

bool TLS13_Handshake_External_recv_certificate_verify(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

bool TLS13_Handshake_External_recv_server_finished(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

#endif

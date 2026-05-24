#ifndef TLS13_HANDSHAKE_BYTE_DRIVER_EXTERNAL_H
#define TLS13_HANDSHAKE_BYTE_DRIVER_EXTERNAL_H

#include "tls13_connection_external.h"
#include "TLS13_Record_Framing.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define TLS13_Record_Framing_parse_record_header(header, header_len, content_type_out, content_type_out_len, fragment_len_out, fragment_len_out_len, header_bytes, old_content_type_out, old_fragment_len_out) \
    TLS13_Record_Framing_parse_record_header(header, header_len, content_type_out, content_type_out_len, fragment_len_out, fragment_len_out_len)

typedef struct TLS13_Handshake_ByteDriver_External_context_s
    *TLS13_Handshake_ByteDriver_External_context;

void TLS13_Handshake_ByteDriver_External_reset_encrypted_handshake(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *old_progress);

size_t TLS13_Handshake_ByteDriver_External_read_raw(
    TLS13_Handshake_ByteDriver_External_context ctx,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *progress,
    void *old_buf);

bool TLS13_Handshake_ByteDriver_External_process_encrypted_handshake_record(
    TLS13_Handshake_ByteDriver_External_context ctx,
    uint8_t *header,
    size_t header_len,
    uint8_t *cipher,
    size_t cipher_len,
    void *progress,
    void *header_bytes,
    void *cipher_bytes);

bool TLS13_Handshake_ByteDriver_External_pending_handshake_message_complete(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress);

uint8_t TLS13_Handshake_ByteDriver_External_pending_handshake_message_type(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress);

bool TLS13_Handshake_ByteDriver_External_accept_encrypted_extensions(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_accept_certificate(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_accept_certificate_verify(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_accept_finished(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_encrypted_handshake_complete(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress);

#endif

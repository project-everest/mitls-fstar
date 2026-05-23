#ifndef TLS13_HANDSHAKE_BYTE_DRIVER_EXTERNAL_H
#define TLS13_HANDSHAKE_BYTE_DRIVER_EXTERNAL_H

#include "tls13_connection_external.h"

#include <stdbool.h>
#include <stdint.h>

typedef struct TLS13_Handshake_ByteDriver_External_context_s
    *TLS13_Handshake_ByteDriver_External_context;

void TLS13_Handshake_ByteDriver_External_reset_encrypted_handshake(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_read_next_encrypted_handshake_record(
    TLS13_Handshake_ByteDriver_External_context ctx,
    TLS13_IO_channel ch);

bool TLS13_Handshake_ByteDriver_External_pending_handshake_message_complete(
    TLS13_Handshake_ByteDriver_External_context ctx);

uint8_t TLS13_Handshake_ByteDriver_External_pending_handshake_message_type(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_accept_encrypted_extensions(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_accept_certificate(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_accept_certificate_verify(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_accept_finished(
    TLS13_Handshake_ByteDriver_External_context ctx);

bool TLS13_Handshake_ByteDriver_External_encrypted_handshake_complete(
    TLS13_Handshake_ByteDriver_External_context ctx);

#endif

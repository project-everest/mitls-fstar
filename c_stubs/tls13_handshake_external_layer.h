#ifndef TLS13_HANDSHAKE_EXTERNAL_LAYER_H
#define TLS13_HANDSHAKE_EXTERNAL_LAYER_H

#include "tls13_connection_external.h"

#include <stdbool.h>

typedef struct TLS13_Handshake_External_handshake_context_s
    *TLS13_Handshake_External_handshake_context;

TLS13_Handshake_External_handshake_context TLS13_Handshake_External_context_new(void);

void TLS13_Handshake_External_context_free(
    TLS13_Handshake_External_handshake_context ctx);

void TLS13_Handshake_External_send_client_hello(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

bool TLS13_Handshake_External_recv_server_hello(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

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

bool TLS13_Handshake_External_send_client_finished(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch);

#endif

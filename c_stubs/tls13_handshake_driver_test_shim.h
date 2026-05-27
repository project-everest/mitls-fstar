#ifndef TLS13_HANDSHAKE_DRIVER_TEST_SHIM_H
#define TLS13_HANDSHAKE_DRIVER_TEST_SHIM_H

#include <stdbool.h>
#include <stddef.h>

typedef struct TLS13_Handshake_handshake_context_s *TLS13_Handshake_handshake_context;
typedef struct TLS13_IO_channel_s *TLS13_IO_channel;

bool TLS13_Handshake_send_client_hello(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

bool TLS13_Handshake_recv_server_hello(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

bool TLS13_Handshake_recv_encrypted_extensions(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

bool TLS13_Handshake_recv_certificate(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

bool TLS13_Handshake_validate_certificate(
    TLS13_Handshake_handshake_context ctx,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

bool TLS13_Handshake_recv_certificate_verify(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

bool TLS13_Handshake_recv_server_finished(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

bool TLS13_Handshake_send_client_finished(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw);

#endif

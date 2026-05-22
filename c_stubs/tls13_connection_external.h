#ifndef TLS13_CONNECTION_EXTERNAL_H
#define TLS13_CONNECTION_EXTERNAL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct TLS13_Connection_connection_s *TLS13_Connection_connection;
typedef struct TLS13_IO_channel_s *TLS13_IO_channel;

bool TLS13_Connection_client_connect(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state);

bool TLS13_Connection_client_write_all(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *erased_bytes,
    void *erased_state_ref,
    void *erased_state);

bool TLS13_Connection_client_read_exact(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t len,
    void *erased_old_bytes,
    void *erased_state_ref,
    void *erased_state);

#endif

#ifndef TLS13_CONNECTION_EXTERNAL_LAYER_H
#define TLS13_CONNECTION_EXTERNAL_LAYER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct TLS13_IO_channel_s *TLS13_IO_channel;
typedef void *TLS13_X509_Spec_trust_store;
typedef struct TLS13_Connection_External_connection_s *TLS13_Connection_External_connection;

TLS13_Connection_External_connection TLS13_Connection_External_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_X509_Spec_trust_store trust_store,
    void *hostname_bytes);

void TLS13_Connection_External_client_free(TLS13_Connection_External_connection c);

bool TLS13_Connection_External_client_connect(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch);

size_t TLS13_Connection_External_client_write(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes);

bool TLS13_Connection_External_client_write_all(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes);

size_t TLS13_Connection_External_client_read(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t max_len,
    void *old_bytes);

bool TLS13_Connection_External_client_read_exact(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t len,
    void *old_bytes);

bool TLS13_Connection_External_client_close(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch);

#endif

#ifndef TLS13_CONNECTION_EXTERNAL_LAYER_H
#define TLS13_CONNECTION_EXTERNAL_LAYER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "TLS13_Record.h"

#define TLS13_Record_record_state_free(st, erased) TLS13_Record_record_state_free(st)

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
    TLS13_IO_channel ch,
    uint8_t *client_key,
    uint8_t *client_iv,
    uint8_t *server_key,
    uint8_t *server_iv,
    void *old_client_key,
    void *old_client_iv,
    void *old_server_key,
    void *old_server_iv);

bool TLS13_Connection_External_client_write_application_record(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    TLS13_Record_record_state record_state,
    uint8_t *key,
    uint8_t *iv,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t chunk_len,
    void *record_state_s,
    void *key_bytes,
    void *iv_bytes,
    void *bytes);

size_t TLS13_Connection_External_client_read_application_record(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    TLS13_Record_record_state record_state,
    uint8_t *key,
    uint8_t *iv,
    uint8_t *out,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *record_state_s,
    void *key_bytes,
    void *iv_bytes,
    void *old_bytes);

bool TLS13_Connection_External_client_close(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch);

#endif

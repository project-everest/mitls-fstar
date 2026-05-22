#ifndef TLS13_CONNECTION_PROBE_H
#define TLS13_CONNECTION_PROBE_H

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
#include "tls13_connection_external_layer.h"
#else
#include "tls13_connection_external.h"
#endif

#include <stdint.h>

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
TLS13_Connection_External_connection tls13_connection_probe_new(
    const char *host,
    uint16_t port,
    const char *ca_pem_path);

void tls13_connection_probe_free(TLS13_Connection_External_connection c);
#else
TLS13_Connection_connection tls13_connection_probe_new(
    const char *host,
    uint16_t port,
    const char *ca_pem_path);

void tls13_connection_probe_free(TLS13_Connection_connection c);
#endif

#endif

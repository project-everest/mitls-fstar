#ifndef TLS13_CONNECTION_PROBE_H
#define TLS13_CONNECTION_PROBE_H

#include "tls13_connection_external_layer.h"

#include <stdint.h>

TLS13_Connection_External_connection tls13_connection_probe_new(
    const char *host,
    uint16_t port,
    const char *ca_pem_path);

void tls13_connection_probe_free(TLS13_Connection_External_connection c);

#endif

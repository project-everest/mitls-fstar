#ifndef TLS13_CONNECTION_PROBE_H
#define TLS13_CONNECTION_PROBE_H

#include "tls13_connection_external.h"

#include <stdint.h>

TLS13_Connection_connection tls13_connection_probe_new(
    const char *host,
    uint16_t port,
    const char *ca_pem_path);

void tls13_connection_probe_free(TLS13_Connection_connection c);

#endif

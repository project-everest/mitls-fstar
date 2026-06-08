#ifndef TLS13_CLIENT_DRIVER_H
#define TLS13_CLIENT_DRIVER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct tls13_client_driver_s tls13_client_driver;

int tls13_client_driver_connect(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds);

int tls13_client_driver_send_application_data(
    tls13_client_driver *driver,
    const uint8_t *payload,
    size_t payload_len);

int tls13_client_driver_receive_application_data(
    tls13_client_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len);

int tls13_client_driver_close(
    tls13_client_driver *driver,
    bool wait_for_peer_close_notify);

const char *tls13_client_driver_last_error(const tls13_client_driver *driver);

void tls13_client_driver_free(tls13_client_driver *driver);

#endif

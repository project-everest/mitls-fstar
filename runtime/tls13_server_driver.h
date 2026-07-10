#ifndef TLS13_SERVER_DRIVER_H
#define TLS13_SERVER_DRIVER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "karamel_option_compat.h"

typedef struct tls13_server_driver_s tls13_server_driver;

int tls13_server_driver_accept(
    tls13_server_driver **out,
    const char *bind_host,
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key_pem,
    size_t private_key_pem_len);

int tls13_server_driver_send_application_data(
    tls13_server_driver *driver,
    const uint8_t *payload,
    size_t payload_len);

int tls13_server_driver_receive_application_data(
    tls13_server_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len);

int tls13_server_driver_close(
    tls13_server_driver *driver,
    bool wait_for_peer_close_notify);

const char *tls13_server_driver_last_error(const tls13_server_driver *driver);

void tls13_server_driver_free(tls13_server_driver *driver);

#endif

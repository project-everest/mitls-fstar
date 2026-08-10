#ifndef TLS13_SERVER_DRIVER_H
#define TLS13_SERVER_DRIVER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "karamel_option_compat.h"

typedef struct tls13_server_driver_s tls13_server_driver;
typedef struct tls13_server_config_s tls13_server_config;

#define TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE ((size_t)16640u)

int tls13_server_config_new(
    tls13_server_config **out,
    const char *bind_host,
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key_pem,
    size_t private_key_pem_len);

void tls13_server_config_free(tls13_server_config *config);

int tls13_server_driver_accept_with_config(
    tls13_server_driver **out,
    const tls13_server_config *config);

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

/* Sends a TLS 1.3 KeyUpdate (RFC 8446 4.6.3), rotating this endpoint's
 * application write key.  When [request_peer_update] is true the peer is asked
 * to rotate its own sending key in reply (update_requested); otherwise the
 * KeyUpdate is a bare rotation (update_not_requested).  Returns 0 on success.
 * On failure the channel is closed, matching the verified contract. */
int tls13_server_driver_send_key_update(
    tls13_server_driver *driver,
    bool request_peer_update);

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

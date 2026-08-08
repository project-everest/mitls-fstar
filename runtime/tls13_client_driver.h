#ifndef TLS13_CLIENT_DRIVER_H
#define TLS13_CLIENT_DRIVER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct tls13_client_driver_s tls13_client_driver;
typedef struct tls13_client_config_s tls13_client_config;

#define TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE ((size_t)16640u)

int tls13_client_config_new(
    tls13_client_config **out,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds);

void tls13_client_config_free(tls13_client_config *config);

int tls13_client_driver_connect_with_config(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const tls13_client_config *config);

int tls13_client_driver_connect(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds);

/* Same as [tls13_client_driver_connect], but also reports why a failed connect
 * failed.  On failure the driver is destroyed (as above, so *out stays NULL)
 * and, when [error_out] is non-NULL, a human-readable reason is copied into it,
 * NUL-terminated and truncated to [error_cap].  Without this the verified
 * workflow status is lost together with the driver that carried it, which makes
 * a handshake failure indistinguishable from a TCP failure. */
int tls13_client_driver_connect_reporting(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds,
    char *error_out,
    size_t error_cap);

int tls13_client_driver_send_application_data(
    tls13_client_driver *driver,
    const uint8_t *payload,
    size_t payload_len);

/* Sends a TLS 1.3 KeyUpdate (RFC 8446 4.6.3), rotating this endpoint's
 * application write key.  When [request_peer_update] is true the peer is asked
 * to rotate its own sending key in reply (update_requested); otherwise the
 * KeyUpdate is a bare rotation (update_not_requested).  Returns 0 on success.
 * On failure the channel is closed, matching the verified contract. */
int tls13_client_driver_send_key_update(
    tls13_client_driver *driver,
    bool request_peer_update);

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

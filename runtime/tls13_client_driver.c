#include "tls13_client_driver.h"

#include "TLS13_Impl_Client.h"
#include "TLS13_Impl_Client_Types.h"
#include "TLS13_Impl_ConnectionState_Repr.h"
#include "tls13_io_stubs.h"
#include "tls13_openssl_stubs.h"

#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLS13_DRIVER_NETWORK_OUT_CAP 20000u
#define TLS13_DRIVER_APP_OUT_CAP 16384u
#define TLS13_DRIVER_RX_CAP 65536u
#define TLS13_DRIVER_SCRATCH_CAP 65536u
#define TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP 4096u

#define TLS13_DRIVER_CONTROL_APPLICATION_DATA 2u
#define TLS13_DRIVER_CONTROL_CLOSING 3u
#define TLS13_DRIVER_CONTROL_CLOSED 4u
#define TLS13_DRIVER_CONTROL_FAILED 5u

struct tls13_client_driver_s {
  TLS13_Impl_ConnectionState_Repr_connection_state client;
  int fd;
  char *server_name;
  uint8_t *trust_anchor_pem;
  size_t trust_anchor_pem_len;
  tls13_peer_identity *peer;
  uint8_t network_out[TLS13_DRIVER_NETWORK_OUT_CAP];
  uint8_t app_out[TLS13_DRIVER_APP_OUT_CAP];
  uint8_t rx[TLS13_DRIVER_RX_CAP];
  size_t rx_len;
  char last_error[256];
};

static int driver_fail(tls13_client_driver *driver, const char *fmt, ...) {
  if (driver != NULL && fmt != NULL) {
    va_list ap;
    va_start(ap, fmt);
    (void)vsnprintf(driver->last_error, sizeof driver->last_error, fmt, ap);
    va_end(ap);
  }
  return 1;
}

static char *duplicate_cstr(const char *src) {
  if (src == NULL) {
    return NULL;
  }
  size_t len = strlen(src);
  char *dst = malloc(len + 1u);
  if (dst != NULL) {
    memcpy(dst, src, len + 1u);
  }
  return dst;
}

static uint8_t *duplicate_bytes(const uint8_t *src, size_t len) {
  if (src == NULL && len != 0u) {
    return NULL;
  }
  uint8_t *dst = calloc(len == 0u ? 1u : len, sizeof(uint8_t));
  if (dst != NULL && len != 0u) {
    memcpy(dst, src, len);
  }
  return dst;
}

static int write_all(tls13_client_driver *driver, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = tls13_io_write_fd(driver->fd, buf + off, len - off);
    if (n <= 0) {
      return driver_fail(driver, "tcp write failed: %s", strerror(errno));
    }
    off += (size_t)n;
  }
  return 0;
}

static int read_more(tls13_client_driver *driver) {
  if (driver->rx_len == sizeof driver->rx) {
    return driver_fail(driver, "receive buffer full");
  }
  ssize_t n =
      tls13_io_read_fd(driver->fd, driver->rx + driver->rx_len, sizeof driver->rx - driver->rx_len);
  if (n < 0) {
    return driver_fail(driver, "tcp read failed: %s", strerror(errno));
  }
  if (n == 0) {
    return driver_fail(driver, "peer closed the TCP connection");
  }
  driver->rx_len += (size_t)n;
  return 0;
}

static int flush_network_response(
    tls13_client_driver *driver,
    TLS13_Impl_Client_Types_client_response response,
    const char *label) {
  if (response.status != TLS13_Impl_Client_Types_StepOk) {
    return driver_fail(driver, "%s returned status %u", label, (unsigned)response.status);
  }
  if (response.network_out_len > sizeof driver->network_out ||
      response.app_out_len > sizeof driver->app_out) {
    return driver_fail(driver, "%s returned out-of-range lengths", label);
  }
  if (response.network_out_len != 0u) {
    return write_all(driver, driver->network_out, response.network_out_len);
  }
  return 0;
}

static int process_one_network_record(
    tls13_client_driver *driver,
    uint8_t *app_out,
    size_t app_out_cap,
    size_t *app_out_len) {
  if (app_out_len != NULL) {
    *app_out_len = 0u;
  }
  memset(driver->network_out, 0, sizeof driver->network_out);
  memset(driver->app_out, 0, sizeof driver->app_out);
  TLS13_Impl_Client_Types_client_buffer_response response =
      process_network_bytes(
          driver->client,
          driver->rx,
          driver->rx_len,
          driver->network_out,
          sizeof driver->network_out,
          driver->app_out,
          sizeof driver->app_out);
  if (response.response.status == TLS13_Impl_Client_Types_NeedMoreInput) {
    return 2;
  }
  if (response.response.status != TLS13_Impl_Client_Types_StepOk) {
    TLS13_Impl_ConnectionState_Repr_control_snapshot snapshot =
        control_snapshot(driver->client);
    if (driver->rx_len >= 5u) {
      size_t record_len = ((size_t)driver->rx[3] << 8) | (size_t)driver->rx[4];
      return driver_fail(
          driver,
          "network step status=%u control=%u stage=%u record={type=%u,ver=%u.%u,len=%zu} buffered=%zu",
          (unsigned)response.response.status,
          (unsigned)snapshot.snapshot_control_tag,
          (unsigned)snapshot.snapshot_handshake_stage_tag,
          (unsigned)driver->rx[0],
          (unsigned)driver->rx[1],
          (unsigned)driver->rx[2],
          record_len,
          driver->rx_len);
    }
    return driver_fail(
        driver,
        "network step returned status %u after %zu buffered bytes",
        (unsigned)response.response.status,
        driver->rx_len);
  }
  if (response.consumed_len == 0u || response.consumed_len > driver->rx_len) {
    return driver_fail(
        driver,
        "network step consumed invalid prefix length %zu from %zu buffered bytes",
        response.consumed_len,
        driver->rx_len);
  }
  if (response.response.network_out_len > sizeof driver->network_out ||
      response.response.app_out_len > sizeof driver->app_out) {
    return driver_fail(driver, "network step returned out-of-range lengths");
  }
  if (response.response.network_out_len != 0u &&
      write_all(driver, driver->network_out, response.response.network_out_len) != 0) {
    return 1;
  }
  if (response.response.app_out_len != 0u) {
    if (app_out == NULL || app_out_len == NULL) {
      return driver_fail(driver, "unexpected application data");
    }
    if (response.response.app_out_len > app_out_cap) {
      return driver_fail(
          driver,
          "application output buffer too small: need %zu bytes",
          response.response.app_out_len);
    }
    memcpy(app_out, driver->app_out, response.response.app_out_len);
    *app_out_len = response.response.app_out_len;
  }
  memmove(
      driver->rx,
      driver->rx + response.consumed_len,
      driver->rx_len - response.consumed_len);
  driver->rx_len -= response.consumed_len;
  return 0;
}

static int validate_certificate_for_local_step(
    tls13_client_driver *driver,
    uint8_t *payload,
    size_t *payload_len) {
  uint8_t leaf_der[TLS13_DRIVER_SCRATCH_CAP] = {0};
  size_t leaf_der_len = copy_certificate_leaf_der(driver->client, leaf_der, sizeof leaf_der);
  if (leaf_der_len == 0u || leaf_der_len > TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP) {
    return driver_fail(driver, "invalid copied leaf DER length %zu", leaf_der_len);
  }
  tls13_openssl_peer_identity_free(driver->peer);
  driver->peer = NULL;
  if (!tls13_openssl_validate_leaf_der(
          driver->server_name,
          driver->trust_anchor_pem,
          driver->trust_anchor_pem_len,
          leaf_der,
          leaf_der_len,
          &driver->peer)) {
    return driver_fail(driver, "certificate validation failed");
  }
  memcpy(payload, leaf_der, leaf_der_len);
  *payload_len = leaf_der_len;
  return 0;
}

static int verify_certificate_signature_for_local_step(tls13_client_driver *driver) {
  if (driver->peer == NULL) {
    return driver_fail(driver, "certificate signature verification has no validated peer");
  }
  uint8_t input[130] = {0};
  size_t input_len = copy_certificate_verify_input(driver->client, input, sizeof input);
  if (input_len != sizeof input) {
    return driver_fail(driver, "CertificateVerify input length was %zu", input_len);
  }
  uint8_t signature[TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP] = {0};
  TLS13_Impl_ConnectionState_Repr_certificate_verify_signature_snapshot sig =
      copy_certificate_verify_signature(driver->client, signature, sizeof signature);
  if (sig.cv_signature_len == 0u || sig.cv_signature_len > sizeof signature) {
    return driver_fail(driver, "CertificateVerify signature length was %zu", sig.cv_signature_len);
  }
  if (!tls13_openssl_peer_verify_signature(
          driver->peer,
          sig.cv_signature_scheme,
          input,
          input_len,
          signature,
          sig.cv_signature_len)) {
    return driver_fail(driver, "CertificateVerify signature verification failed");
  }
  return 0;
}

static int run_one_local_action(tls13_client_driver *driver, bool *progress) {
  TLS13_Impl_Client_Types_next_local_action action =
      next_local_action(
          driver->client,
          sizeof driver->network_out,
          TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP,
          36u);
  if (!action.next_local_ready) {
    *progress = false;
    return 0;
  }

  uint8_t empty_payload[1] = {0};
  uint8_t certificate_payload[TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP] = {0};
  uint8_t *payload = empty_payload;
  size_t payload_len = 0u;

  if (action.next_local_payload == TLS13_Impl_Client_Types_LocalPayloadCertificatePublicKey) {
    if (validate_certificate_for_local_step(driver, certificate_payload, &payload_len) != 0) {
      return 1;
    }
    payload = certificate_payload;
  }

  if (action.next_local_kind == TLS13_Impl_Client_Types_LocalVerifyCertificateSignature &&
      verify_certificate_signature_for_local_step(driver) != 0) {
    return 1;
  }

  memset(driver->network_out, 0, sizeof driver->network_out);
  memset(driver->app_out, 0, sizeof driver->app_out);
  TLS13_Impl_Client_Types_client_response response =
      process_local_event(
          driver->client,
          action.next_local_kind,
          payload,
          payload_len,
          driver->network_out,
          sizeof driver->network_out,
          driver->app_out,
          sizeof driver->app_out);
  if (flush_network_response(driver, response, "local action") != 0) {
    return 1;
  }
  *progress = true;
  return 0;
}

static int run_pending_local_actions(tls13_client_driver *driver) {
  for (size_t i = 0; i < 100u; ++i) {
    bool progress = false;
    if (run_one_local_action(driver, &progress) != 0) {
      return 1;
    }
    if (!progress) {
      return 0;
    }
  }
  return driver_fail(driver, "too many pending local actions");
}

int tls13_client_driver_connect(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds) {
  if (out == NULL || connect_host == NULL || server_name == NULL ||
      (trust_anchor_pem == NULL && trust_anchor_pem_len != 0u)) {
    return 1;
  }
  *out = NULL;
  tls13_client_driver *driver = calloc(1, sizeof *driver);
  if (driver == NULL) {
    return 1;
  }
  driver->fd = -1;
  driver->server_name = duplicate_cstr(server_name);
  driver->trust_anchor_pem = duplicate_bytes(trust_anchor_pem, trust_anchor_pem_len);
  driver->trust_anchor_pem_len = trust_anchor_pem_len;
  if (driver->server_name == NULL || driver->trust_anchor_pem == NULL) {
    tls13_client_driver_free(driver);
    return 1;
  }

  size_t server_name_len = strlen(server_name);
  if (server_name_len == 0u) {
    tls13_client_driver_free(driver);
    return 1;
  }
  driver->client =
      new_client(
          (uint8_t *)driver->server_name,
          server_name_len,
          driver->trust_anchor_pem,
          driver->trust_anchor_pem_len,
          validation_time_seconds);
  driver->fd = tls13_io_connect_tcp(connect_host, port);
  if (driver->fd < 0) {
    driver_fail(driver, "tcp connect to %s:%u failed: %s", connect_host, (unsigned)port, strerror(errno));
    tls13_client_driver_free(driver);
    return 1;
  }
  *out = driver;
  return 0;
}

int tls13_client_driver_handshake(tls13_client_driver *driver) {
  if (driver == NULL) {
    return 1;
  }
  for (size_t i = 0; i < 1000u; ++i) {
    TLS13_Impl_ConnectionState_Repr_control_snapshot snapshot =
        control_snapshot(driver->client);
    if (snapshot.snapshot_control_tag == TLS13_DRIVER_CONTROL_APPLICATION_DATA) {
      return 0;
    }
    if (snapshot.snapshot_control_tag == TLS13_DRIVER_CONTROL_FAILED) {
      return driver_fail(driver, "connection failed during handshake");
    }

    bool local_progress = false;
    if (run_one_local_action(driver, &local_progress) != 0) {
      return 1;
    }
    if (local_progress) {
      continue;
    }

    if (driver->rx_len == 0u && read_more(driver) != 0) {
      return 1;
    }
    int rc = process_one_network_record(driver, NULL, 0u, NULL);
    if (rc == 2) {
      if (read_more(driver) != 0) {
        return 1;
      }
      continue;
    }
    if (rc != 0) {
      return 1;
    }
  }
  return driver_fail(driver, "handshake did not complete");
}

int tls13_client_driver_send_application_data(
    tls13_client_driver *driver,
    const uint8_t *payload,
    size_t payload_len) {
  if (driver == NULL || (payload == NULL && payload_len != 0u)) {
    return 1;
  }
  memset(driver->network_out, 0, sizeof driver->network_out);
  memset(driver->app_out, 0, sizeof driver->app_out);
  TLS13_Impl_Client_Types_client_response response =
      process_local_event(
          driver->client,
          TLS13_Impl_Client_Types_LocalSendApplicationData,
          (uint8_t *)payload,
          payload_len,
          driver->network_out,
          sizeof driver->network_out,
          driver->app_out,
          sizeof driver->app_out);
  return flush_network_response(driver, response, "LocalSendApplicationData");
}

int tls13_client_driver_receive_application_data(
    tls13_client_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len) {
  if (driver == NULL || out == NULL || out_len == NULL) {
    return 1;
  }
  *out_len = 0u;
  for (size_t i = 0; i < 1000u; ++i) {
    if (driver->rx_len == 0u && read_more(driver) != 0) {
      return 1;
    }
    int rc = process_one_network_record(driver, out, out_cap, out_len);
    if (rc == 2) {
      if (read_more(driver) != 0) {
        return 1;
      }
      continue;
    }
    if (rc != 0) {
      return 1;
    }
    if (*out_len != 0u) {
      return 0;
    }
    if (run_pending_local_actions(driver) != 0) {
      return 1;
    }
  }
  return driver_fail(driver, "did not receive application data");
}

static int await_peer_close_notify(tls13_client_driver *driver) {
  for (size_t i = 0; i < 1000u; ++i) {
    TLS13_Impl_ConnectionState_Repr_control_snapshot snapshot =
        control_snapshot(driver->client);
    if (snapshot.snapshot_control_tag == TLS13_DRIVER_CONTROL_CLOSED) {
      return 0;
    }
    if (snapshot.snapshot_control_tag != TLS13_DRIVER_CONTROL_CLOSING &&
        snapshot.snapshot_control_tag != TLS13_DRIVER_CONTROL_APPLICATION_DATA) {
      return driver_fail(
          driver,
          "unexpected control state while waiting for close_notify: %u",
          (unsigned)snapshot.snapshot_control_tag);
    }
    if (driver->rx_len == 0u && read_more(driver) != 0) {
      return 1;
    }
    int rc = process_one_network_record(driver, NULL, 0u, NULL);
    if (rc == 2) {
      if (read_more(driver) != 0) {
        return 1;
      }
      continue;
    }
    if (rc != 0) {
      return 1;
    }
  }
  return driver_fail(driver, "did not receive close_notify");
}

int tls13_client_driver_close(tls13_client_driver *driver, bool wait_for_peer) {
  if (driver == NULL) {
    return 1;
  }
  TLS13_Impl_ConnectionState_Repr_control_snapshot snapshot =
      control_snapshot(driver->client);
  if (snapshot.snapshot_control_tag == TLS13_DRIVER_CONTROL_APPLICATION_DATA) {
    uint8_t empty_payload[1] = {0};
    memset(driver->network_out, 0, sizeof driver->network_out);
    memset(driver->app_out, 0, sizeof driver->app_out);
    TLS13_Impl_Client_Types_client_response response =
        process_local_event(
            driver->client,
            TLS13_Impl_Client_Types_LocalSendCloseNotify,
            empty_payload,
            0u,
            driver->network_out,
            sizeof driver->network_out,
            driver->app_out,
            sizeof driver->app_out);
    if (flush_network_response(driver, response, "LocalSendCloseNotify") != 0) {
      return 1;
    }
  }
  if (wait_for_peer) {
    return await_peer_close_notify(driver);
  }
  return 0;
}

const char *tls13_client_driver_last_error(const tls13_client_driver *driver) {
  if (driver == NULL || driver->last_error[0] == '\0') {
    return "no driver error";
  }
  return driver->last_error;
}

void tls13_client_driver_free(tls13_client_driver *driver) {
  if (driver == NULL) {
    return;
  }
  if (driver->fd >= 0) {
    (void)tls13_io_close_fd(driver->fd);
  }
  tls13_openssl_peer_identity_free(driver->peer);
  free(driver->trust_anchor_pem);
  free(driver->server_name);
  free(driver);
}

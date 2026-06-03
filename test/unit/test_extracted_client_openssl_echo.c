#include "TLS13_Impl_Client.h"
#include "TLS13_Impl_Client_Types.h"
#include "TLS13_Impl_ConnectionState.h"
#include "tls13_openssl_stubs.h"

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

#define NETWORK_OUT_CAP 20000u
#define APP_OUT_CAP 16384u
#define RX_CAP 65536u
#define SCRATCH_CAP 65536u
#define PUBLIC_KEY_PAYLOAD_CAP 4096u

typedef struct driver_state_s {
  TLS13_Impl_ConnectionState_connection_state client;
  int fd;
  uint8_t network_out[NETWORK_OUT_CAP];
  uint8_t app_out[APP_OUT_CAP];
  uint8_t rx[RX_CAP];
  size_t rx_len;
  uint8_t *trust_anchor;
  size_t trust_anchor_len;
  tls13_peer_identity *peer;
} driver_state;

static void write_u24(uint8_t *out, size_t v) {
  out[0] = (uint8_t)(v >> 16);
  out[1] = (uint8_t)(v >> 8);
  out[2] = (uint8_t)v;
}

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return 1;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    perror("fseek");
    fclose(f);
    return 1;
  }
  long len = ftell(f);
  if (len < 0) {
    perror("ftell");
    fclose(f);
    return 1;
  }
  rewind(f);
  uint8_t *buf = calloc((size_t)len == 0u ? 1u : (size_t)len, sizeof(uint8_t));
  if (buf == NULL) {
    fclose(f);
    return 1;
  }
  if (fread(buf, 1u, (size_t)len, f) != (size_t)len) {
    perror("fread");
    free(buf);
    fclose(f);
    return 1;
  }
  fclose(f);
  *out = buf;
  *out_len = (size_t)len;
  return 0;
}

static int connect_loopback(const char *host, uint16_t port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    perror("socket");
    return -1;
  }

  struct timeval timeout = {.tv_sec = 10, .tv_usec = 0};
  (void)setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof timeout);
  (void)setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof timeout);

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_port = htons(port);
  if (inet_pton(AF_INET, host, &addr.sin_addr) != 1) {
    fprintf(stderr, "invalid IPv4 address: %s\n", host);
    close(fd);
    return -1;
  }
  if (connect(fd, (struct sockaddr *)&addr, sizeof addr) != 0) {
    perror("connect");
    close(fd);
    return -1;
  }
  return fd;
}

static int write_all(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = send(fd, buf + off, len - off, 0);
    if (n < 0 && errno == EINTR) {
      continue;
    }
    if (n <= 0) {
      perror("send");
      return 1;
    }
    off += (size_t)n;
  }
  return 0;
}

static int flush_network_response(
    driver_state *d,
    TLS13_Impl_Client_Types_client_response resp,
    const char *label) {
  if (resp.status != TLS13_Impl_Client_Types_StepOk) {
    fprintf(stderr, "%s returned status %u\n", label, (unsigned)resp.status);
    return 1;
  }
  if (resp.network_out_len > sizeof d->network_out ||
      resp.app_out_len > sizeof d->app_out) {
    fprintf(stderr, "%s returned out-of-range lengths\n", label);
    return 1;
  }
  if (resp.network_out_len != 0u &&
      write_all(d->fd, d->network_out, resp.network_out_len) != 0) {
    return 1;
  }
  return 0;
}

static int read_more(driver_state *d) {
  if (d->rx_len == sizeof d->rx) {
    fprintf(stderr, "receive buffer full\n");
    return 1;
  }
  ssize_t n = recv(d->fd, d->rx + d->rx_len, sizeof d->rx - d->rx_len, 0);
  if (n < 0 && errno == EINTR) {
    return read_more(d);
  }
  if (n <= 0) {
    if (n < 0) {
      perror("recv");
    } else {
      fprintf(stderr, "peer closed connection\n");
    }
    return 1;
  }
  d->rx_len += (size_t)n;
  return 0;
}

static int process_one_network_record(
    driver_state *d,
    const uint8_t *expected_app,
    size_t expected_app_len,
    bool *saw_expected_app) {
  memset(d->network_out, 0, sizeof d->network_out);
  memset(d->app_out, 0, sizeof d->app_out);
  TLS13_Impl_Client_Types_client_buffer_response br =
      process_network_bytes(
          d->client,
          d->rx,
          d->rx_len,
          d->network_out,
          sizeof d->network_out,
          d->app_out,
          sizeof d->app_out);
  if (br.response.status == TLS13_Impl_Client_Types_NeedMoreInput) {
    return 2;
  }
  if (br.response.status != TLS13_Impl_Client_Types_StepOk) {
    TLS13_Impl_ConnectionState_control_snapshot snapshot = control_snapshot(d->client);
    if (d->rx_len >= 5u) {
      size_t record_len = ((size_t)d->rx[3] << 8) | (size_t)d->rx[4];
      fprintf(stderr,
              "network record status=%u control=%u stage=%u header={type=%u,ver=%u.%u,len=%zu} buffered=%zu\n",
              (unsigned)br.response.status,
              (unsigned)snapshot.snapshot_control_tag,
              (unsigned)snapshot.snapshot_handshake_stage_tag,
              (unsigned)d->rx[0],
              (unsigned)d->rx[1],
              (unsigned)d->rx[2],
              record_len,
              d->rx_len);
    }
    fprintf(stderr,
            "network record returned status %u after %zu buffered bytes\n",
            (unsigned)br.response.status,
            d->rx_len);
    return 1;
  }
  if (br.consumed_len == 0u || br.consumed_len > d->rx_len) {
    fprintf(stderr, "invalid consumed_len %zu for rx_len %zu\n", br.consumed_len, d->rx_len);
    return 1;
  }
  if (br.response.network_out_len > sizeof d->network_out ||
      br.response.app_out_len > sizeof d->app_out) {
    fprintf(stderr, "network record returned out-of-range response lengths\n");
    return 1;
  }
  if (br.response.network_out_len != 0u &&
      write_all(d->fd, d->network_out, br.response.network_out_len) != 0) {
    return 1;
  }
  if (br.response.app_out_len != 0u) {
    if (br.response.app_out_len == expected_app_len &&
        memcmp(d->app_out, expected_app, expected_app_len) == 0) {
      *saw_expected_app = true;
    } else {
      fprintf(stderr, "unexpected application data length %zu\n", br.response.app_out_len);
      return 1;
    }
  }
  memmove(d->rx, d->rx + br.consumed_len, d->rx_len - br.consumed_len);
  d->rx_len -= br.consumed_len;
  return 0;
}

static int validate_certificate_for_local_step(driver_state *d, uint8_t *payload, size_t *payload_len) {
  uint8_t leaf_der[SCRATCH_CAP] = {0};
  size_t leaf_der_len = copy_certificate_leaf_der(d->client, leaf_der, sizeof leaf_der);
  if (leaf_der_len == 0u || leaf_der_len > PUBLIC_KEY_PAYLOAD_CAP) {
    fprintf(stderr, "invalid copied leaf DER length %zu\n", leaf_der_len);
    return 1;
  }
  tls13_openssl_peer_identity_free(d->peer);
  d->peer = NULL;
  if (!tls13_openssl_validate_leaf_der(
          "localhost",
          d->trust_anchor,
          d->trust_anchor_len,
          leaf_der,
          leaf_der_len,
          &d->peer)) {
    fprintf(stderr, "OpenSSL certificate validation failed\n");
    return 1;
  }
  memcpy(payload, leaf_der, leaf_der_len);
  *payload_len = leaf_der_len;
  return 0;
}

static int verify_certificate_signature_for_local_step(driver_state *d) {
  if (d->peer == NULL) {
    fprintf(stderr, "certificate signature verification has no validated peer\n");
    return 1;
  }
  uint8_t input[130] = {0};
  size_t input_len = copy_certificate_verify_input(d->client, input, sizeof input);
  if (input_len != sizeof input) {
    fprintf(stderr, "CertificateVerify input length was %zu\n", input_len);
    return 1;
  }
  uint8_t signature[PUBLIC_KEY_PAYLOAD_CAP] = {0};
  TLS13_Impl_ConnectionState_certificate_verify_signature_snapshot sig =
      copy_certificate_verify_signature(d->client, signature, sizeof signature);
  if (sig.cv_signature_len == 0u || sig.cv_signature_len > sizeof signature) {
    fprintf(stderr, "CertificateVerify signature length was %zu\n", sig.cv_signature_len);
    return 1;
  }
  if (!tls13_openssl_peer_verify_signature(
          d->peer,
          sig.cv_signature_scheme,
          input,
          input_len,
          signature,
          sig.cv_signature_len)) {
    fprintf(stderr, "OpenSSL CertificateVerify verification failed\n");
    return 1;
  }
  return 0;
}

static int build_finished_payload(driver_state *d, uint8_t out[36]) {
  uint8_t verify_data[32] = {0};
  size_t verify_len = copy_server_finished_verify_data(d->client, verify_data, sizeof verify_data);
  if (verify_len != sizeof verify_data) {
    fprintf(stderr, "server Finished verify_data length was %zu\n", verify_len);
    return 1;
  }
  out[0] = 20u;
  write_u24(out + 1, verify_len);
  memcpy(out + 4, verify_data, verify_len);
  return 0;
}

static int run_one_local_action(driver_state *d, bool *progress) {
  TLS13_Impl_Client_Types_next_local_action action =
      next_local_action(d->client, sizeof d->network_out, PUBLIC_KEY_PAYLOAD_CAP, 36u);
  if (!action.next_local_ready) {
    *progress = false;
    return 0;
  }
  uint8_t empty_payload[1] = {0};
  uint8_t certificate_payload[PUBLIC_KEY_PAYLOAD_CAP] = {0};
  uint8_t finished_payload[36] = {0};
  uint8_t *payload = empty_payload;
  size_t payload_len = 0u;

  if (action.next_local_payload == TLS13_Impl_Client_Types_LocalPayloadCertificatePublicKey) {
    if (validate_certificate_for_local_step(d, certificate_payload, &payload_len) != 0) {
      return 1;
    }
    payload = certificate_payload;
  } else if (action.next_local_payload == TLS13_Impl_Client_Types_LocalPayloadServerFinishedHandshake) {
    if (build_finished_payload(d, finished_payload) != 0) {
      return 1;
    }
    payload = finished_payload;
    payload_len = sizeof finished_payload;
  }

  if (action.next_local_kind == TLS13_Impl_Client_Types_LocalVerifyCertificateSignature &&
      verify_certificate_signature_for_local_step(d) != 0) {
    return 1;
  }

  memset(d->network_out, 0, sizeof d->network_out);
  memset(d->app_out, 0, sizeof d->app_out);
  TLS13_Impl_Client_Types_client_response resp =
      process_local_event(
          d->client,
          action.next_local_kind,
          payload,
          payload_len,
          d->network_out,
          sizeof d->network_out,
          d->app_out,
          sizeof d->app_out);
  if (flush_network_response(d, resp, "local action") != 0) {
    return 1;
  }
  *progress = true;
  return 0;
}

static int drive_handshake(driver_state *d) {
  for (size_t i = 0; i < 1000u; ++i) {
    TLS13_Impl_ConnectionState_control_snapshot snapshot = control_snapshot(d->client);
    if (snapshot.snapshot_control_tag == 2u) {
      return 0;
    }
    if (snapshot.snapshot_control_tag == 5u) {
      fprintf(stderr, "connection failed during handshake\n");
      return 1;
    }

    bool local_progress = false;
    if (run_one_local_action(d, &local_progress) != 0) {
      return 1;
    }
    if (local_progress) {
      continue;
    }

    if (d->rx_len == 0u && read_more(d) != 0) {
      return 1;
    }
    bool ignored_app = false;
    int rc = process_one_network_record(d, NULL, 0u, &ignored_app);
    if (rc == 2) {
      if (read_more(d) != 0) {
        return 1;
      }
      continue;
    }
    if (rc != 0) {
      return 1;
    }
  }
  fprintf(stderr, "handshake did not complete\n");
  return 1;
}

static int send_application_data(driver_state *d, const uint8_t *payload, size_t payload_len) {
  memset(d->network_out, 0, sizeof d->network_out);
  memset(d->app_out, 0, sizeof d->app_out);
  TLS13_Impl_Client_Types_client_response resp =
      process_local_event(
          d->client,
          TLS13_Impl_Client_Types_LocalSendApplicationData,
          (uint8_t *)payload,
          payload_len,
          d->network_out,
          sizeof d->network_out,
          d->app_out,
          sizeof d->app_out);
  return flush_network_response(d, resp, "LocalSendApplicationData");
}

static int send_close_notify(driver_state *d) {
  uint8_t empty_payload[1] = {0};
  memset(d->network_out, 0, sizeof d->network_out);
  memset(d->app_out, 0, sizeof d->app_out);
  TLS13_Impl_Client_Types_client_response resp =
      process_local_event(
          d->client,
          TLS13_Impl_Client_Types_LocalSendCloseNotify,
          empty_payload,
          0u,
          d->network_out,
          sizeof d->network_out,
          d->app_out,
          sizeof d->app_out);
  return flush_network_response(d, resp, "LocalSendCloseNotify");
}

static int receive_expected_echo(driver_state *d, const uint8_t *expected, size_t expected_len) {
  bool saw_expected = false;
  for (size_t i = 0; i < 1000u && !saw_expected; ++i) {
    if (d->rx_len == 0u && read_more(d) != 0) {
      return 1;
    }
    int rc = process_one_network_record(d, expected, expected_len, &saw_expected);
    if (rc == 2) {
      if (read_more(d) != 0) {
        return 1;
      }
      continue;
    }
    if (rc != 0) {
      return 1;
    }
  }
  if (!saw_expected) {
    fprintf(stderr, "did not receive expected echo\n");
    return 1;
  }
  return 0;
}

static int receive_close_notify(driver_state *d) {
  for (size_t i = 0; i < 1000u; ++i) {
    TLS13_Impl_ConnectionState_control_snapshot snapshot = control_snapshot(d->client);
    if (snapshot.snapshot_control_tag == 4u) {
      return 0;
    }
    if (d->rx_len == 0u && read_more(d) != 0) {
      return 1;
    }
    bool ignored_app = false;
    int rc = process_one_network_record(d, NULL, 0u, &ignored_app);
    if (rc == 2) {
      if (read_more(d) != 0) {
        return 1;
      }
      continue;
    }
    if (rc != 0) {
      return 1;
    }
  }
  fprintf(stderr, "did not receive close_notify\n");
  return 1;
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s HOST PORT CA_PEM\n", argv[0]);
    return 1;
  }

  char *end = NULL;
  long port_long = strtol(argv[2], &end, 10);
  if (end == argv[2] || *end != '\0' || port_long <= 0 || port_long > 65535) {
    fprintf(stderr, "invalid port: %s\n", argv[2]);
    return 1;
  }

  driver_state d;
  memset(&d, 0, sizeof d);
  d.fd = -1;
  if (read_file(argv[3], &d.trust_anchor, &d.trust_anchor_len) != 0) {
    return 1;
  }

  uint8_t server_name[] = {'l', 'o', 'c', 'a', 'l', 'h', 'o', 's', 't'};
  d.client = new_client(server_name, sizeof server_name, d.trust_anchor, d.trust_anchor_len, 0u);
  d.fd = connect_loopback(argv[1], (uint16_t)port_long);
  if (d.fd < 0) {
    free(d.trust_anchor);
    return 1;
  }

  int rc = 1;
  static const uint8_t ping[] = {'p', 'i', 'n', 'g'};
  if (drive_handshake(&d) == 0 &&
      send_application_data(&d, ping, sizeof ping) == 0 &&
      receive_expected_echo(&d, ping, sizeof ping) == 0 &&
      send_close_notify(&d) == 0 &&
      receive_close_notify(&d) == 0) {
    printf("extracted client OpenSSL echo test passed\n");
    rc = 0;
  }

  if (d.fd >= 0) {
    close(d.fd);
  }
  tls13_openssl_peer_identity_free(d.peer);
  free(d.trust_anchor);
  return rc;
}

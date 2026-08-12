#include "tls13_client_engine.h"
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

#define NETWORK_INPUT_CAPACITY ((size_t)65535u)
#define NETWORK_READ_CHUNK ((size_t)7u)
#define ENGINE_STEP_LIMIT ((size_t)1000u)

typedef struct engine_test_state_s {
  tls13_client_engine *engine;
  tls13_trust_store *trust_store;
  tls13_peer_identity *peer;
  int socket_fd;
  uint8_t network_input[NETWORK_INPUT_CAPACITY];
  size_t network_input_len;
  uint8_t network_out[TLS13_CLIENT_ENGINE_NETWORK_OUT_CAPACITY];
  uint8_t application_out[TLS13_CLIENT_ENGINE_APPLICATION_OUT_CAPACITY];
  uint8_t received[64];
  size_t received_len;
  unsigned pings_sent;
  unsigned pings_echoed;
  bool sent_close;
} engine_test_state;

/* Several echo round-trips, not one.  The echo server requests a KeyUpdate on
   each record it receives, so round-trip i drives application traffic at
   epoch i in both directions.  One round-trip only ever reaches epoch 1. */
#define ECHO_ROUNDS 4u

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
  uint8_t *bytes = malloc((size_t)len == 0u ? 1u : (size_t)len);
  if (bytes == NULL) {
    fclose(f);
    return 1;
  }
  if (fread(bytes, 1u, (size_t)len, f) != (size_t)len) {
    perror("fread");
    free(bytes);
    fclose(f);
    return 1;
  }
  fclose(f);
  *out = bytes;
  *out_len = (size_t)len;
  return 0;
}

static int connect_tcp(const char *host, uint16_t port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    perror("socket");
    return -1;
  }
  struct sockaddr_in address;
  memset(&address, 0, sizeof address);
  address.sin_family = AF_INET;
  if (inet_pton(AF_INET, host, &address.sin_addr) != 1) {
    fprintf(stderr, "invalid IPv4 address: %s\n", host);
    close(fd);
    return -1;
  }
  address.sin_port = htons(port);
  if (connect(fd, (struct sockaddr *)&address, sizeof address) != 0) {
    perror("connect");
    close(fd);
    return -1;
  }
  struct timeval timeout = {.tv_sec = 10, .tv_usec = 0};
  if (setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof timeout) != 0 ||
      setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof timeout) != 0) {
    perror("setsockopt");
    close(fd);
    return -1;
  }
  return fd;
}

static int send_all(int fd, const uint8_t *bytes, size_t len) {
  size_t sent = 0u;
  while (sent < len) {
    ssize_t written = send(fd, bytes + sent, len - sent, MSG_NOSIGNAL);
    if (written <= 0) {
      perror("send");
      return 1;
    }
    sent += (size_t)written;
  }
  return 0;
}

static int check_result_lengths(
    const tls13_client_engine_result *result) {
  if (result->network_out_len >
          TLS13_CLIENT_ENGINE_NETWORK_OUT_CAPACITY ||
      result->application_out_len >
          TLS13_CLIENT_ENGINE_APPLICATION_OUT_CAPACITY) {
    fprintf(stderr, "engine returned an invalid output length\n");
    return 1;
  }
  return 0;
}

static int handle_outputs(
    engine_test_state *state,
    const tls13_client_engine_result *result) {
  if (check_result_lengths(result) != 0 ||
      send_all(
          state->socket_fd,
          state->network_out,
          result->network_out_len) != 0) {
    return 1;
  }
  if (result->application_out_len >
      sizeof state->received - state->received_len) {
    fprintf(stderr, "too much application data\n");
    return 1;
  }
  memcpy(
      state->received + state->received_len,
      state->application_out,
      result->application_out_len);
  state->received_len += result->application_out_len;
  return 0;
}

static int poll_engine(
    engine_test_state *state,
    tls13_client_engine_result *result) {
  return tls13_client_engine_poll(
      state->engine,
      state->network_out,
      sizeof state->network_out,
      state->application_out,
      sizeof state->application_out,
      result);
}

static int feed_network(
    engine_test_state *state,
    bool append_input,
    tls13_client_engine_result *result) {
  if (state->network_input_len == 0u || append_input) {
    if (state->network_input_len == sizeof state->network_input) {
      fprintf(stderr, "incomplete TLS record exceeds input capacity\n");
      return 1;
    }
    size_t available = sizeof state->network_input - state->network_input_len;
    size_t read_len =
        available < NETWORK_READ_CHUNK ? available : NETWORK_READ_CHUNK;
    ssize_t received = recv(
        state->socket_fd,
        state->network_input + state->network_input_len,
        read_len,
        0);
    if (received <= 0) {
      if (received < 0) {
        perror("recv");
      } else {
        fprintf(stderr, "transport closed before TLS close_notify\n");
      }
      return 1;
    }
    state->network_input_len += (size_t)received;
  }
  int rc = tls13_client_engine_feed_network(
      state->engine,
      state->network_input,
      state->network_input_len,
      state->network_out,
      sizeof state->network_out,
      state->application_out,
      sizeof state->application_out,
      result);
  if (rc != TLS13_CLIENT_ENGINE_SUCCESS) {
    fprintf(stderr, "feed_network failed: %d\n", rc);
    return 1;
  }
  if (result->consumed_len > state->network_input_len) {
    fprintf(stderr, "engine consumed beyond supplied network input\n");
    return 1;
  }
  state->network_input_len -= result->consumed_len;
  memmove(
      state->network_input,
      state->network_input + result->consumed_len,
      state->network_input_len);
  return 0;
}

static bool valid_certificate_span(
    const tls13_client_engine_certificate_chain *chain,
    size_t offset,
    size_t len) {
  return len != 0u && offset <= chain->bytes_len &&
      len <= chain->bytes_len - offset;
}

static int validate_certificate(
    engine_test_state *state,
    tls13_client_engine_result *result) {
  uint8_t chain_bytes[TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_CAPACITY];
  size_t offsets[TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES];
  size_t lengths[TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES];
  tls13_client_engine_certificate_chain chain;
  int rc = tls13_client_engine_copy_certificate_chain(
      state->engine,
      chain_bytes,
      sizeof chain_bytes,
      offsets,
      TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES,
      lengths,
      TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES,
      &chain);
  if (rc != TLS13_CLIENT_ENGINE_SUCCESS ||
      chain.certificate_count == 0u ||
      chain.certificate_count >
          TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES ||
      chain.bytes_len > sizeof chain_bytes ||
      !valid_certificate_span(&chain, offsets[0], lengths[0])) {
    fprintf(stderr, "invalid verified certificate-chain copyout\n");
    return 1;
  }

  tls13_openssl_peer_identity_free(state->peer);
  state->peer = NULL;
  if (!tls13_openssl_validate_leaf_der_with_store(
          "localhost",
          state->trust_store,
          0u,
          chain_bytes + offsets[0],
          lengths[0],
          &state->peer)) {
    fprintf(stderr, "OpenSSL rejected the server certificate\n");
    return 1;
  }

  uint8_t public_key[TLS13_CLIENT_ENGINE_PUBLIC_KEY_CAPACITY];
  size_t public_key_len = 0u;
  if (!tls13_openssl_peer_copy_public_key_der(
          state->peer,
          public_key,
          sizeof public_key,
          &public_key_len)) {
    fprintf(stderr, "could not encode the authenticated public key\n");
    return 1;
  }
  rc = tls13_client_engine_complete_certificate_verification(
      state->engine,
      public_key,
      public_key_len,
      state->network_out,
      sizeof state->network_out,
      state->application_out,
      sizeof state->application_out,
      result);
  if (rc != TLS13_CLIENT_ENGINE_SUCCESS) {
    fprintf(stderr, "certificate completion failed: %d\n", rc);
    return 1;
  }
  return 0;
}

static int validate_certificate_verify(
    engine_test_state *state,
    tls13_client_engine_result *result) {
  uint8_t input[TLS13_CLIENT_ENGINE_CERTIFICATE_VERIFY_INPUT_CAPACITY];
  uint8_t signature[TLS13_CLIENT_ENGINE_SIGNATURE_CAPACITY];
  tls13_client_engine_certificate_verify_request request;
  int rc = tls13_client_engine_copy_certificate_verify_request(
      state->engine,
      input,
      sizeof input,
      signature,
      sizeof signature,
      &request);
  if (rc != TLS13_CLIENT_ENGINE_SUCCESS ||
      request.input_len > sizeof input ||
      request.signature_len > sizeof signature ||
      !tls13_openssl_peer_verify_signature(
          state->peer,
          request.signature_scheme,
          input,
          request.input_len,
          signature,
          request.signature_len)) {
    fprintf(stderr, "OpenSSL rejected CertificateVerify\n");
    return 1;
  }
  rc = tls13_client_engine_complete_certificate_signature_verification(
      state->engine,
      state->network_out,
      sizeof state->network_out,
      state->application_out,
      sizeof state->application_out,
      result);
  if (rc != TLS13_CLIENT_ENGINE_SUCCESS) {
    fprintf(stderr, "CertificateVerify completion failed: %d\n", rc);
    return 1;
  }
  return 0;
}

static int drive_engine(engine_test_state *state) {
  static const uint8_t ping[] = {'p', 'i', 'n', 'g'};
  tls13_client_engine_result result;
  if (poll_engine(state, &result) != TLS13_CLIENT_ENGINE_SUCCESS) {
    fprintf(stderr, "initial poll failed\n");
    return 1;
  }

  for (size_t step = 0u; step < ENGINE_STEP_LIMIT; ++step) {
    if (handle_outputs(state, &result) != 0) {
      return 1;
    }
    switch (result.action) {
      case TLS13_CLIENT_ENGINE_PROGRESS:
      case TLS13_CLIENT_ENGINE_NETWORK_OUTPUT:
      case TLS13_CLIENT_ENGINE_APPLICATION_DATA:
        if (poll_engine(state, &result) != TLS13_CLIENT_ENGINE_SUCCESS) {
          fprintf(stderr, "poll failed\n");
          return 1;
        }
        break;
      case TLS13_CLIENT_ENGINE_NEED_NETWORK_INPUT:
        if (feed_network(
                state,
                result.status == TLS13_CLIENT_ENGINE_STATUS_NEED_MORE_INPUT,
                &result) != 0) {
          return 1;
        }
        break;
      case TLS13_CLIENT_ENGINE_CLOSING:
        if (feed_network(state, false, &result) != 0) {
          return 1;
        }
        break;
      case TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_VERIFICATION:
        if (validate_certificate(state, &result) != 0) {
          return 1;
        }
        break;
      case TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_SIGNATURE_VERIFICATION:
        if (validate_certificate_verify(state, &result) != 0) {
          return 1;
        }
        break;
      case TLS13_CLIENT_ENGINE_READY:
        if (state->received_len == sizeof ping &&
            memcmp(state->received, ping, sizeof ping) == 0) {
          state->pings_echoed += 1u;
          state->received_len = 0u;
          memset(state->received, 0, sizeof state->received);
        }
        if (state->pings_sent < ECHO_ROUNDS &&
            state->pings_sent == state->pings_echoed) {
          int rc = tls13_client_engine_send_application_data(
              state->engine,
              ping,
              sizeof ping,
              state->network_out,
              sizeof state->network_out,
              state->application_out,
              sizeof state->application_out,
              &result);
          if (rc != TLS13_CLIENT_ENGINE_SUCCESS) {
            fprintf(stderr, "application send failed in round %u: %d\n",
                    state->pings_sent, rc);
            return 1;
          }
          state->pings_sent += 1u;
        } else if (!state->sent_close &&
                   state->pings_echoed == ECHO_ROUNDS) {
          int rc = tls13_client_engine_send_close_notify(
              state->engine,
              state->network_out,
              sizeof state->network_out,
              state->application_out,
              sizeof state->application_out,
              &result);
          if (rc != TLS13_CLIENT_ENGINE_SUCCESS) {
            fprintf(stderr, "close_notify send failed: %d\n", rc);
            return 1;
          }
          state->sent_close = true;
        } else if (feed_network(state, false, &result) != 0) {
          return 1;
        }
        break;
      case TLS13_CLIENT_ENGINE_CLOSED:
        if (state->sent_close && state->pings_echoed == ECHO_ROUNDS) {
          return 0;
        }
        fprintf(stderr, "TLS closed before the echo exchange completed\n");
        return 1;
      case TLS13_CLIENT_ENGINE_FAILED:
      default:
        fprintf(
            stderr,
            "verified engine failed: action=%d status=%d\n",
            (int)result.action,
            (int)result.status);
        return 1;
    }
  }
  fprintf(stderr, "engine step limit exhausted\n");
  return 1;
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s HOST PORT CA_PEM\n", argv[0]);
    return 1;
  }
  char *end = NULL;
  long port_long = strtol(argv[2], &end, 10);
  if (end == argv[2] || *end != '\0' || port_long <= 0 ||
      port_long > 65535) {
    fprintf(stderr, "invalid port: %s\n", argv[2]);
    return 1;
  }

  uint8_t *trust_anchor = NULL;
  size_t trust_anchor_len = 0u;
  if (read_file(argv[3], &trust_anchor, &trust_anchor_len) != 0) {
    return 1;
  }

  engine_test_state *state = calloc(1u, sizeof *state);
  if (state == NULL) {
    free(trust_anchor);
    return 1;
  }
  state->socket_fd = -1;
  state->trust_store =
      tls13_openssl_trust_store_new(trust_anchor, trust_anchor_len);
  state->socket_fd = connect_tcp(argv[1], (uint16_t)port_long);
  int rc = TLS13_CLIENT_ENGINE_ERROR_ALLOCATION;
  if (state->trust_store != NULL && state->socket_fd >= 0) {
    rc = tls13_client_engine_new(
        &state->engine,
        (const uint8_t *)"localhost",
        strlen("localhost"),
        trust_anchor,
        trust_anchor_len,
        0u);
  }

  int result = 1;
  if (rc == TLS13_CLIENT_ENGINE_SUCCESS && drive_engine(state) == 0) {
    printf("transport-neutral client engine OpenSSL echo test passed\n");
    result = 0;
  } else {
    fprintf(stderr, "transport-neutral client engine OpenSSL echo test failed\n");
  }

  tls13_client_engine_free(state->engine);
  tls13_openssl_peer_identity_free(state->peer);
  tls13_openssl_trust_store_free(state->trust_store);
  if (state->socket_fd >= 0) {
    close(state->socket_fd);
  }
  free(state);
  free(trust_anchor);
  return result;
}

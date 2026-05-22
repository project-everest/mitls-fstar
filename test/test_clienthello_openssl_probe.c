#include "tls13_connection_probe.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PROBE_ECHO_PAYLOAD_LEN 40000u

static void fill_probe_payload(uint8_t *payload, size_t payload_len) {
  static const uint8_t echo_pattern[] = "agentic tls multi-record probe\n";
  for (size_t i = 0; i < payload_len; ++i) {
    payload[i] = echo_pattern[i % (sizeof echo_pattern - 1u)];
  }
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s HOST PORT CA_PEM\n", argv[0]);
    return 1;
  }

  char *end = NULL;
  long port_long = strtol(argv[2], &end, 10);
  if (*argv[2] == '\0' || *end != '\0' || port_long <= 0 || port_long > 65535) {
    fprintf(stderr, "invalid port\n");
    return 1;
  }

  uint8_t *echo_payload = malloc(PROBE_ECHO_PAYLOAD_LEN);
  uint8_t *echo_response = malloc(PROBE_ECHO_PAYLOAD_LEN);
  if (echo_payload == NULL || echo_response == NULL) {
    free(echo_payload);
    free(echo_response);
    return 1;
  }
  fill_probe_payload(echo_payload, PROBE_ECHO_PAYLOAD_LEN);

  TLS13_Connection_connection c =
      tls13_connection_probe_new(argv[1], (uint16_t)port_long, argv[3]);
  if (c == NULL) {
    free(echo_payload);
    free(echo_response);
    return 1;
  }

  int rc = 1;
  if (!TLS13_Connection_client_connect(c, NULL, NULL, NULL) ||
      !TLS13_Connection_client_write_all(
          c, NULL, echo_payload, PROBE_ECHO_PAYLOAD_LEN, NULL, NULL, NULL) ||
      !TLS13_Connection_client_read_exact(
          c, NULL, echo_response, PROBE_ECHO_PAYLOAD_LEN, NULL, NULL, NULL)) {
    goto done;
  }
  if (memcmp(echo_response, echo_payload, PROBE_ECHO_PAYLOAD_LEN) != 0) {
    fprintf(stderr, "OpenSSL echo application data mismatch\n");
    goto done;
  }

  printf("ClientHello/OpenSSL TLS echo probe passed\n");
  rc = 0;

done:
  tls13_connection_probe_free(c);
  free(echo_payload);
  free(echo_response);
  return rc;
}

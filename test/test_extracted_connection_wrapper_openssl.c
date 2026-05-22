#include "TLS13_Connection.h"
#include "tls13_connection_probe.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define EXTRACTED_WRAPPER_ECHO_PAYLOAD_LEN 40000u

static void fill_wrapper_payload(uint8_t *payload, size_t payload_len) {
  static const uint8_t echo_pattern[] = "agentic tls extracted wrapper echo\n";
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

  uint8_t *outbound = malloc(EXTRACTED_WRAPPER_ECHO_PAYLOAD_LEN);
  uint8_t *inbound = malloc(EXTRACTED_WRAPPER_ECHO_PAYLOAD_LEN);
  if (outbound == NULL || inbound == NULL) {
    free(outbound);
    free(inbound);
    return 1;
  }
  fill_wrapper_payload(outbound, EXTRACTED_WRAPPER_ECHO_PAYLOAD_LEN);

  TLS13_Connection_External_connection c =
      tls13_connection_probe_new(argv[1], (uint16_t)port_long, argv[3]);
  if (c == NULL) {
    free(outbound);
    free(inbound);
    return 1;
  }

  int rc = 1;
  if (!TLS13_Connection_client_connect(c, NULL) ||
      !TLS13_Connection_client_write_all(
          c, NULL, outbound, EXTRACTED_WRAPPER_ECHO_PAYLOAD_LEN) ||
      !TLS13_Connection_client_read_exact(
          c, NULL, inbound, EXTRACTED_WRAPPER_ECHO_PAYLOAD_LEN)) {
    goto done;
  }
  if (memcmp(inbound, outbound, EXTRACTED_WRAPPER_ECHO_PAYLOAD_LEN) != 0) {
    fprintf(stderr, "extracted wrapper OpenSSL echo mismatch\n");
    goto done;
  }

  printf("extracted connection wrapper OpenSSL echo passed\n");
  rc = 0;

done:
  tls13_connection_probe_free(c);
  free(outbound);
  free(inbound);
  return rc;
}

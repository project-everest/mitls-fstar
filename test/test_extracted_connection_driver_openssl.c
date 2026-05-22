#include "TLS13_Connection_Driver.h"
#include "tls13_connection_probe.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define EXTRACTED_DRIVER_ECHO_PAYLOAD_LEN 40000u

static void fill_driver_payload(uint8_t *payload, size_t payload_len) {
  static const uint8_t echo_pattern[] = "agentic tls extracted driver echo\n";
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

  uint8_t *outbound = malloc(EXTRACTED_DRIVER_ECHO_PAYLOAD_LEN);
  uint8_t *inbound = malloc(EXTRACTED_DRIVER_ECHO_PAYLOAD_LEN);
  if (outbound == NULL || inbound == NULL) {
    free(outbound);
    free(inbound);
    return 1;
  }
  fill_driver_payload(outbound, EXTRACTED_DRIVER_ECHO_PAYLOAD_LEN);

  TLS13_Connection_connection c =
      tls13_connection_probe_new(argv[1], (uint16_t)port_long, argv[3]);
  if (c == NULL) {
    free(outbound);
    free(inbound);
    return 1;
  }

  int rc = 1;
  if (!TLS13_Connection_Driver_connect_write_read_exact(
          c,
          NULL,
          outbound,
          EXTRACTED_DRIVER_ECHO_PAYLOAD_LEN,
          inbound,
          EXTRACTED_DRIVER_ECHO_PAYLOAD_LEN)) {
    goto done;
  }
  if (memcmp(inbound, outbound, EXTRACTED_DRIVER_ECHO_PAYLOAD_LEN) != 0) {
    fprintf(stderr, "extracted driver OpenSSL echo mismatch\n");
    goto done;
  }

  printf("extracted connection driver OpenSSL echo passed\n");
  rc = 0;

done:
  tls13_connection_probe_free(c);
  free(outbound);
  free(inbound);
  return rc;
}

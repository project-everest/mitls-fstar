#include "TLS13_Connection.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define EXTRACTED_WRAPPER_MAX_ECHO_PAYLOAD_LEN 40000u

struct echo_case {
  const char *name;
  size_t payload_len;
  size_t first_read_len;
};

static void fill_wrapper_payload(uint8_t *payload, size_t payload_len) {
  static const uint8_t echo_pattern[] = "agentic tls extracted wrapper echo\n";
  for (size_t i = 0; i < payload_len; ++i) {
    payload[i] = echo_pattern[i % (sizeof echo_pattern - 1u)];
  }
}

static int run_echo_case(
    TLS13_Connection_connection c,
    uint8_t *outbound,
    uint8_t *inbound,
    const struct echo_case *test_case) {
  fill_wrapper_payload(outbound, test_case->payload_len);
  memset(inbound, 0, test_case->payload_len);

  if (!TLS13_Connection_client_write_all(c, NULL, outbound, test_case->payload_len)) {
    fprintf(stderr, "extracted wrapper OpenSSL echo write failed for %s\n", test_case->name);
    return 1;
  }

  size_t first_read_len = test_case->first_read_len;
  if (first_read_len > test_case->payload_len) {
    first_read_len = test_case->payload_len;
  }
  if (first_read_len > 0 &&
      !TLS13_Connection_client_read_exact(c, NULL, inbound, first_read_len)) {
    fprintf(stderr, "extracted wrapper OpenSSL echo first read failed for %s\n", test_case->name);
    return 1;
  }

  size_t remaining = test_case->payload_len - first_read_len;
  if (remaining > 0 &&
      !TLS13_Connection_client_read_exact(c, NULL, inbound + first_read_len, remaining)) {
    fprintf(stderr, "extracted wrapper OpenSSL echo final read failed for %s\n", test_case->name);
    return 1;
  }

  if (memcmp(inbound, outbound, test_case->payload_len) != 0) {
    fprintf(stderr, "extracted wrapper OpenSSL echo mismatch for %s\n", test_case->name);
    return 1;
  }

  return 0;
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

  uint8_t *outbound = malloc(EXTRACTED_WRAPPER_MAX_ECHO_PAYLOAD_LEN);
  uint8_t *inbound = malloc(EXTRACTED_WRAPPER_MAX_ECHO_PAYLOAD_LEN);
  if (outbound == NULL || inbound == NULL) {
    free(outbound);
    free(inbound);
    return 1;
  }

  struct TLS13_Connection_Backend_config_s config = {
      .port = (uint16_t)port_long,
      .ca_pem_path = argv[3],
  };
  TLS13_Connection_connection c =
      TLS13_Connection_client_new((uint8_t *)argv[1], strlen(argv[1]), &config);
  if (c.handshake.backend == NULL) {
    free(outbound);
    free(inbound);
    return 1;
  }

  int rc = 1;
  const struct echo_case echo_cases[] = {
      {"single-byte", 1u, 1u},
      {"split-small", 37u, 5u},
      {"record-boundary", 4096u, 2048u},
      {"record-plus-one", 4097u, 17u},
      {"large-multi-record", EXTRACTED_WRAPPER_MAX_ECHO_PAYLOAD_LEN, 17u},
  };

  if (!TLS13_Connection_client_connect(c, NULL)) {
    goto done;
  }
  for (size_t i = 0; i < sizeof echo_cases / sizeof echo_cases[0]; ++i) {
    if (run_echo_case(c, outbound, inbound, &echo_cases[i]) != 0) {
      goto done;
    }
  }
  TLS13_Connection_client_close(c, NULL);

  printf("extracted connection wrapper OpenSSL echo passed\n");
  rc = 0;

done:
  TLS13_Connection_client_free(c);
  free(outbound);
  free(inbound);
  return rc;
}

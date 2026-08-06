#include "tls13_client_driver.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

  uint8_t *trust_anchor = NULL;
  size_t trust_anchor_len = 0;
  if (read_file(argv[3], &trust_anchor, &trust_anchor_len) != 0) {
    return 1;
  }

  tls13_client_driver *driver = NULL;
  int rc = 1;
  static const uint8_t ping[] = {'p', 'i', 'n', 'g'};
#define ECHO_ROUNDS 4u
  uint8_t received[TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE] = {0};
  size_t received_len = 0;

  /* Several round-trips, not one.  The echo server requests a KeyUpdate on
     each record it receives (up to its own cap), so round-trip i exercises
     application traffic at epoch i in BOTH directions: the peer rotates its
     write key, we rotate our read key to match, and our mandated
     update_not_requested reply rotates our write key and the peer's read key.
     A single round-trip would only ever reach epoch 1, which cannot
     distinguish a correctly iterated traffic secret from one that is
     re-derived from the base secret each time. */
  bool exchange_ok = tls13_client_driver_connect(
          &driver,
          argv[1],
          (uint16_t)port_long,
          "localhost",
          trust_anchor,
          trust_anchor_len,
          0u) == 0;
  for (unsigned round = 0; exchange_ok && round < ECHO_ROUNDS; ++round) {
    received_len = 0;
    memset(received, 0, sizeof received);
    exchange_ok =
        tls13_client_driver_send_application_data(driver, ping, sizeof ping) == 0 &&
        tls13_client_driver_receive_application_data(
            driver,
            received,
            sizeof received,
            &received_len) == 0 &&
        received_len == sizeof ping &&
        memcmp(received, ping, sizeof ping) == 0;
    if (!exchange_ok) {
      fprintf(stderr,
              "extracted client OpenSSL echo test failed in round %u\n",
              round);
    }
  }

  if (exchange_ok && tls13_client_driver_close(driver, true) == 0) {
    printf("extracted client OpenSSL echo test passed\n");
    rc = 0;
  } else if (driver != NULL) {
    fprintf(stderr, "extracted client OpenSSL echo test failed: %s\n",
            tls13_client_driver_last_error(driver));
  } else {
    fprintf(stderr, "extracted client OpenSSL echo test failed during connect\n");
  }

  tls13_client_driver_free(driver);
  free(trust_anchor);
  return rc;
}

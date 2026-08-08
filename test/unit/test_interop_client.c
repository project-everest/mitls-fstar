/* ATLAS interop harness.
 *
 * Drives the extracted, verified ATLAS client driver against a real public
 * HTTPS server: real DNS (the driver's TCP stub already uses getaddrinfo),
 * real SNI, a real trust anchor bundle, and a real HTTP/1.1 GET.  Prints one
 * machine-readable line per run so a sweep can be tabulated:
 *
 *   RESULT <host> <status> <detail>
 *
 * status is one of OK, TCP, HANDSHAKE, SEND, RECV, HTTP.
 */

#include "tls13_client_driver.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    return 1;
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    fclose(file);
    return 1;
  }
  long length = ftell(file);
  if (length < 0) {
    fclose(file);
    return 1;
  }
  rewind(file);
  uint8_t *buffer = malloc((size_t)length + 1u);
  if (buffer == NULL) {
    fclose(file);
    return 1;
  }
  size_t got = fread(buffer, 1u, (size_t)length, file);
  fclose(file);
  if (got != (size_t)length) {
    free(buffer);
    return 1;
  }
  buffer[length] = '\0';
  *out = buffer;
  *out_len = (size_t)length;
  return 0;
}

static void report(const char *host, const char *status, const char *detail) {
  printf("RESULT\t%s\t%s\t%s\n", host, status, detail == NULL ? "-" : detail);
  fflush(stdout);
}

int main(int argc, char **argv) {
  if (argc < 3 || argc > 4) {
    fprintf(stderr, "usage: %s HOST CA_BUNDLE_PEM [PORT]\n", argv[0]);
    return 2;
  }
  const char *host = argv[1];
  const char *ca_path = argv[2];
  uint16_t port = 443u;
  if (argc == 4) {
    port = (uint16_t)strtoul(argv[3], NULL, 10);
  }

  uint8_t *ca = NULL;
  size_t ca_len = 0u;
  if (read_file(ca_path, &ca, &ca_len) != 0) {
    report(host, "TCP", "cannot read CA bundle");
    return 1;
  }

  tls13_client_driver *driver = NULL;
  char why[256];
  int rc = tls13_client_driver_connect_reporting(
      &driver, host, port, host, ca, ca_len, 0u, why, sizeof why);
  if (rc != 0) {
    if (why[0] == '\0') {
      (void)snprintf(why, sizeof why, "connect failed without a reason");
    }
    report(host, "HANDSHAKE", why);
    tls13_client_driver_free(driver);
    free(ca);
    return 1;
  }

  char request[512];
  int request_len = snprintf(
      request,
      sizeof request,
      "GET / HTTP/1.1\r\nHost: %s\r\nUser-Agent: atlas-interop\r\n"
      "Accept: */*\r\nConnection: close\r\n\r\n",
      host);
  if (request_len <= 0 || (size_t)request_len >= sizeof request) {
    report(host, "SEND", "request too long");
    tls13_client_driver_free(driver);
    free(ca);
    return 1;
  }

  if (tls13_client_driver_send_application_data(
          driver, (const uint8_t *)request, (size_t)request_len) != 0) {
    report(host, "SEND", tls13_client_driver_last_error(driver));
    tls13_client_driver_free(driver);
    free(ca);
    return 1;
  }

  char response[8192];
  size_t response_len = 0u;
  for (;;) {
    uint8_t chunk[TLS13_CLIENT_DRIVER_RECEIVE_BUFFER_SIZE];
    size_t chunk_len = 0u;
    if (tls13_client_driver_receive_application_data(
            driver, chunk, sizeof chunk, &chunk_len) != 0) {
      if (response_len == 0u) {
        report(host, "RECV", tls13_client_driver_last_error(driver));
        tls13_client_driver_free(driver);
        free(ca);
        return 1;
      }
      break; /* Peer closed after sending a response; that is fine. */
    }
    if (chunk_len == 0u) {
      break;
    }
    size_t room = sizeof response - 1u - response_len;
    size_t copy = chunk_len < room ? chunk_len : room;
    memcpy(response + response_len, chunk, copy);
    response_len += copy;
    response[response_len] = '\0';
    if (strstr(response, "\r\n\r\n") != NULL || room == copy) {
      break; /* Headers complete; that is all this probe needs. */
    }
  }

  if (response_len == 0u || strncmp(response, "HTTP/1.", 7) != 0) {
    report(host, "HTTP", "no HTTP status line");
    tls13_client_driver_free(driver);
    free(ca);
    return 1;
  }

  char status_line[128];
  size_t status_len = 0u;
  while (status_len < response_len && status_len + 1u < sizeof status_line &&
         response[status_len] != '\r' && response[status_len] != '\n') {
    status_line[status_len] = response[status_len];
    status_len++;
  }
  status_line[status_len] = '\0';
  report(host, "OK", status_line);

  (void)tls13_client_driver_close(driver, false);
  tls13_client_driver_free(driver);
  free(ca);
  return 0;
}

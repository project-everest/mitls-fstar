#include "tls13_openssl_stubs.h"

#include <stdio.h>
#include <stdlib.h>

static uint8_t *read_file(const char *path, size_t *len_out) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return NULL;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fclose(f);
    return NULL;
  }
  long len = ftell(f);
  if (len < 0) {
    fclose(f);
    return NULL;
  }
  rewind(f);
  uint8_t *buf = malloc((size_t)len);
  if (buf == NULL) {
    fclose(f);
    return NULL;
  }
  if (fread(buf, 1, (size_t)len, f) != (size_t)len) {
    free(buf);
    fclose(f);
    return NULL;
  }
  fclose(f);
  *len_out = (size_t)len;
  return buf;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s CA_PEM CHAIN_PEM\n", argv[0]);
    return 1;
  }

  size_t ca_len = 0;
  size_t chain_len = 0;
  uint8_t *ca = read_file(argv[1], &ca_len);
  uint8_t *chain = read_file(argv[2], &chain_len);
  if (ca == NULL || chain == NULL) {
    free(ca);
    free(chain);
    return 1;
  }

  tls13_peer_identity *peer = NULL;
  bool ok = tls13_openssl_validate_chain_pem("localhost", ca, ca_len, chain, chain_len, &peer);
  if (!ok || peer == NULL) {
    fprintf(stderr, "expected localhost certificate validation to succeed\n");
    free(ca);
    free(chain);
    return 1;
  }
  tls13_openssl_peer_identity_free(peer);

  peer = NULL;
  ok = tls13_openssl_validate_chain_pem("not-localhost.example", ca, ca_len, chain, chain_len, &peer);
  if (ok || peer != NULL) {
    fprintf(stderr, "expected wrong-hostname certificate validation to fail\n");
    tls13_openssl_peer_identity_free(peer);
    free(ca);
    free(chain);
    return 1;
  }

  free(ca);
  free(chain);
  printf("OpenSSL X.509 stub tests passed\n");
  return 0;
}


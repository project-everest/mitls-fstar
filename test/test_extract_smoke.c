#include "TLS13_Extract_Smoke.h"

#include <stdio.h>

int main(void) {
  if (TLS13_Extract_Smoke_tls13_version_major() != 3U ||
      TLS13_Extract_Smoke_tls13_version_minor() != 4U) {
    fprintf(stderr, "unexpected extracted TLS version constants\n");
    return 1;
  }
  if (TLS13_Extract_Smoke_tls13_chacha20_poly1305_sha256() != 0x1303U) {
    fprintf(stderr, "unexpected extracted cipher-suite constant\n");
    return 1;
  }
  printf("extraction smoke test passed\n");
  return 0;
}

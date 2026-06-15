#include "TLS13_Impl_Server_Driver.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return 0;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    perror("fseek");
    fclose(f);
    return 0;
  }
  long len = ftell(f);
  if (len < 0) {
    perror("ftell");
    fclose(f);
    return 0;
  }
  if (fseek(f, 0, SEEK_SET) != 0) {
    perror("fseek");
    fclose(f);
    return 0;
  }
  uint8_t *buf = malloc((size_t)len == 0 ? 1 : (size_t)len);
  if (buf == NULL) {
    perror("malloc");
    fclose(f);
    return 0;
  }
  size_t read_len = fread(buf, 1, (size_t)len, f);
  if (read_len != (size_t)len || ferror(f)) {
    fprintf(stderr, "failed to read %s\n", path);
    free(buf);
    fclose(f);
    return 0;
  }
  fclose(f);
  *out = buf;
  *out_len = (size_t)len;
  return 1;
}

int main(void) {
  uint8_t *certificate_chain = NULL;
  uint8_t *private_key = NULL;
  size_t certificate_chain_len = 0;
  size_t private_key_len = 0;

  if (!read_file("test/certs/chain.pem", &certificate_chain, &certificate_chain_len) ||
      !read_file("test/certs/leaf.key", &private_key, &private_key_len)) {
    free(certificate_chain);
    free(private_key);
    return 1;
  }

  FStar_Pervasives_Native_option__TLS13_Impl_Server_Driver_State_server_driver created =
      TLS13_Impl_Server_Driver_new_server(
          certificate_chain,
          certificate_chain_len,
          private_key,
          private_key_len);

  free(certificate_chain);
  free(private_key);

  if (created.tag != FStar_Pervasives_Native_Some) {
    fprintf(stderr, "expected verified top-level server driver allocation to succeed\n");
    return 1;
  }

  printf("extracted Pulse top-level server driver API smoke test passed\n");
  return 0;
}

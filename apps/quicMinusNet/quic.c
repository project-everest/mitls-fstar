#include <stdio.h>
#include <memory.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/cdefs.h>
#if __APPLE__
#include <sys/errno.h> // OS/X only provides include/sys/errno.h
#else
#include <errno.h> // MinGW only provides include/errno.h
#include <malloc.h>
#endif
#include "mitlsffi.h"

int main(int argc, char **argv)
{
  char *errmsg;
  quic_result rc, rs;

  quic_config config = {
    .is_server = 1,
    .host_name = "",
    .qp = {
      .max_stream_data = 16000,
      .max_data = 32000,
      .max_stream_id = 16,
      .idle_timeout = 60
    },
    .certificate_chain_file = "../../data/test_chain.pem",
    .private_key_file = "../../data/server.key",
    .ca_file = "../../data/CAFile.pem",
    .cipher_suites = NULL, // Use defaults
    .signature_algorithms = NULL,
    .named_groups = "X25519",
    .ticket_enc_alg = NULL,
    .ticket_key = NULL,
    .ticket_key_len = 0,
    .enable_0rtt = 1
  };

  quic_state *server;
  quic_state *client;

  FFI_mitls_init();

  if(!FFI_mitls_quic_create(&server, &config, &errmsg))
  {
    printf("quic_create server failed: %s\n", errmsg);
    return -1;
  }

  config.is_server = 0;
  config.host_name = "localhost";

  if(!FFI_mitls_quic_create(&client, &config, &errmsg))
  {
    printf("quic_create client failed: %s\n", errmsg);
    return -1;
  }

  // server write buffer
  char *s_buffer = malloc(16*1024);
  size_t slen = 0;
  char *c_buffer = malloc(16*1024);
  size_t clen = 0;

 
  clen = 2048;
  rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
  slen = 2048;
  rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);


  FFI_mitls_cleanup();
  return 0;
}

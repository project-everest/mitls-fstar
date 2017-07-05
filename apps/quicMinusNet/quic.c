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

void dump(unsigned char buffer[], size_t len)
{
  int i; 
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

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

  printf("server create\n");
  if(!FFI_mitls_quic_create(&server, &config, &errmsg))
  {
    printf("quic_create server failed: %s\n", errmsg);
    return -1;
  }

  config.is_server = 0;
  config.host_name = "localhost";

  printf("client create\n");
  if(!FFI_mitls_quic_create(&client, &config, &errmsg))
  {
    printf("quic_create client failed: %s\n", errmsg);
    return -1;
  }

  // server writer buffer (cumulative)
  size_t slen = 0;
  size_t smax = 8*1024; // too much; we use < 1KB
  char *s_buffer = malloc(smax);

  // client write buffer (cumulative)
  size_t clen = 0;
  size_t cmax = 8*1024; // too much; we use < 1KB
  char *c_buffer = malloc(clen); // 


  do{
    c_buffer += clen; // assuming miTLS never returns a larger clen
    cmax -= clen;
    clen = cmax;

    printf("client call clen=%4d slen=%4d\n", clen, slen);
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    printf("client done clen=%4d slen=%4d rc=%d\n", clen, slen, rc);
    dump(c_buffer, clen);
    
    s_buffer += slen; // assuming miTLS never returns a larger clen
    smax -= slen;
    slen = smax;
    
    /* clen -= 12; // simulating fragmentation */
    /* printf("server call clen=%4d slen=%4d\n", clen, slen); */
    /* rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg); */
    /* printf("server done clen=%4d slen=%4d rc=%d\n", clen, slen, rc); */
    /* clen += 12; */

    printf("server call clen=%4d slen=%4d\n", clen, slen);
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    printf("server done clen=%4d slen=%4d rc=%d\n", clen, slen, rc);
    dump(s_buffer, slen);
  }
  while(rc != TLS_client_complete && rs != TLS_server_complete);

  FFI_mitls_cleanup();
  printf("Ok\n");
  return 0;
}

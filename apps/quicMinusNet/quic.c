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

// TLS library
#include "mitlsffi.h"
// Crypto library
#include "quic_provider.h"

void dump(unsigned char buffer[], size_t len)
{
  int i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

void dump_parameters(quic_transport_parameters *qp)
{
  printf("  max_stream_data = %d\n", qp->max_stream_data);
  printf("  max_data        = %d\n", qp->max_data);
  printf("  max_stream_id   = %d\n", qp->max_stream_id);
  printf("  idle_timeout    = %d\n", qp->idle_timeout);
  if (qp->others_len) printf("  other parameters= "); dump(qp->others, qp->others_len); 
}

char *quic_result_string(quic_result r){
  static char *codes[10] = {
    "would_block", "error_local", "error_alert", "client_early_data",
    "client_complete", "client_complete_early_data", "server_accept",
    "server_accept_early_data", "server_complete", "other_error" };
  if(r < 9) return codes[r];
  return codes[9];
}

int main(int argc, char **argv)
{
  char *errmsg;

  quic_config config = {
    .is_server = 1,
    .host_name = "",
    .qp = {
      .max_stream_data = 16000,
      .max_data = 32000,
      .max_stream_id = 16,
      .idle_timeout = 60,
      .others_len = 9,
      .others = { 9,9,0,5,10,11,12,13,14,0 }
    },
    .server_ticket = {
      .len = 0,
      .ticket = {0} } ,
    .certificate_chain_file = "../../data/server-ecdsa.crt",
    .private_key_file = "../../data/server-ecdsa.key",
    .ca_file = "../../data/CAFile.pem",
    .cipher_suites = NULL, // Use defaults
    .signature_algorithms = "ECDSA+SHA256",
    .named_groups = "X25519",
    .ticket_enc_alg = NULL,
    .ticket_key = NULL,
    .ticket_key_len = 0,
    .enable_0rtt = 1
  };

  quic_result rc, rs;
  quic_state *server = NULL, *client = NULL;
  quic_secret qs = {0}, qs_early = {0};
  quic_ticket qt = {0};

  FFI_mitls_init();

  // server writer buffer (cumulative)
  size_t slen = 0;
  size_t smax = 8*1024;
  char _sbuf[smax], *s_buffer = _sbuf;

  // client write buffer (cumulative)
  size_t clen = 0;
  size_t cmax = 8*1024;
  char _cbuf[cmax], *c_buffer = _cbuf;

  if (argc == 1) {
      // GENERIC HANDSHAKE TEST (NO 0RTT)

      int client_complete = 0;
      int server_complete = 0;

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

      do {
        c_buffer += clen; // assuming miTLS never returns a larger clen
        cmax -= clen;
        clen = cmax;

        printf("client call clen=%4d slen=%4d\n", clen, slen);
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
        printf("client done clen=%4d slen=%4d status=%s\n", clen, slen, quic_result_string(rc));
        dump(c_buffer, clen);

        client_complete |= rc == TLS_client_complete || rc == TLS_client_complete_with_early_data;
        if(rc == TLS_error_other || rc == TLS_error_local || rc == TLS_error_alert){
          printf("Stopping due to error code. Msg: %s\n", errmsg);
          break;
        }

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
        printf("sender done clen=%4d slen=%4d status=%s\n", clen, slen, quic_result_string(rs));
        dump(s_buffer, slen);

        server_complete |= rs == TLS_server_complete;
        if(rs == TLS_error_other || rs == TLS_error_local || rs == TLS_error_alert){
          printf("Stopping due to error code. Msg: %s\n", errmsg);
          break;
        }

      }
      while(!client_complete || !server_complete);

      FFI_mitls_quic_get_exporter(client, 0, &qs, &errmsg);
      FFI_mitls_quic_get_exporter(server, 0, &qs_early, &errmsg);
      if(memcmp(qs_early.secret, qs.secret, 64))
      {
        printf("  *** ERROR: exporter secrets do not match! ***\n");
        return 1;
      }

      printf("   === Exporter secret ===\n");
      dump(qs.secret, 32);

      quic_secret qs_client = {0}, qs_server = {0};
      quic_crypto_tls_derive_secret(&qs_client, &qs, "EXPORTER-QUIC client 1-RTT Secret");
      quic_crypto_tls_derive_secret(&qs_server, &qs, "EXPORTER-QUIC server 1-RTT Secret");

      printf("   === QUIC 1-RTT secrets ===\n");
      printf("C: "); dump(qs_client.secret, 32);
      printf("S: "); dump(qs_server.secret, 32);

      quic_key *k_client, *k_server;
      if(!quic_crypto_derive_key(&k_client, &qs_client) ||
         !quic_crypto_derive_key(&k_server, &qs_server))
      {
        printf("Failed to derive AEAD keys.\n");
        return 1;
      }

      char data[] = "Hello world";
      char cipher[sizeof(data)+15] = {0}; // NB: not NUL terminated
      const char ad[] = "<QUIC header>";

      printf("   === AEAD client key test ===\n");
      quic_crypto_encrypt(k_client, cipher, 0, ad, strlen(ad), data, strlen(data));
      dump(cipher, sizeof(cipher));
      memset(data, 0, sizeof(data));

      if(!quic_crypto_decrypt(k_client, data, 0, ad, strlen(ad), cipher, sizeof(cipher))
        || memcmp(data, "Hello world", sizeof(data)))
      {
        printf("AEAD encryption test failed.\n");
        return 1;
      }
      printf("   === Decrypt successful ===\n");

      quic_crypto_free_key(k_client);
      quic_crypto_free_key(k_server);
  }

  if (argc == 2) {
    // HANDSHAKE WALKTHROUGH; 0RTT then 1RTT

    printf("\n     INITIAL ECDHE HANDSHAKE (NO EARLY SECRET)\n\n");

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

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_would_block);
    printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), clen, slen);
    printf("ClientHello[%4d] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_accept);
    FFI_mitls_quic_get_exporter(server, 0, &qs, &errmsg);
    printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), clen, slen);
    printf("                        secret="); dump(qs.secret, 32);
    printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4d]\n\n",slen);

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_client_complete);
    FFI_mitls_quic_get_exporter(client, 0, &qs, &errmsg);
    printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), clen, slen);
    printf("secret="); dump(qs.secret, 32);
    printf("(Finished) [%4d] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_complete);
    printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), clen, slen);

    // NB we must call the server again to get a ticket
    c_buffer += clen; cmax -= clen; clen = 0;
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_would_block);
    printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), clen, slen);
    printf("                  <---- {Ticket}[%4d]\n\n", slen);

    clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_would_block);
    printf("client returns clen=%d slen=%d status=%s\n", clen, slen, quic_result_string(rc));

    if(FFI_mitls_quic_get_ticket(client, &qt, &errmsg))
    {
      printf("new ticket: \n");
      dump(qt.ticket, qt.len);
    }
    else printf("Failed to get ticket: %s\n", errmsg);

    printf("\n     TICKET-BASED RESUMPTION\n\n");

    FFI_mitls_quic_free(server);
    FFI_mitls_quic_free(client);

    config.is_server = 1;
    config.host_name = "";
    printf("server create\n");
    if(!FFI_mitls_quic_create(&server, &config, &errmsg))
      {
        printf("quic_create server failed: %s\n", errmsg);
        return -1;
      }
    config.is_server = 0;
    config.host_name = "localhost";
    config.server_ticket = qt;

    printf("client create\n");
    if(!FFI_mitls_quic_create(&client, &config, &errmsg))
      {
        printf("quic_create client failed: %s\n", errmsg);
        return -1;
      }

    s_buffer += slen; smax -= slen; slen = 0;
    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), clen, slen);
    assert(rc == TLS_client_early);
    FFI_mitls_quic_get_exporter(client, 1, &qs_early, &errmsg);
    printf("early secret="); dump(qs_early.secret, 32);
    printf("ClientHello[%4d] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_accept_with_early_data);
    printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), clen, slen);
    FFI_mitls_quic_get_exporter(server, 1, &qs_early, &errmsg);
    printf("                        early secret="); dump(qs_early.secret, 32);
    FFI_mitls_quic_get_exporter(server, 0, &qs, &errmsg);
    printf("                        secret="); dump(qs.secret, 32);
    printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4d]\n\n",slen);

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_client_complete_with_early_data);
    FFI_mitls_quic_get_exporter(client, 0, &qs, &errmsg);
    printf("client returns %s clen=%d slen=%d\n", quic_result_string(rc), clen, slen);
    printf("secret="); dump(qs.secret, 32);
    printf("(Finished) [%4d] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_complete);
    printf("                        server returns clen=%d slen=%d status=%s\n", clen, slen, quic_result_string(rs));

    // NB we must call the server again to get a ticket
    c_buffer += clen; cmax -= clen; clen = 0;
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_would_block);
    printf("                        server returns %s clen=%d slen=%d\n", quic_result_string(rs), clen, slen);
    printf("                  <---- {Ticket}[%4d]\n\n", slen);

    clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_would_block);
    printf("client returns clen=%d slen=%d status=%s\n", clen, slen, quic_result_string(rc));

    if(FFI_mitls_quic_get_ticket(client, &qt, &errmsg))
    {
      printf("new ticket:\n");
      dump(qt.ticket, qt.len);
    }
    else printf("Failed to get ticket: %s\n", errmsg);

    dump_parameters(&(config.qp));

    quic_transport_parameters peer[1];
    /*
    if (FFI_mitls_quic_get_peer_parameters(server, peer, &errmsg)) 
      {
        printf("Server received client parameters:\n");
        dump_parameters(peer);
      }
    else printf("Failed to get peer parameter: %s\n", errmsg);
    if (FFI_mitls_quic_get_peer_parameters(client, peer, &errmsg))
      {
        printf("Client received server parameters:\n");
        dump_parameters(peer);
      }
    else printf("Failed to get peer parameter: %s\n", errmsg);
    */
  }
    
  FFI_mitls_quic_free(server);
  FFI_mitls_quic_free(client);

  printf("Ok\n");
  return 0;
}

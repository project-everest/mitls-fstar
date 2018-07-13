#define __USE_MINGW_ANSI_STDIO 1
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
// PKI library
#include "mipki.h"

#define STATE_TYPE quic_state

// Definitions shared between old and new API
// e.g. callbacks, printers, etc.
#include "quic_common.c"

int main(int argc, char **argv)
{
  hs_type mode = handshake_simple;
  if(argc > 1)
  {
    if(!strcasecmp(argv[1], "0rtt"))
      mode = handshake_0rtt;
    if(!strcasecmp(argv[1], "0rtt-reject"))
      mode = handshake_0rtt_reject;
    if(!strcasecmp(argv[1], "hrr"))
      mode = handshake_stateless_retry;
  }

  // Server PKI configuration: one ECDSA certificate
  mipki_config_entry pki_config[1] = {
    {
      .cert_file = "../../data/server-ecdsa.crt",
      .key_file = "../../data/server-ecdsa.key",
      .is_universal = 1 // ignore SNI
    }
  };

  char *errmsg = NULL;
  int erridx;

  mipki_state *pki = mipki_init(pki_config, 1, NULL, &erridx);

  if(!pki)
  {
    printf("Failed to initialize PKI library: errid=%d\n", erridx);
    return 1;
  }

  if(!mipki_add_root_file_or_path(pki, "../../data/CAFile.pem"))
  {
    printf("Failed to add CAFile\n");
    return 1;
  }

  mitls_cert_cb cert_callbacks =
    {
      .select = certificate_select,
      .format = certificate_format,
      .sign = certificate_sign,
      .verify = certificate_verify
    };

  mitls_extension client_qtp[1] = {
    { // QUIC transport parameters (client)
      .ext_type = (uint16_t)0x1A,
      .ext_data = "\xff\xff\x00\x05\x0a\x0b\x0c\x0d\x0e\x00",
      .ext_data_len = 9
    }
  };

  mitls_alpn alpn = {
    .alpn = "hq-10",
    .alpn_len = 5
  };

  quic_config config = {
    .is_server = 1,
    .host_name = "",
    .alpn = &alpn,
    .alpn_count = 1,
    .server_ticket = NULL,
    .exts = client_qtp,
    .exts_count = 1,
    .callback_state = NULL,
    .ticket_callback = ticket_cb,
    .nego_callback = nego_cb,
    .cert_callbacks = &cert_callbacks,
    .cipher_suites = "TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256",
    .signature_algorithms = "ECDSA+SHA256:RSAPSS+SHA256",
    .named_groups = "X25519",
    .ticket_enc_alg = NULL,
    .ticket_key = NULL,
    .ticket_key_len = 0
  };

  quic_result rc, rs;
  connection_state server = {.quic_state=NULL, pki=pki };
  connection_state client = {.quic_state=NULL, pki=pki };
  quic_secret qs = {0}, qs_early = {0};

  FFI_mitls_init();

  // server writer buffer (cumulative)
  size_t slen = 0;
  size_t smax = 8*1024;
  char _sbuf[smax], *s_buffer = _sbuf;

  // client write buffer (cumulative)
  size_t clen = 0;
  size_t cmax = 8*1024;
  char _cbuf[cmax], *c_buffer = _cbuf;

  if (mode == handshake_simple)
  {
      // GENERIC HANDSHAKE TEST (NO 0RTT)

      int client_complete = 0;
      int server_complete = 0;

      printf("server create\n");
      config.callback_state = &server;
      if(!FFI_mitls_quic_create(&server.quic_state, &config))
        {
          printf("quic_create server failed: %s\n", errmsg);
          return -1;
        }
      config.is_server = 0;
      config.host_name = "localhost";

      printf("client create\n");
      config.callback_state = &client;
      if(!FFI_mitls_quic_create(&client.quic_state, &config))
        {
          printf("quic_create client failed: %s\n", errmsg);
          return -1;
        }

      do {
        c_buffer += clen; // assuming miTLS never returns a larger clen
        cmax -= clen;
        clen = cmax;

        printf("client call clen=%4zd slen=%4zd\n", clen, slen);
        rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
        printf("client done clen=%4zd slen=%4zd status=%s\n", clen, slen, quic_result_string(rc));
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
    /* printf("server call clen=%4zd slen=%4zd\n", clen, slen); */
    /* rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen); */
    /* printf("server done clen=%4zd slen=%4zd rc=%d\n", clen, slen, rc); */
    /* clen += 12; */

        printf("server call clen=%4zd slen=%4zd\n", clen, slen);
        rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
        printf("sender done clen=%4zd slen=%4zd status=%s\n", clen, slen, quic_result_string(rs));
        dump(s_buffer, slen);

        server_complete |= rs == TLS_server_complete;
        if(rs == TLS_error_other || rs == TLS_error_local || rs == TLS_error_alert){
          printf("Stopping due to error code. Msg: %s\n", errmsg);
          break;
        }

      }
      while(!client_complete || !server_complete);

/*
      if (FFI_mitls_quic_get_peer_parameters(server.quic_state, &ver, peer))
        {
          printf("   === server received client parameters === \n");
          printf(" Client initial version: %x\n", ver);
          dump_parameters(peer);
        }
      else printf("Failed to get peer parameter: %s\n", errmsg);

      peer->tp_len = 256;
      if (FFI_mitls_quic_get_peer_parameters(client.quic_state, &ver, peer))
        {
          printf("   === client received server parameters === \n");
          printf(" Server negotiated version: %x\n", ver);
          dump_parameters(peer);
        }
      else printf("Failed to get peer parameter: %s\n", errmsg);
*/

      FFI_mitls_quic_get_exporter(client.quic_state, 0, &qs);
      FFI_mitls_quic_get_exporter(server.quic_state, 0, &qs_early);
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
  else if(mode == handshake_0rtt || mode == handshake_0rtt_reject)
  {
    // HANDSHAKE WALKTHROUGH; 0RTT then 1RTT

    printf("\n     INITIAL ECDHE HANDSHAKE (NO EARLY SECRET)\n\n");

    printf("server create\n");
    config.callback_state = &server;
    if(!FFI_mitls_quic_create(&server.quic_state, &config))
      {
        printf("quic_create server failed: %s\n", errmsg);
        return -1;
      }
    config.is_server = 0;
    config.host_name = "localhost";

    printf("client create\n");
    config.callback_state = &client;
    if(!FFI_mitls_quic_create(&client.quic_state, &config))
      {
        printf("quic_create client failed: %s\n", errmsg);
        return -1;
      }

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_would_block);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("ClientHello[%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == TLS_server_accept);
    FFI_mitls_quic_get_exporter(server.quic_state, 0, &qs);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                        secret="); dump(qs.secret, 32);
    printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4zd]\n\n",slen);

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_client_complete);
    FFI_mitls_quic_get_exporter(client.quic_state, 0, &qs);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("secret="); dump(qs.secret, 32);
    printf("(Finished) [%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == TLS_server_complete);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);

    // NB we must call the server again to get a ticket
    c_buffer += clen; cmax -= clen; clen = 0;
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == TLS_would_block);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                  <---- {Ticket}[%4zd]\n", slen);

    clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_would_block);
    printf("client returns clen=%zd slen=%zd status=%s\n", clen, slen, quic_result_string(rc));

    printf("\n     TICKET-BASED RESUMPTION\n\n");

    if(qt == NULL)
    {
      printf("ERROR: no ticket received!\n");
      return -1;
    }

    if(mode == handshake_0rtt_reject)
      memset((char*)qt->ticket, 0, qt->ticket_len);

    FFI_mitls_quic_close(server.quic_state);
    FFI_mitls_quic_close(client.quic_state);

    config.is_server = 1;
    config.host_name = "";

    printf("server create\n");
    config.callback_state = &server;
    if(!FFI_mitls_quic_create(&server.quic_state, &config))
      {
        printf("quic_create server failed: %s\n", errmsg);
        return -1;
      }
    config.is_server = 0;
    config.host_name = "localhost";
    config.server_ticket = qt;

    printf("client create\n");
    config.callback_state = &client;
    if(!FFI_mitls_quic_create(&client.quic_state, &config))
      {
        printf("quic_create client failed: %s\n", errmsg);
        return -1;
      }

    s_buffer += slen; smax -= slen; slen = 0;
    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    assert(rc == TLS_client_early);
    FFI_mitls_quic_get_exporter(client.quic_state, 1, &qs_early);
    printf("early secret="); dump(qs_early.secret, 32);
    printf("ClientHello[%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == (mode == handshake_0rtt_reject ? TLS_server_accept : TLS_server_accept_with_early_data));
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    if(mode == handshake_0rtt) {
      FFI_mitls_quic_get_exporter(server.quic_state, 1, &qs_early);
      printf("                        early secret="); dump(qs_early.secret, 32);
      FFI_mitls_quic_get_exporter(server.quic_state, 0, &qs);
      printf("                        secret="); dump(qs.secret, 32);
    }
    printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4zd]\n\n",slen);

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == (mode == handshake_0rtt_reject ? TLS_client_complete : TLS_client_complete_with_early_data));
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    if(mode == handshake_0rtt) {
      FFI_mitls_quic_get_exporter(client.quic_state, 0, &qs);
      printf("secret="); dump(qs.secret, 32);
    }
    printf("(Finished) [%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == TLS_server_complete);
    printf("                        server returns clen=%zd slen=%zd status=%s\n", clen, slen, quic_result_string(rs));

    // NB we must call the server again to get a ticket
    c_buffer += clen; cmax -= clen; clen = 0;
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == TLS_would_block);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                  <---- {Ticket}[%4zd]\n", slen);

    clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_would_block);
    printf("client returns clen=%zd slen=%zd status=%s\n", clen, slen, quic_result_string(rc));
  }
  else if(mode == handshake_stateless_retry)
  {
    // STATELESS RETRY HANDSHAKE
    mitls_hello_summary ch;
    printf("\n     STATELESS RETRY TEST\n\n");

    printf("server create\n");
    config.callback_state = &server;
    if(!FFI_mitls_quic_create(&server.quic_state, &config))
      {
        printf("quic_create server failed: %s\n", errmsg);
        return -1;
      }

    config.is_server = 0;
    config.host_name = "localhost";

    printf("client create\n");
    config.callback_state = &client;
    if(!FFI_mitls_quic_create(&client.quic_state, &config))
      {
        printf("quic_create client failed: %s\n", errmsg);
        return -1;
      }

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_would_block);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("ClientHello[%4zd] ---->\n\n",clen);

    unsigned char *cookie; size_t cookie_len;
    assert(FFI_mitls_get_hello_summary(c_buffer, clen, 1, &ch, &cookie, &cookie_len) == 1);
    print_hello_summary(&ch, cookie, cookie_len);
    FFI_mitls_global_free(cookie);

    def_action = TLS_nego_retry; // Force server to ask for retry
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                  <---- HRR[%4zd]\n\n",slen);
    assert(rs == TLS_server_stateless_retry);
    def_action = TLS_nego_accept;

    // Kill the server (otherwise it defaults to stateful HRR)
    FFI_mitls_quic_close(server.quic_state);
    config.is_server = 1;
    config.callback_state = &server;
    printf("server re-create\n");
    if(!FFI_mitls_quic_create(&server.quic_state, &config))
      {
        printf("quic_create server failed: %s\n", errmsg);
        return -1;
      }

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_would_block);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("ClientHello2[%4zd] ---->\n\n",clen);

    assert(FFI_mitls_get_hello_summary(c_buffer, clen, 1, &ch, &cookie, &cookie_len) == 1);
    print_hello_summary(&ch, cookie, cookie_len);
    FFI_mitls_global_free(cookie);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    FFI_mitls_quic_get_exporter(server.quic_state, 0, &qs);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                        secret="); dump(qs.secret, 32);
    printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4zd]\n\n",slen);
    assert(rs == TLS_server_accept);

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_client_complete);
    FFI_mitls_quic_get_exporter(client.quic_state, 0, &qs);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("secret="); dump(qs.secret, 32);
    printf("(Finished) [%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == TLS_server_complete);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);

    // NB we must call the server again to get a ticket
    c_buffer += clen; cmax -= clen; clen = 0;
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server.quic_state, c_buffer, &clen, s_buffer, &slen);
    assert(rs == TLS_would_block);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                  <---- {Ticket}[%4zd]\n", slen);

    clen = cmax;
    rc = FFI_mitls_quic_process(client.quic_state, s_buffer, &slen, c_buffer, &clen);
    assert(rc == TLS_would_block);
    printf("client returns clen=%zd slen=%zd status=%s\n", clen, slen, quic_result_string(rc));
  }

  FFI_mitls_quic_close(server.quic_state);
  FFI_mitls_quic_close(client.quic_state);
  mipki_free(pki);

  printf("Ok\n");
  return 0;
}

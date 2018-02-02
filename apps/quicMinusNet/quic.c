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

void dump(const char *buffer, size_t len)
{
  int i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

void dump_parameters(quic_transport_parameters *qp)
{
  printf("transport parameters "); dump(qp->tp_data, qp->tp_len);
}

mitls_ticket *qt = NULL;

void ticket_cb(void *st, const char *sni, const mitls_ticket *ticket)
{
  printf("\n ##### New session ticket received! #####\n  Host: %s\n  Ticket:\n", sni);
  qt = malloc(sizeof(mitls_ticket));
  qt->ticket = malloc(ticket->ticket_len);
  qt->session = malloc(ticket->session_len);
  qt->ticket_len = ticket->ticket_len;
  qt->session_len = ticket->session_len;
  memcpy((void*)qt->ticket, ticket->ticket, qt->ticket_len);
  memcpy((void*)qt->session, ticket->session, qt->session_len);
  dump(qt->ticket, qt->ticket_len);
  printf(" ########################################\n");
}

void* certificate_select(void *cbs, const char *sni, const mitls_signature_scheme *sigalgs, size_t sigalgs_len, mitls_signature_scheme *selected)
{
  mipki_state *st = (mipki_state*)cbs;
  mipki_chain r = mipki_select_certificate(st, sni, sigalgs, sigalgs_len, selected);
  return (void*)r;
}

size_t certificate_format(void *cbs, const void *cert_ptr, char *buffer)
{
  mipki_state *st = (mipki_state*)cbs;
  mipki_chain chain = (mipki_chain)cert_ptr;
  return mipki_format_chain(st, cert_ptr, buffer, MAX_CHAIN_LEN);
}

size_t certificate_sign(void *cbs, const void *cert_ptr, const mitls_signature_scheme sigalg, const char *tbs, size_t tbs_len, char *sig)
{
  mipki_state *st = (mipki_state*)cbs;
  size_t ret = MAX_SIGNATURE_LEN;

  printf("======== TO BE SIGNED <%04x>: (%zd octets) ========\n", sigalg, tbs_len);
  dump(tbs, tbs_len);
  printf("===================================================\n");

  if(mipki_sign_verify(st, cert_ptr, sigalg, tbs, tbs_len, sig, &ret, MIPKI_SIGN))
    return ret;

  return 0;
}

int certificate_verify(void *cbs, const char* chain_bytes, size_t chain_len, const mitls_signature_scheme sigalg, const char *tbs, size_t tbs_len, char *sig, size_t sig_len)
{
  mipki_state *st = (mipki_state*)cbs;
  mipki_chain chain = mipki_parse_chain(st, chain_bytes, chain_len);

  if(chain == NULL)
  {
    printf("ERROR: failed to parse certificate chain");
    return 0;
  }

  // We don't validate hostname, but could with the callback state
  if(!mipki_validate_chain(st, chain, ""))
  {
    printf("WARNING: chain validation failed, ignoring.\n");
    // return 0;
  }

  size_t slen = sig_len;
  if(!mipki_sign_verify(st, chain, sigalg, tbs, tbs_len, sig, &slen, MIPKI_VERIFY))
  {
    printf("ERROR: invalid signature.\n");
    return 0;
  }

  mipki_free_chain(st, chain);
  return 1;
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
  // Server PKI configuration: one ECDSA certificate
  mipki_config_entry pki_config[1] = {
    {
      .cert_file = "../../data/server-ecdsa.crt",
      .key_file = "../../data/server-ecdsa.key",
      .is_universal = 1 // ignore SNI
    }
  };

  char *errmsg;
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

  quic_transport_parameters client_qp =
    {
      .tp_len = 6,
      .tp_data = "\x00\x05\x00\x02\x0f\xe4"
    };

  mitls_cert_cb cert_callbacks =
    {
      .select = certificate_select,
      .format = certificate_format,
      .sign = certificate_sign,
      .verify = certificate_verify
    };

  quic_transport_parameters server_qp =
    {
      // an example well-formed custom parameter
      .tp_len = 9,
      .tp_data = "\xff\xff\x00\x05\x0a\x0b\x0c\x0d\x0e\x00"
    };


  uint32_t versions[1] = {0xff000008};
  quic_config config = {
    .is_server = 1,
    .supported_versions = versions,
    .supported_versions_len = 1,
    .host_name = "",
    .alpn = "hq-08",
    .qp = server_qp,
    .server_ticket = NULL,
    .callback_state = (void*)pki,
    .ticket_callback = ticket_cb,
    .cert_callbacks = &cert_callbacks,
    .cipher_suites = "TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256",
    .signature_algorithms = "ECDSA+SHA256:RSAPSS+SHA256",
    .named_groups = "X25519",
    .ticket_enc_alg = NULL,
    .ticket_key = NULL,
    .ticket_key_len = 0,
    .enable_0rtt = 1
  };

  quic_result rc, rs;
  quic_state *server = NULL, *client = NULL;
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
      config.qp = client_qp;

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

        printf("client call clen=%4zd slen=%4zd\n", clen, slen);
        rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
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
    /* rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg); */
    /* printf("server done clen=%4zd slen=%4zd rc=%d\n", clen, slen, rc); */
    /* clen += 12; */

        printf("server call clen=%4zd slen=%4zd\n", clen, slen);
        rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
        printf("sender done clen=%4zd slen=%4zd status=%s\n", clen, slen, quic_result_string(rs));
        dump(s_buffer, slen);

        server_complete |= rs == TLS_server_complete;
        if(rs == TLS_error_other || rs == TLS_error_local || rs == TLS_error_alert){
          printf("Stopping due to error code. Msg: %s\n", errmsg);
          break;
        }

      }
      while(!client_complete || !server_complete);

      // showing how to get the peer's parameters
      // (available with the main exporter secret)
      quic_transport_parameters peer[1];
      peer->tp_len = 256;
      peer->tp_data = malloc(256);
      uint32_t ver;

      if (FFI_mitls_quic_get_peer_parameters(server, &ver, peer, &errmsg))
        {
          printf("   === server received client parameters === \n");
          printf(" Client initial version: %x\n", ver);
          dump_parameters(peer);
        }
      else printf("Failed to get peer parameter: %s\n", errmsg);

      peer->tp_len = 256;
      if (FFI_mitls_quic_get_peer_parameters(client, &ver, peer, &errmsg))
        {
          printf("   === client received server parameters === \n");
          printf(" Server negotiated version: %x\n", ver);
          dump_parameters(peer);
        }
      else printf("Failed to get peer parameter: %s\n", errmsg);

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
    config.qp = client_qp;

    printf("client create\n");
    if(!FFI_mitls_quic_create(&client, &config, &errmsg))
      {
        printf("quic_create client failed: %s\n", errmsg);
        return -1;
      }

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_would_block);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("ClientHello[%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_accept);
    FFI_mitls_quic_get_exporter(server, 0, &qs, &errmsg);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                        secret="); dump(qs.secret, 32);
    printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4zd]\n\n",slen);

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_client_complete);
    FFI_mitls_quic_get_exporter(client, 0, &qs, &errmsg);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("secret="); dump(qs.secret, 32);
    printf("(Finished) [%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_complete);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);

    // NB we must call the server again to get a ticket
    c_buffer += clen; cmax -= clen; clen = 0;
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_would_block);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                  <---- {Ticket}[%4zd]\n", slen);

    clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_would_block);
    printf("client returns clen=%zd slen=%zd status=%s\n", clen, slen, quic_result_string(rc));

    printf("\n     TICKET-BASED RESUMPTION\n\n");

    if(qt == NULL)
    {
      printf("ERROR: no ticket received!\n");
      return -1;
    }

    FFI_mitls_quic_free(server);
    FFI_mitls_quic_free(client);

    config.is_server = 1;
    config.host_name = "";
    config.qp = server_qp;

    printf("server create\n");
    if(!FFI_mitls_quic_create(&server, &config, &errmsg))
      {
        printf("quic_create server failed: %s\n", errmsg);
        return -1;
      }
    config.is_server = 0;
    config.host_name = "localhost";
    config.qp = client_qp;
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
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    assert(rc == TLS_client_early);
    FFI_mitls_quic_get_exporter(client, 1, &qs_early, &errmsg);
    printf("early secret="); dump(qs_early.secret, 32);
    printf("ClientHello[%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_accept_with_early_data);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    FFI_mitls_quic_get_exporter(server, 1, &qs_early, &errmsg);
    printf("                        early secret="); dump(qs_early.secret, 32);
    FFI_mitls_quic_get_exporter(server, 0, &qs, &errmsg);
    printf("                        secret="); dump(qs.secret, 32);
    printf("                  <---- ServerHello;(EncryptedExtensions; Certificate; CertVerify; Finished)[%4zd]\n\n",slen);

    c_buffer += clen; cmax -= clen; clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_client_complete_with_early_data);
    FFI_mitls_quic_get_exporter(client, 0, &qs, &errmsg);
    printf("client returns %s clen=%zd slen=%zd\n", quic_result_string(rc), clen, slen);
    printf("secret="); dump(qs.secret, 32);
    printf("(Finished) [%4zd] ---->\n\n",clen);

    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_server_complete);
    printf("                        server returns clen=%zd slen=%zd status=%s\n", clen, slen, quic_result_string(rs));

    // NB we must call the server again to get a ticket
    c_buffer += clen; cmax -= clen; clen = 0;
    s_buffer += slen; smax -= slen; slen = smax;
    rs = FFI_mitls_quic_process(server, c_buffer, &clen, s_buffer, &slen, &errmsg);
    assert(rs == TLS_would_block);
    printf("                        server returns %s clen=%zd slen=%zd\n", quic_result_string(rs), clen, slen);
    printf("                  <---- {Ticket}[%4zd]\n", slen);

    clen = cmax;
    rc = FFI_mitls_quic_process(client, s_buffer, &slen, c_buffer, &clen, &errmsg);
    assert(rc == TLS_would_block);
    printf("client returns clen=%zd slen=%zd status=%s\n", clen, slen, quic_result_string(rc));
  }

  FFI_mitls_quic_free(server);
  FFI_mitls_quic_free(client);
  mipki_free(pki);

  printf("Ok\n");
  return 0;
}

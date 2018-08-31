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

#define COMPLETE(ctx) (0 != ctx.flags & QFLAG_COMPLETE)

// Definitions shared between old and new API
// e.g. callbacks, printers, etc.
#include "quic_common.c"

void half_round(quic_state *my_state, quic_process_ctx *my_ctx, quic_process_ctx *peer_ctx, int *my_r, int *my_w, unsigned char *plain, unsigned char *cipher, size_t *plen, int is_server, int *my_ctr, int *peer_ctr)
{
  if(*plen && *my_r >= 0)
  {
    quic_raw_key k;
    assert(FFI_mitls_quic_get_record_key(my_state, &k, *my_r, QUIC_Reader));
    printf("[%c] R_Key[%d] = ", is_server?'S':'C', *my_r);
    dump(k.aead_key, k.alg ? 32 : 16);
    printf("[%c] R_IV[%d] = ", is_server?'S':'C', *my_r);
    dump(k.aead_iv, 12);
    printf("[%c] R_PN Key[%d] = ", is_server?'S':'C', *my_r);
    dump(k.pne_key, k.alg ? 32 : 16);
    quic_key *key;
    assert(quic_crypto_create(&key, k.alg, k.aead_key, k.aead_iv, k.pne_key));
    unsigned char tmp[2048];
    assert(quic_crypto_decrypt(key, tmp, *peer_ctr, tmp, 0, cipher, (*plen)+16));
    assert(!memcmp(tmp, plain, *plen));
    printf("[%c] Decrypt successful for PN=%d.\n", is_server?'S':'C', *peer_ctr);
    (*peer_ctr)++;
    quic_crypto_free_key(key);
    }
  
  printf("[%c] out_len=%d, in<%d>=\n", is_server?'S':'C',
    my_ctx->output_len, my_ctx->input_len);
  dump(my_ctx->input, my_ctx->input_len);

  size_t old_olen = my_ctx->output_len;
  if(!FFI_mitls_quic_process(my_state, my_ctx))
  {
    printf("[%c] Error %d returned.\n", is_server?'S':'C', my_ctx->tls_error);
    exit(my_ctx->tls_error & 255);
  }

  printf("[%c] Epochs: %d read, %d write\n", is_server?'S':'C',
    my_ctx->cur_reader_key, my_ctx->cur_writer_key);
  printf("[%c] Read %d, written %d, to_be_written %d\n", is_server?'S':'C',
    my_ctx->consumed_bytes, my_ctx->output_len, my_ctx->to_be_written);

  *plen = my_ctx->output_len;
  memcpy(plain, my_ctx->output, *plen);
  if(*plen && *my_w >= 0)
  {
    quic_raw_key k;
    assert(FFI_mitls_quic_get_record_key(my_state, &k, *my_w, QUIC_Writer));
    printf("[%c] W_Key[%d] = ", is_server?'S':'C', *my_w);
    dump(k.aead_key, k.alg ? 32 : 16);
    printf("[%c] W_IV[%d] = ", is_server?'S':'C', *my_w);
    dump(k.aead_iv, 12);
    printf("[%c] W_PN Key[%d] = ", is_server?'S':'C', *my_w);
    dump(k.pne_key, k.alg ? 32 : 16);
    quic_key *key;
    assert(quic_crypto_create(&key, k.alg, k.aead_key, k.aead_iv, k.pne_key));
    assert(quic_crypto_encrypt(key, cipher, *my_ctr, plain, 0, plain, *plen));
    printf("[%c] Encrypt successful for PN=%d.\n", is_server?'S':'C', *my_ctr);
    quic_crypto_free_key(key);
  }

  my_ctx->output += my_ctx->output_len;
  my_ctx->input += my_ctx->consumed_bytes;
  my_ctx->input_len -= my_ctx->consumed_bytes;
  peer_ctx->input_len += my_ctx->output_len;
  my_ctx->output_len = old_olen - my_ctx->output_len;
  
  if(my_ctx->cur_reader_key > *my_r) *my_r = my_ctx->cur_reader_key;
  if(my_ctx->cur_writer_key > *my_w) *my_w = my_ctx->cur_writer_key;
  if(my_ctx->flags & QFLAG_REJECTED_0RTT)
    printf("[%c] Server rejected our 0-RTT data!\n", is_server?'S':'C');
  if(my_ctx->flags & QFLAG_APPLICATION_KEY)
    printf("[%c] Application data can now be sent (%s)\n",
           is_server?'S':'C', *my_w == 0 ? "0-RTT" : "1-RTT");
}

void reset_ctx(quic_process_ctx *cctx, quic_process_ctx *sctx, unsigned char *cbuf, unsigned char *sbuf, size_t cmax, size_t smax)
{
  cctx->input = cbuf;
  cctx->input_len = 0;
  cctx->output = sbuf;
  cctx->output_len = smax;
  cctx->flags = 0;

  sctx->input = sbuf;
  sctx->input_len = 0;
  sctx->output = cbuf;
  sctx->output_len = cmax;
  sctx->flags = 0;
}

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
    .enable_0rtt = 1,
    .host_name = "localhost",
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

  connection_state server = {.quic_state=NULL, pki=pki };
  connection_state client = {.quic_state=NULL, pki=pki };

  FFI_mitls_init();

  size_t slen = 0, clen = 0, smax = 8*1024, cmax = 8*1024, plen;
  unsigned char sbuf[smax], cbuf[cmax], plain[2048], cipher[2048];
  quic_process_ctx cctx, sctx;
  int32_t cr = -1, cw = -1, sr = -1, sw = -1, cpn = 0, spn = 0;

  plen = 0;
  memset(plain, 0, sizeof(plain));
  memset(cipher, 0, sizeof(cipher));
  reset_ctx(&cctx, &sctx, cbuf, sbuf, cmax, smax);
  
  // GENERIC HANDSHAKE TEST (NO 0RTT)
  if (mode == handshake_simple)
  {
    printf("\n     1-RTT HANDSHAKE TEST\n\n");

    printf("[S] create\n");
    config.callback_state = &server;
    assert(FFI_mitls_quic_create(&server.quic_state, &config));

    config.is_server = 0;
    printf("[C] create\n");
    config.callback_state = &client;
    assert(FFI_mitls_quic_create(&client.quic_state, &config));
      
    for(int i = 0, post_hs = 0; post_hs < 2 ; i++)
    {
      // We need one extra round of post-handshake for NST
      if(COMPLETE(cctx) && COMPLETE(sctx)) post_hs++;
      
      printf("\n == Round %d ==\n\n", i);

      // Client half-round
      half_round(client.quic_state, &cctx, &sctx, &cr, &cw, plain, cipher, &plen, 0, &cpn, &spn);

      // Server half-round
      half_round(server.quic_state, &sctx, &cctx, &sr, &sw, plain, cipher, &plen, 1, &spn, &cpn);

      printf("\n == End round %d [CComplete=%d, SComplete=%d] ==\n\n", i, COMPLETE(cctx), COMPLETE(sctx));
    }
  }
  else if(mode == handshake_0rtt || mode == handshake_0rtt_reject)
  {
    printf("\n     1-RTT + 0-RTT TICKET RESUMPTION TEST\n\n");

    printf("[S] create\n");
    config.callback_state = &server;
    assert(FFI_mitls_quic_create(&server.quic_state, &config));

    config.is_server = 0;
    printf("[C] create\n");
    config.callback_state = &client;
    assert(FFI_mitls_quic_create(&client.quic_state, &config));
      
    for(int i = 0, post_hs = 0; post_hs < 2; i++)
    {
      // We need one extra round of post-handshake for NST
      if(COMPLETE(cctx) && COMPLETE(sctx)) post_hs++;
      
      printf("\n == Round %d ==\n\n", i);

      // Client half-round
      half_round(client.quic_state, &cctx, &sctx, &cr, &cw, plain, cipher, &plen, 0, &cpn, &spn);

      // Server half-round
      half_round(server.quic_state, &sctx, &cctx, &sr, &sw, plain, cipher, &plen, 1, &spn, &cpn);

      printf("\n == End round %d [CComplete=%d, SComplete=%d] ==\n\n", i, COMPLETE(cctx), COMPLETE(sctx));
    }
    
    printf("\n     TICKET-BASED RESUMPTION\n\n");

    if(qt == NULL)
    {
      printf("ERROR: no ticket received!\n");
      return -1;
    }

    // Corrupt ticket ID
    if(mode == handshake_0rtt_reject)
      memset((char*)qt->ticket, 0, 8);

    FFI_mitls_quic_free(server.quic_state);
    FFI_mitls_quic_free(client.quic_state);
    reset_ctx(&cctx, &sctx, cbuf, sbuf, cmax, smax);
    cr = -1; sr = -1; cw = -1; sw = -1;

    printf("[S] create\n");
    config.is_server = 1;
    config.callback_state = &server;
    assert(FFI_mitls_quic_create(&server.quic_state, &config));

    config.is_server = 0;
    printf("[C] create with ticket<%d> = ", qt->ticket_len);
    dump(qt->ticket, qt->ticket_len);
    config.callback_state = &client;
    config.server_ticket = qt;
    assert(FFI_mitls_quic_create(&client.quic_state, &config));
      
    for(int i = 0, post_hs = 0; post_hs < 2; i++)
    {
      // We need one extra round of post-handshake for NST
      if(COMPLETE(cctx) && COMPLETE(sctx)) post_hs++;
      
      printf("\n == Round %d ==\n\n", i);

      // Client half-round
      half_round(client.quic_state, &cctx, &sctx, &cr, &cw, plain, cipher, &plen, 0, &cpn, &spn);

      // Server half-round
      half_round(server.quic_state, &sctx, &cctx, &sr, &sw, plain, cipher, &plen, 1, &spn, &cpn);

      printf("\n == End round %d [CComplete=%d, SComplete=%d] ==\n\n", i, COMPLETE(cctx), COMPLETE(sctx));
    }
  }

  FFI_mitls_quic_free(server.quic_state);
  FFI_mitls_quic_free(client.quic_state);
  mipki_free(pki);

  printf("Ok\n");
  return 0;
}


typedef enum {
  handshake_simple,
  handshake_0rtt,
  handshake_0rtt_reject,
  handshake_stateless_retry
} hs_type;

typedef struct {
    STATE_TYPE *quic_state;
    mipki_state *pki;
} connection_state;

void dump(const char *buffer, size_t len)
{
  int i;
  for(i=0; i<len; i++) {
    printf("%02x", buffer[i] & 0xFF);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

const char* pvname(mitls_version pv)
{
  switch(pv)
  {
    case TLS_SSL3: return "SSL 3.0";
    case TLS_1p0: return "TLS 1.0";
    case TLS_1p1: return "TLS 1.1";
    case TLS_1p2: return "TLS 1.2";
    case TLS_1p3: return "TLS 1.3";
  }
  return "(unknown)";
}

void print_hello_summary(mitls_hello_summary *ch, unsigned char *cookie, size_t cookie_len)
{
  printf("~~~~~~~~~ Client Hello Summary ~~~~~~~~~~~\n");
  printf("~ SNI = %s\n", ch->sni ? ch->sni : (const unsigned char*)"NULL");
  printf("~ ALPN = ");
  if(ch->alpn) dump(ch->alpn, ch->alpn_len);
  else printf("NULL\n");
  printf("~ Cookie = ");
  if(cookie) dump(cookie, cookie_len);
  else printf("NULL\n");
  printf("~ Extensions = ");
  if(ch->extensions) dump(ch->extensions, ch->extensions_len);
  else printf("NULL\n");
  printf("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
}

mitls_nego_action def_action = TLS_nego_accept;

mitls_nego_action nego_cb(void *cb_state, mitls_version ver,
  const unsigned char *cexts, size_t cexts_len, mitls_extension **custom_exts,
  size_t *custom_exts_len, unsigned char **cookie, size_t *cookie_len)
{
  printf(" @@@@ Nego callback for %s @@@@\n", pvname(ver));
  printf("Offered extensions:\n");
  dump(cexts, cexts_len);

  connection_state *state = (connection_state*)cb_state;
  unsigned char *qtp = NULL;
  size_t qtp_len;
  int r = FFI_mitls_find_custom_extension(1, cexts, cexts_len, (uint16_t)0x1A, &qtp, &qtp_len);
  assert(r && qtp != NULL && qtp_len > 0);
  printf("Transport parameters offered:\n");
  dump(qtp, qtp_len);

  if(*cookie != NULL && *cookie_len > 0) {
    printf("Stateless cookie found, application contents:\n");
    dump(*cookie, *cookie_len);
  } else {
    printf("No application cookie (fist connection).\n");
  }

  // only used when TLS_nego_retry is returned, but it's safe to set anyway
  *cookie = "Hello World";
  *cookie_len = 11;

  *custom_exts = malloc(sizeof(mitls_extension));
  *custom_exts_len = 1;
  custom_exts[0]->ext_type = (uint16_t)0x1a;
  custom_exts[0]->ext_data = "\x00\x01\x02";
  custom_exts[0]->ext_data_len = 3;
  printf("Adding server transport parameters:\n");
  dump(custom_exts[0]->ext_data, custom_exts[0]->ext_data_len);

  printf(" @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n");
  fflush(stdout);
  return def_action;
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

void* certificate_select(void *cbs, mitls_version ver, const unsigned char *sni, size_t sni_len, const unsigned char *alpn, size_t alpn_len, const mitls_signature_scheme *sigalgs, size_t sigalgs_len, mitls_signature_scheme *selected)
{
  connection_state *state = (connection_state*)cbs;
  mipki_chain r = mipki_select_certificate(state->pki, sni, sni_len, sigalgs, sigalgs_len, selected);
  return (void*)r;
}

size_t certificate_format(void *cbs, const void *cert_ptr, unsigned char *buffer)
{
  connection_state *state = (connection_state*)cbs;
  mipki_chain chain = (mipki_chain)cert_ptr;
  return mipki_format_chain(state->pki, cert_ptr, buffer, MAX_CHAIN_LEN);
}

size_t certificate_sign(void *cbs, const void *cert_ptr, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, unsigned char *sig)
{
  connection_state *state = (connection_state*)cbs;
  size_t ret = MAX_SIGNATURE_LEN;

  printf("======== TO BE SIGNED <%04x>: (%zd octets) ========\n", sigalg, tbs_len);
  dump(tbs, tbs_len);
  printf("===================================================\n");

  if(mipki_sign_verify(state->pki, cert_ptr, sigalg, tbs, tbs_len, sig, &ret, MIPKI_SIGN))
    return ret;

  return 0;
}

int certificate_verify(void *cbs, const unsigned char* chain_bytes, size_t chain_len, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, const unsigned char *sig, size_t sig_len)
{
  connection_state *state = (connection_state*)cbs;
  mipki_chain chain = mipki_parse_chain(state->pki, chain_bytes, chain_len);

  if(chain == NULL)
  {
    printf("ERROR: failed to parse certificate chain");
    return 0;
  }

  // We don't validate hostname, but could with the callback state
  if(!mipki_validate_chain(state->pki, chain, ""))
  {
    printf("WARNING: chain validation failed, ignoring.\n");
    // return 0;
  }

  size_t slen = sig_len;
  if(!mipki_sign_verify(state->pki, chain, sigalg, tbs, tbs_len, (char*)sig, &slen, MIPKI_VERIFY))
  {
    printf("ERROR: invalid signature.\n");
    return 0;
  }

  mipki_free_chain(state->pki, chain);
  return 1;
}

char *quic_result_string(quic_result r){
  static char *codes[11] = {
    "would_block", "error_local", "error_alert", "client_early_data",
    "client_complete", "client_complete_early_data", "server_accept",
    "server_accept_early_data", "server_complete", "server_stateless_retry",
    "other_error" };
  if(r < 10) return codes[r];
  return codes[10];
}

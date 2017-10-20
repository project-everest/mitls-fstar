/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509v3.h>

#include "mipki.h"
#define DEBUG 1

/*
 DESIGN NOTES

 This file is meant to implement the certificate callbacks for TLS:

 typedef void* (MITLS_CALLCONV *pfn_FFI_cert_select_cb)(void *cb_state, const char *sni, const mitls_signature_scheme *sigalgs, size_t sigalgs_len, mitls_signature_scheme *selected);
 typedef size_t (MITLS_CALLCONV *pfn_FFI_cert_format_cb)(void *cb_state, const void *cert_ptr, char buffer[MAX_CHAIN_LEN]);
 typedef size_t (MITLS_CALLCONV *pfn_FFI_cert_sign_cb)(void *cb_state, const void *cert_ptr, const mitls_signature_scheme sigalg, const char *tbs, size_t tbs_len, char *sig);
 typedef int (MITLS_CALLCONV *pfn_FFI_cert_verify_cb)(void *cb_state, const char* chain, size_t chain_len, const mitls_signature_scheme sigalg, const char *tbs, size_t tbs_len, char *sig, size_t sig_len);

On the server side, we maintain a pre-declared certificate configuration.
Chains and private keys are loaded when the library is initialized and stay in memory

The certificates are configured in order of preference.
Certificate selection first matches the SNI against the names in the certificates,
then looks at the supported signature algorithms and tries to pick one compatible
with the private key.

*/


// The parsed representation of chains and private keys
typedef struct {
  X509* endpoint;
  STACK_OF(X509) *intermediates;
  EVP_PKEY* key;
  int is_universal;
} config_entry;

/********************** GLOBAL VARIABLES ***********************/
// We cache the loading of certificate chains and private keys
// They remain in memory until mipki_cleanup() is called
X509_STORE *g_store = NULL;
config_entry *g_config = NULL;
size_t g_config_len = 0;


/* CODE POINTS FOR SIGNATURE ALGORITHMS
  rsa_pkcs1_sha1(0x0201),
  rsa_pkcs1_sha256(0x0401),
  rsa_pkcs1_sha384(0x0501),
  rsa_pkcs1_sha512(0x0601),

  rsa_pss_sha256(0x0804),
  rsa_pss_sha384(0x0805),
  rsa_pss_sha512(0x0806),

  ecdsa_sha1(0x0203),
  ecdsa_secp256r1_sha256(0x0403),
  ecdsa_secp384r1_sha384(0x0503),
  ecdsa_secp521r1_sha512(0x0603),

  ed25519(0x0807),
  ed448(0x0808),
*/

// Debugging function to inspect certificates loaded by the store
static int cert_verify_cb(int ok, X509_STORE_CTX *ctx)
{
#ifdef DEBUG
    char buf[512];
    static int cb_index = 0;

    printf("Starting cb #%d (ok = %d)\n", ++cb_index, ok);
    if(X509_STORE_CTX_get_error(ctx) == X509_V_OK) {
      printf("Callback reports no error.\n");
    } else {
      printf("Error string = '%s'\n",
        X509_verify_cert_error_string(X509_STORE_CTX_get_error(ctx)));
    }

    X509 *cur = X509_STORE_CTX_get0_cert(ctx);
    X509_NAME_oneline(X509_get_subject_name(cur), buf, 256);
    printf("current_cert subject:   %s\n",buf);
    X509_NAME_oneline(X509_get_issuer_name(cur), buf, 256);
    printf("current_cert issuer:    %s\n",buf);
#endif

    return ok;
}

typedef struct {
  password_callback cb;
  const char *info;
} pass_cb_state;

int password_cb(char *buf, int size, int rwflag, void *p)
{
  pass_cb_state *s = (pass_cb_state*)p;
  if(s == NULL || s->cb == NULL) return 0;

  #if DEBUG
  printf("Calling passwork callback for <%s>\n", (char*)s->info);
  #endif

  return s->cb(buf, size, s->info);
}

void mipki_cleanup()
{
  for(size_t i=0; i<g_config_len; i++)
  {
    config_entry *cfg = g_config + i;
    X509_free(cfg->endpoint);
    EVP_PKEY_free(cfg->key);
    sk_X509_pop_free(cfg->intermediates, X509_free);
  }

  free(g_config);
  g_config = NULL;
  g_config_len = 0;

  X509_STORE_free(g_store);
  g_store = NULL;

  OPENSSL_thread_stop();
}

int mipki_init(const mipki_config_entry config[], size_t config_len, password_callback pcb, int *erridx)
{
  *erridx = -1;

  if(g_config != NULL) return 0;
  if(!OPENSSL_init_crypto(OPENSSL_INIT_LOAD_CRYPTO_STRINGS, NULL))
    return 0;

  g_store = X509_STORE_new();
  if(!g_store) return 0;

  if(!X509_STORE_set_default_paths(g_store)) return 0;
  X509_STORE_set_verify_cb_func(g_store, cert_verify_cb);

  g_config = malloc(sizeof(config_entry) * config_len);
  if(!g_config) return 0;

  for(size_t i = 0; i < config_len; i++)
  {
    *erridx = i;
    config_entry *cfg = g_config + i;
    const mipki_config_entry *cur = config + i;
    pass_cb_state cbs = {.cb = pcb, .info = cur->key_file};

    STACK_OF(X509) *chain = sk_X509_new_null();
    X509 *x509 = NULL;

    if(!chain) return 0;

    BIO *bio = BIO_new_file(cur->key_file, "r");
    if(!bio) return 0;

    EVP_PKEY* sk = PEM_read_bio_PrivateKey(bio, NULL, password_cb, (void*)&cbs);
    if(!sk || !BIO_free(bio)) return 0;

    bio = BIO_new_file(cur->cert_file, "r");
    if(!bio) return 0;

    for(size_t j = 0; ; j++)
    {
      x509 = PEM_read_bio_X509_AUX(bio, NULL, NULL, NULL);

      if(!x509) {
        int n = ERR_peek_last_error();

        if(!j || !(ERR_GET_LIB(n) == ERR_LIB_PEM && ERR_GET_REASON(n) == PEM_R_NO_START_LINE))
          return 0;
        else
          break; // Chain is complete, allegedly
      }

      // Check that the private key matches the first certificate in the file
      if(!j) {
        if(!X509_check_private_key(x509, sk))
          return 0;

        cfg->endpoint = x509;
      } else {
        sk_X509_push(chain, x509);
      }
    }

    g_config_len++;
    cfg->intermediates = chain;
    cfg->key = sk;
    cfg->is_universal = cur->is_universal;
  }

  return 1;
}

int mipki_add_root_file_or_path(const char *ca_file)
{
  if(g_store == NULL) return 0;
  struct stat sb;

  if(!stat(ca_file, &sb)){
    #if DEBGUG
    printf("mipki_add_root_file_or_path: stat failed\n");
    #endif
    return 0;
  }

  if(S_ISDIR(sb.st_mode))
    return X509_STORE_load_locations(g_store, NULL, ca_file);

  return X509_STORE_load_locations(g_store, ca_file, NULL);
}

mipki_chain mipki_select_certificate(const char *sni, mipki_signature *algs, size_t algs_len, mipki_signature *selected)
{
  if(g_config == NULL)
  {
    #if DEBUG
      printf("The library must be initialized first with mipki_init!\n");
    #endif
    return 0;
  }

  #if DEBUG
    printf("Selecting certificate for <%s>, signatures=", sni);
    for(size_t j = 0; j < algs_len; j++) printf("%04x ", algs[j]);
    printf("\n");
  #endif

  for(size_t i = 0; i < g_config_len; i++)
  {
    config_entry *cfg = g_config + i;

    #if DEBUG
      char buf[256];
      char *peername = NULL;
      char **peer = &peername;
      X509_NAME_oneline(X509_get_subject_name(cfg->endpoint), buf, 256);
      printf(" - Testing certificate: %s\n", buf);
    #else
      char **peer = NULL; // save memory
    #endif

    // Server-side hostname validation to match wildcards, SAN, etc
    if(cfg->is_universal || X509_check_host(cfg->endpoint, sni, strlen(sni), 0, peer))
    {
      #if DEBUG
      printf(" - Positive match for <%s>\n", peername);
      OPENSSL_free(peername);
      #endif

      int curve, kt = EVP_PKEY_base_id(cfg->key);
      *selected = 0;

      #if DEBUG
        switch(kt){
          case EVP_PKEY_RSA:     printf(" - RSA key\n"); break;
          case EVP_PKEY_EC:      printf(" - ECDSA key\n"); break;
          case EVP_PKEY_ED25519: printf(" - EdDSA-25519 key\n"); break;
        }
      #endif

      // TLS < 1.2
      if(algs_len == 0 && kt == EVP_PKEY_RSA)
        *selected = 0xFFFF; // MD5+SHA1 RSA
      if(algs_len == 0 && kt == EVP_PKEY_EC)
        *selected = 0x0203; // ECDSA+SHA1

      for(size_t j = 0; j < algs_len; j++)
      {
        mipki_signature alg = algs[j];
        uint8_t low = algs[j] & 0xFF;
        uint8_t high = algs[j] >> 8;

        #if DEBUG
        printf(" - Testing if <%02x,%02x> is suitable\n", high, low);
        #endif

        switch(kt)
        {
          case EVP_PKEY_RSA:
            if((high == 8 && (low == 4 || low == 5 || low == 6)) || // RSA_PSS
               (low == 1 && high >= 2 && high <= 6)) // RSA_PKCS1
              *selected = alg;
            break;

          case EVP_PKEY_ED25519:
            if(high == 8 && low == 7)
              *selected = alg;
            break;

          case EVP_PKEY_EC:
            curve = EC_GROUP_get_curve_name(EC_KEY_get0_group(EVP_PKEY_get0_EC_KEY(cfg->key)));
            if((curve == NID_X9_62_prime256v1 && high == 4 && low == 3) ||
               (curve == NID_secp384r1 && high == 5 && low == 3) ||
               (curve == NID_secp521r1 && high == 6 && low == 3) ||
               (high == 2 && low == 3))
              *selected = alg;
            break;
        }

        if(*selected)
        {
          #if DEBUG
            printf(" + Certificate selected with alg=%04x\n", *selected);
          #endif
          break;
        }
      }

      if(*selected)
        return (void*)cfg;
    }
  }

  *selected = 0;
  return NULL;
}
/*
int EVP_DigestSignInit(EVP_MD_CTX *ctx, EVP_PKEY_CTX **pctx,
                       const EVP_MD *type, ENGINE *e, EVP_PKEY *pkey);
int EVP_DigestSignUpdate(EVP_MD_CTX *ctx, const void *d, size_t cnt);
int EVP_DigestSignFinal(EVP_MD_CTX *ctx, unsigned char *sig, size_t *siglen);
*/

typedef const EVP_MD* DIGEST;

static DIGEST sha(int variant) {
    switch (variant) {
      case 0: return EVP_sha256();
      case 1: return EVP_sha384();
      case 2: return EVP_sha512();
    }
    return NULL;
}

static int set_digest(mipki_signature sigalg, DIGEST* md)
{
  // N.B. ed25519 and ed448 expect NULL md
  switch(sigalg)
  {
    case 0x0804: // rsa_pss_sha256
    case 0x0805: // rsa_pss_sha384
    case 0x0806: // rsa_pss_sha512
      *md = sha(sigalg - 0x0804);
      break;

    case 0x0401: // rsa_pkcs1_sha256
    case 0x0501: // rsa_pkcs1_sha384
    case 0x0601: // rsa_pkcs1_sha512
    case 0x0403: // ecdsa_secp256r1_sha256
    case 0x0503: // ecdsa_secp384r1_sha384
    case 0x0603: // ecdsa_secp521r1_sha512
      *md = sha((sigalg>>8) - 4);
      break;

    case 0x0203: // ecdsa_sha1
    case 0x0201: // rsa_pkcs1_sha1
      *md = EVP_sha1();
      break;

    case 0x0807: // ed25519
    case 0x0808: // ed448
      *md = NULL;
      break;

    default:
      #if DEBUG
        printf("set_md: unknown algorithm %04x\n", sigalg);
      #endif
      return 0; // unrecognized siganture alg
  }

  return 1;
}

int mipki_sign_verify(const mipki_chain cert_ptr, const mipki_signature sigalg, const char *tbs, size_t tbs_len, char *sig, size_t *sig_len, mipki_mode mode)
{
  config_entry *cfg = (config_entry*)cert_ptr;
  assert(cfg != NULL);
  int ret = 0;

  // Special case: MD5+SHA1 signature
  // we use a different signing interface
  if(sigalg == 0xffff)
  {
    RSA *rsa = EVP_PKEY_get0_RSA(cfg->key); // doesn't copy, no free
    unsigned int slen = (unsigned int)*sig_len;
    if(!rsa) return 0;

    if(mode == MIPKI_SIGN)
    {
      if (RSA_sign(NID_md5_sha1, tbs, tbs_len, sig, &slen, rsa) != 1) {
        #if DEBUG
          unsigned long err = ERR_peek_last_error();
          char* err_string = ERR_error_string(err, NULL);
          printf("RSA MD5_SHA1 signing error: %s\n", err_string);
          OPENSSL_free(err_string);
        #endif
        return 0;
      }
      *sig_len = slen;
      return 1;
    }
    else
    {
      return RSA_verify(NID_md5_sha1, tbs, tbs_len, sig, slen, rsa);
    }
  }

  EVP_PKEY_CTX* key_ctx = NULL;
  DIGEST md = NULL;
  EVP_MD_CTX *md_ctx = EVP_MD_CTX_new();

  int kt = EVP_PKEY_base_id(cfg->key);
  if(!set_digest(sigalg, &md)) return 0;

  if(EVP_DigestSignInit(md_ctx, &key_ctx, md, NULL, cfg->key) != 1)
  {
    #if DEBUG
      printf("mipki_sign: failed to initialize DigestSign\n");
    #endif
    return 0;
  }

  // for RSA: set padding
  if(kt == EVP_PKEY_RSA)
  {
    if(sigalg >> 8 == 8) // PSS
    {
      if(EVP_PKEY_CTX_set_rsa_padding(key_ctx, RSA_PKCS1_PSS_PADDING) != 1)
        return 0;
      if(EVP_PKEY_CTX_set_rsa_pss_saltlen(key_ctx, RSA_PSS_SALTLEN_DIGEST) != 1)
        return 0;
    }
    else // PKCS1
    {
      if (EVP_PKEY_CTX_set_rsa_padding(key_ctx, RSA_PKCS1_PADDING) != 1)
        return 0;
    }
  }

  if(mode == MIPKI_SIGN)
  {
    ret = EVP_DigestSign(md_ctx, sig, sig_len, tbs, tbs_len);
    if(ret != 1)
    {
      #if DEBUG
        unsigned long err = ERR_peek_last_error();
        char* err_string = ERR_error_string(err, NULL);
        printf("mipki_sign DigestSign error: %s\n", err_string);
        OPENSSL_free(err_string);
      #endif
    }
  }
  else // MIPKI_VERIFY
  {
    ret = EVP_DigestVerify(md_ctx, sig, *sig_len, tbs, tbs_len);
  }

  EVP_MD_CTX_free(md_ctx);
  return ret;
}

mipki_chain mipki_parse_chain(const char *chain, size_t chain_len)
{
  const char *cur = chain;
  const char *end = cur + chain_len;

  // We delay allocation of a long-lived heap version until the whole chain is parsed
  config_entry c = {
    .endpoint = NULL,
    .intermediates = sk_X509_new_null(),
    .key = NULL
  };

  do {
    if(end - cur < 3)
    {
      #if DEBUG
        printf("mipki_parse_chain: not enough bytes\n");
      #endif
      goto fail;
    }

    uint8_t *cur_u8 = (uint8_t*)cur;
    size_t cert_len = (cur_u8[0]<<16) + (cur_u8[1]<<8) + cur_u8[2];
    cur += 3;

    if(cur + cert_len > end)
    {
      #if DEBUG
        printf("mipki_parse_chain: certificate length overflows buffer size");
      #endif
      goto fail;
    }

    // The following call also does cur += cert_len
    X509 *x509 = d2i_X509(NULL, (const unsigned char**)&cur, cert_len);
    if(x509 == NULL)
    {
      #if DEBUG
        printf("mipki_parse_chain: failed to parse certificate");
      #endif
      goto fail;
    }

    if(c.endpoint == NULL) {
      c.endpoint = x509;
    } else {
      sk_X509_push(c.intermediates, x509);
    }
  } while(cur < end);

  if(c.endpoint != NULL)
  {
    c.key = X509_get_pubkey(c.endpoint);
    config_entry *res = malloc(sizeof(c));
    *res = c;
    return res;
  }

  // Ugly, but we really do not want memory leaks in this function
  fail:
    if(c.endpoint != NULL) X509_free(c.endpoint);
    sk_X509_pop_free(c.intermediates, X509_free);
    return NULL;
}

int mipki_format_chain(const mipki_chain chain, char *buffer, size_t buffer_len)
{

}

int mipki_validate_chain(const mipki_chain chain, const char *host)
{
  config_entry *cfg = (config_entry*)chain;
  assert(cfg != NULL);
  X509_STORE_CTX *ctx = X509_STORE_CTX_new();
  X509_VERIFY_PARAM *param = X509_VERIFY_PARAM_new();
  time_t current_time = time(NULL);

  if(!ctx || !param)
  {
    #if DEBUG
    printf("mipki_validate_chain: failed to initialize certificate validation context");
    #endif
    return 0;
  }

  X509_VERIFY_PARAM_set_flags(param, X509_V_FLAG_USE_CHECK_TIME | X509_V_FLAG_CRL_CHECK_ALL);
  X509_VERIFY_PARAM_set_time(param, current_time);
  X509_VERIFY_PARAM_set1_host(param, host, 0);
  X509_STORE_set1_param(g_store, param);
  X509_STORE_CTX_init(ctx, g_store, cfg->endpoint, cfg->intermediates);

  int r = X509_verify_cert(ctx);
  #if DEBUG
    printf("mipki_validate_chain = %d [%s]\n", r, X509_verify_cert_error_string(X509_STORE_CTX_get_error(ctx)));
  #endif

  X509_STORE_CTX_free(ctx);
  X509_VERIFY_PARAM_free(param);
  return r;
}

void mipki_free_chain(mipki_chain chain)
{
  config_entry *cfg = (config_entry*)chain;
  if(cfg == NULL) return;

  X509_free(cfg->endpoint);
  EVP_PKEY_free(cfg->key);
  sk_X509_pop_free(cfg->intermediates, X509_free);

  free(cfg);
}

/*
static void* get_key(X509* x509, key_type *type)
{
  *type = key_unknown;
  EVP_PKEY* pk = X509_get_pubkey(x509);
  if(!pk) return NULL;

  switch(EVP_PKEY_base_id(pk))
  {
    case EVP_PKEY_RSA:
      RSA* rsa = EVP_PKEY_get1_RSA(pk);
      *type = key_rsa;
      return (void*)rsa;

    case EVP_PKEY_DSA:
      DSA* dsa = EVP_PKEY_get1_DSA(pk);
      *type = key_dsa;
      return (void*)dsa;
      if (!dsa) CAMLreturn(Val_none);
      (void) DSA_set_method(dsa, DSA_OpenSSL());
      DSA_val(mldsa) = dsa;
      mlkey = caml_alloc(1, 1); // CertDSA
      Store_field(mlkey, 0, mldsa);
      break;

    case EVP_PKEY_EC:
      mlec = caml_alloc_custom(&key_ops, sizeof(EC_KEY*), 0, 1);
      EC_KEY* eck = EVP_PKEY_get1_EC_KEY(pk);
      break;

    default:
      CAMLreturn(Val_none);
  }
}*/

/*
size_t ocaml_ecdsa_sign(EC_KEY *key, const char *data, size_t data_len, char *output)
{
  size_t olen;
  if (ECDSA_sign(0, data, data_len, output, &olen, key) == 0) {
    return 0;
  }
  return olen;
}

int ocaml_ecdsa_verify(EC_KEY *key, const char *data, size_t data_len, const char *sig, size_t sig_len)
{
  return ECDSA_verify(0, data, data_len, sig, sig_len, key) > 0;
}
*/

/*
CAMLprim value ocaml_validate_chain(value chain, value for_signing, value hostname, value cafile) {
    CAMLparam4(chain, for_signing, hostname, cafile);

    time_t current_time;
    STACK_OF(X509) *sk;
    sk = sk_X509_new_null();
    X509* top_cert = NULL;
    char *host;

    if(chain == Val_emptylist) CAMLreturn(Val_false);
    if(hostname == Val_none) host = NULL;
    else host = String_val(Some_val(hostname));

    do {
      value head = Field(chain, 0);
      size_t len = caml_string_length(head);
      X509* x509;
      unsigned char *cert = (unsigned char*)String_val(head);

//      printf("ADDING CERT[%d]\n", (int)len);
      if(!top_cert) top_cert = x509; else sk_X509_push(sk, x509);
      chain = Field(chain, 1);
    }
    while(chain != Val_emptylist);

    X509_STORE_CTX *ctx = NULL;
    X509_STORE *store = NULL;
    X509_VERIFY_PARAM *param = NULL;

    current_time = time(NULL);
    store = X509_STORE_new();
    ctx = X509_STORE_CTX_new();
    param = X509_VERIFY_PARAM_new();
    if(!ctx || !store || !param) CAMLreturn(Val_false);

    // Validation parameters
    X509_VERIFY_PARAM_set_flags(param, X509_V_FLAG_USE_CHECK_TIME | X509_V_FLAG_CRL_CHECK_ALL);
    X509_VERIFY_PARAM_set_time(param, current_time);
    X509_VERIFY_PARAM_set1_host(param, host, 0);
    X509_STORE_set1_param(store, param);

    X509_STORE_CTX_init(ctx, store, top_cert, sk);

    int r = X509_verify_cert(ctx);
//    printf("X509_verify_cert() == %d [%s]\n", r, X509_verify_cert_error_string(ctx->error));

    X509_STORE_free(store);
    X509_STORE_CTX_free(ctx);
    sk_X509_free(sk);
    X509_VERIFY_PARAM_free(param);

    CAMLreturn(r==1 ? Val_true : Val_false);
}

CAMLprim value ocaml_load_chain(value pem) {
  CAMLparam1(pem);

  char *pemfile = (char*)String_val(pem);
  BIO *bio = BIO_new_file(pemfile, "r");
  if(!bio) CAMLreturn(Val_none);

  int c = 0;
  unsigned long n = 0;
  X509 *x509, *first = NULL;

  CAMLlocal2(mlc, mlret);
  mlret = Val_emptylist;

  ERR_clear_error();

  // Try to read all x509 structs in the file
  do {
    x509 = PEM_read_bio_X509_AUX(bio, NULL, NULL, NULL);

    if(!c) first = x509;

    if(!x509)
    {
      n = ERR_peek_last_error();
      if(!c ||
	 !(ERR_GET_LIB(n) == ERR_LIB_PEM
	  && ERR_GET_REASON(n) == PEM_R_NO_START_LINE))
	CAMLreturn(Val_none);
      else break;
    }

    int len;
    unsigned char *buf = NULL;
    len = i2d_X509(x509, &buf);
    if (len < 0) CAMLreturn(Val_none); // Yes there is a leak there

    CAMLlocal1(der_cert);
    der_cert = caml_alloc_string(len);
    memcpy(String_val(der_cert), buf, len);

    mlc = caml_alloc(2, 0);
    Store_field(mlc, 0, der_cert);
    Store_field(mlc, 1, mlret);
    mlret = mlc;
  }
  while(++c);

  CAMLreturn(Val_some(mlret));
}

CAMLprim value ocaml_load_key(value pem) {
  CAMLparam1(pem);

  char *pemfile = (char*)String_val(pem);
  BIO *bio = BIO_new_file(pemfile, "r");
  if(!bio) CAMLreturn(Val_none);


  if(!sk) CAMLreturn(Val_none);
  CAMLlocal4(mlkey, mlrsa, mldsa, mlec);

  switch(EVP_PKEY_base_id(sk))
  {
    case EVP_PKEY_RSA:
      mlrsa = caml_alloc_custom(&evp_rsa_ops, sizeof(RSA*), 0, 1);
      RSA* rsa = EVP_PKEY_get1_RSA(sk);
      if(!rsa) CAMLreturn(Val_none);
      RSA_val(mlrsa) = rsa;
      mlkey = caml_alloc(1, 0); // CertRSA
      Store_field(mlkey, 0, mlrsa);
      break;

    case EVP_PKEY_DSA:
      mldsa = caml_alloc_custom(&evp_dsa_ops, sizeof(DSA*), 0, 1);
      DSA* dsa = EVP_PKEY_get1_DSA(sk);
      if (!dsa) CAMLreturn(Val_none);
      DSA_val(mldsa) = dsa;
      mlkey = caml_alloc(1, 1); // CertDSA
      Store_field(mlkey, 0, mldsa);
      break;

    case EVP_PKEY_EC:
      mlec = caml_alloc_custom(&key_ops, sizeof(EC_KEY*), 0, 1);
      EC_KEY* eck = EVP_PKEY_get1_EC_KEY(sk);
      if(!eck) CAMLreturn(Val_none);
      EC_KEY_val(mlec) = eck;
      mlkey = caml_alloc(1, 2); // CertECDSA
      Store_field(mlkey, 0, mlec);
      break;

    default:
      CAMLreturn(Val_none);
  }

  CAMLreturn(Val_some(mlkey));
}
*/

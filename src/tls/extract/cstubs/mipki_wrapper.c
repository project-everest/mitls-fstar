#include <kremlib.h>
#include <mipki.h>
#include <mitlsffi.h>
#include <PKI.h>
#include <TLSConstants.h>

#define DEBUG 0

static size_t list_sa_len(Prims_list__TLSConstants_signatureScheme *l)
{
  if (l->tag == Prims_Cons)
  {
    return 1 + list_sa_len(l->tl);
  }
  return 0;
}

static size_t list_bytes_len(Prims_list__FStar_Bytes_bytes* l)
{
  if (l->tag == Prims_Cons)
  {
    return 1 + list_bytes_len(l->tl);
  }
  return 0;
}

static TLSConstants_signatureScheme_tags tls_of_pki(mitls_signature_scheme sa)
{
  switch(sa)
  {
    //  rsa_pkcs1_sha1(0x0201),
    case 0x0201: return TLSConstants_RSA_PKCS1_SHA1;
    //  rsa_pkcs1_sha256(0x0401),
    case 0x0401: return TLSConstants_RSA_PKCS1_SHA256;
    //  rsa_pkcs1_sha384(0x0501),
    case 0x0501: return TLSConstants_RSA_PKCS1_SHA384;
    //  rsa_pkcs1_sha512(0x0601),
    case 0x0601: return TLSConstants_RSA_PKCS1_SHA512;
    //  rsa_pss_sha256(0x0804),
    case 0x0804: return TLSConstants_RSA_PSS_SHA256;
    //  rsa_pss_sha384(0x0805),
    case 0x0805: return TLSConstants_RSA_PSS_SHA384;
    //  rsa_pss_sha512(0x0806),
    case 0x0806: return TLSConstants_RSA_PSS_SHA512;
    //  ecdsa_sha1(0x0203),
    case 0x0203: return TLSConstants_ECDSA_SHA1;
    //  ecdsa_secp256r1_sha256(0x0403),
    case 0x0403: return TLSConstants_ECDSA_SECP256R1_SHA256;
    //  ecdsa_secp384r1_sha384(0x0503),
    case 0x0503: return TLSConstants_ECDSA_SECP384R1_SHA384;
    //  ecdsa_secp521r1_sha512(0x0603),
    case 0x0603: return TLSConstants_ECDSA_SECP521R1_SHA512;
    //  ed25519(0x0807),
    //  ed448(0x0808),
    default:
      KRML_HOST_PRINTF("tls_of_pki: unsupported (%04x)\n", sa);
      KRML_EXIT;
  }
}

static mitls_signature_scheme pki_of_tls(TLSConstants_signatureScheme_tags sa)
{
  switch(sa)
  {
    //  rsa_pkcs1_sha1(0x0201),
    case TLSConstants_RSA_PKCS1_SHA1: return 0x0201;
    //  rsa_pkcs1_sha256(0x0401),
    case TLSConstants_RSA_PKCS1_SHA256: return 0x0401;
    //  rsa_pkcs1_sha384(0x0501),
    case TLSConstants_RSA_PKCS1_SHA384: return 0x0501;
    //  rsa_pkcs1_sha512(0x0601),
    case TLSConstants_RSA_PKCS1_SHA512: return 0x0601;
    //  rsa_pss_sha256(0x0804),
    case TLSConstants_RSA_PSS_SHA256: return 0x0804;
    //  rsa_pss_sha384(0x0805),
    case TLSConstants_RSA_PSS_SHA384: return 0x0805;
    //  rsa_pss_sha512(0x0806),
    case TLSConstants_RSA_PSS_SHA512: return 0x0806;
    //  ecdsa_sha1(0x0203),
    case TLSConstants_ECDSA_SHA1: return 0x0203;
    //  ecdsa_secp256r1_sha256(0x0403),
    case TLSConstants_ECDSA_SECP256R1_SHA256: return 0x0403;
    //  ecdsa_secp384r1_sha384(0x0503),
    case TLSConstants_ECDSA_SECP384R1_SHA384: return 0x0503;
    //  ecdsa_secp521r1_sha512(0x0603),
    case TLSConstants_ECDSA_SECP521R1_SHA512: return 0x0603;
    //  ed25519(0x0807), ed448(0x0808),
    default:
      KRML_HOST_PRINTF("pki_of_tls: unsupported (%d)\n", sa);
      KRML_EXIT;
  }
}

FStar_Pervasives_Native_option__K___uint64_t_TLSConstants_signatureScheme
PKI_select(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st,
  FStar_Bytes_bytes sni, Prims_list__TLSConstants_signatureScheme *sal)
{
  mitls_signature_scheme sel;
  mipki_state *pki = (mipki_state*)cbs;

  #if DEBUG
    KRML_HOST_PRINTF("PKI| SELECT callback <%08x>\n", cbs);
  #endif

  size_t sigalgs_len = list_sa_len(sal);
  mitls_signature_scheme *sigalgs = alloca(sigalgs_len*sizeof(mitls_signature_scheme));
  Prims_list__TLSConstants_signatureScheme *cur = sal;

  for(size_t i = 0; i < sigalgs_len; i++)
  {
    sigalgs[i] = pki_of_tls(cur->hd.tag);
    cur = cur->tl;
  }

  FStar_Pervasives_Native_option__K___uint64_t_TLSConstants_signatureScheme res;
  mipki_chain chain = mipki_select_certificate(pki, sni.data, sni.length, sigalgs, sigalgs_len, &sel);

  #if DEBUG
    KRML_HOST_PRINTF("PKI| Selected chain <%08x>, sigalg = %04x\n", chain, sel);
  #endif

  if(chain == NULL)
  {
    res.tag = FStar_Pervasives_Native_None;
  }
  else
  {
    K___uint64_t_TLSConstants_signatureScheme sig;

    // silence a GCC warning about sig.snd._0.length possibly uninitialized
    memset(&sig, 0, sizeof(sig));

    res.tag = FStar_Pervasives_Native_Some;
    sig.fst = (uint64_t)chain;
    sig.snd.tag = tls_of_pki(sel);
    res.v = sig;
  }
  return res;
}

static void* append(void* chain, size_t len, char **buf)
{
  #if DEBUG
    printf("PKI| FORMAT::append adding %d bytes element\n", len);
  #endif

  *buf = KRML_HOST_MALLOC(len);

  Prims_list__FStar_Bytes_bytes* cur = (Prims_list__FStar_Bytes_bytes*) chain;
  Prims_list__FStar_Bytes_bytes* new = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));

  new->tag = Prims_Nil;
  cur->tag = Prims_Cons;

  cur->hd = (FStar_Bytes_bytes){.length = len, .data = *buf};
  cur->tl = new;
  return (void*)new;
}

Prims_list__FStar_Bytes_bytes* PKI_format(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st, uint64_t cert)
{
  mipki_state *pki = (mipki_state*)cbs;
  mipki_chain chain = (mipki_chain)cert;

  #if DEBUG
    KRML_HOST_PRINTF("PKI| FORMAT <%08x> CHAIN <%08x>\n", pki, chain);
  #endif

  Prims_list__FStar_Bytes_bytes *res = KRML_HOST_MALLOC(sizeof(Prims_list__FStar_Bytes_bytes));
  mipki_format_alloc(pki, chain, (void*)res, append);
  return res;
}

FStar_Pervasives_Native_option__FStar_Bytes_bytes PKI_sign(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st,
  uint64_t cert, TLSConstants_signatureScheme sa, FStar_Bytes_bytes tbs)
{
  mipki_state *pki = (mipki_state*)cbs;
  mipki_chain chain = (mipki_chain)cert;

  #if DEBUG
    KRML_HOST_PRINTF("PKI| SIGN <%08x> CHAIN <%08x>\n", pki, chain);
  #endif

  char* sig = KRML_HOST_MALLOC(MAX_SIGNATURE_LEN);
  size_t slen = MAX_SIGNATURE_LEN;
  FStar_Pervasives_Native_option__FStar_Bytes_bytes res = {.tag = FStar_Pervasives_Native_None};
  mipki_signature sigalg = pki_of_tls(sa.tag);

  if(mipki_sign_verify(pki, chain, sigalg, tbs.data, tbs.length, sig, &slen, MIPKI_SIGN))
  {
    #if DEBUG
      KRML_HOST_PRINTF("PKI| Success: produced %d bytes of signature.\n", pki, slen);
    #endif
    res.tag = FStar_Pervasives_Native_Some;
    res.v = (FStar_Bytes_bytes){.length = slen, .data = sig};
  }

  return res;
}

bool PKI_verify(FStar_Dyn_dyn cbs, FStar_Dyn_dyn st,
  Prims_list__FStar_Bytes_bytes *certs, TLSConstants_signatureScheme sa,
  FStar_Bytes_bytes tbs, FStar_Bytes_bytes sig)
{
  mipki_state *pki = (mipki_state*)cbs;
  size_t chain_len = list_bytes_len(certs);

  #if DEBUG
    KRML_HOST_PRINTF("PKI| VERIFY <%08x> (contains %d certificates)\n", pki, chain_len);
  #endif

  mipki_signature sigalg = pki_of_tls(sa.tag);
  size_t *lens = alloca(chain_len*sizeof(size_t));
  const char **ders = alloca(chain_len*sizeof(const char*));
  Prims_list__FStar_Bytes_bytes *cur = certs;

  for(size_t i = 0; i < chain_len; i++)
  {
    lens[i] = cur->hd.length;
    ders[i] = cur->hd.data;
    cur = cur->tl;
  }

  mipki_chain chain = mipki_parse_list(pki, ders, lens, chain_len);
  size_t slen = sig.length;

  if(chain == NULL)
  {
    #if DEBUG
      KRML_HOST_PRINTF("PKI| Failed to parse certificate chain.\n");
    #endif
    return false;
  }

  // We don't validate hostname, but could with the callback state
  if(!mipki_validate_chain(pki, chain, ""))
  {
    #if DEBUG
      KRML_HOST_PRINTF("PKI| WARNING: chain validation failed, ignoring.\n");
    #endif
    // return 0;
  }

  #if DEBUG
    KRML_HOST_PRINTF("PKI| Chain parsed, verifying %d bytes signature with %04x.\n", slen, sigalg);
  #endif

  char* sigp = (char *)sig.data;
  int r = mipki_sign_verify(pki, chain, sigalg, tbs.data, tbs.length,
    sigp, &slen, MIPKI_VERIFY);

  mipki_free_chain(pki, chain);
  return (r == 1);
}

static uint32_t config_len(Prims_list__K___Prims_string_Prims_string_bool *l)
{
  if (l->tag == Prims_Cons)
  {
    return 1 + config_len(l->tl);
  }
  return 0;
}

FStar_Dyn_dyn PKI_init(Prims_string cafile, Prims_list__K___Prims_string_Prims_string_bool *certs)
{
  uint32_t len = config_len(certs);
  Prims_list__K___Prims_string_Prims_string_bool* cur = certs;
  mipki_config_entry *pki_config = alloca(len*sizeof(mipki_config_entry));
  int err;

  for(int i = 0; i<len; i++)
  {
    K___Prims_string_Prims_string_bool cfg = cur->hd;

    #if DEBUG
      KRML_HOST_PRINTF("PKI| Adding cert <%s> with key <%s>\n", cfg.fst, cfg.snd);
    #endif

    pki_config[i] = (mipki_config_entry){
      .cert_file = cfg.fst,
      .key_file = cfg.snd,
      .is_universal = cfg.thd
    };
    cur = cur->tl;
  };

  #if DEBUG
    KRML_HOST_PRINTF("PKI| INIT\n");
  #endif

  mipki_state *pki = mipki_init(pki_config, len, NULL, &err);
  if(pki == NULL) {
     KRML_HOST_PRINTF("mipki_init failed at %s:%d. Do all files in the config exist?\n", __FILE__, __LINE__);
     KRML_HOST_EXIT(253);
  }

  #if DEBUG
    KRML_HOST_PRINTF("PKI| Created <%08x>, set CAFILE <%s>\n", pki, cafile);
  #endif

  if(cafile[0] != '\0') mipki_add_root_file_or_path(pki, cafile);

  return pki;
}

TLSConstants_cert_cb PKI_tls_callbacks(FStar_Dyn_dyn x0)
{
  return (TLSConstants_cert_cb){
    .app_context = x0,
    .cert_select_ptr = NULL,
    .cert_select_cb = PKI_select,
    .cert_format_ptr = NULL,
    .cert_format_cb = PKI_format,
    .cert_sign_ptr = NULL,
    .cert_sign_cb = PKI_sign,
    .cert_verify_ptr = NULL,
    .cert_verify_cb = PKI_verify
  };
}

void PKI_free(FStar_Dyn_dyn pki)
{
  mipki_free((mipki_state*)pki);
}

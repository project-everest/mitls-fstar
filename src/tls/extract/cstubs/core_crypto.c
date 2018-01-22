#include "CoreCrypto.h"
#include "Crypto_HKDF_Crypto_HMAC.h"

#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

#include <openssl/conf.h>
#include <openssl/err.h>
#include <openssl/bn.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/dsa.h>
#include <openssl/dh.h>
#include <openssl/pem.h>
#include <openssl/ec.h>
#include <openssl/objects.h>
#include <openssl/obj_mac.h>

#define FAIL_IF(test, msg)                                                     \
  do {                                                                         \
    if (test)                                                                  \
      continue;                                                                \
    fprintf(stderr, "%s %s\n", __FUNCTION__, msg);                             \
    exit(253);                                                                 \
  } while (0)

#define TODO(t)                                                                \
  {                                                                            \
    t _x = {0};                                                                \
    fprintf(stderr, "%s TODO\n", __FUNCTION__);                                \
    exit(252);                                                                 \
    return _x;                                                                 \
  }

FStar_Bytes_bytes CoreCrypto_dh_agreement(CoreCrypto_dh_key x0,
                                          FStar_Bytes_bytes x1) {
  DH *dh = DH_new();
  FAIL_IF(dh == NULL, "OpenSSL allocation failure dh");
  BIGNUM *p = BN_bin2bn((uint8_t *) x0.dh_params.dh_p.data, x0.dh_params.dh_p.length, NULL);
  BIGNUM *g = BN_bin2bn((uint8_t *) x0.dh_params.dh_g.data, x0.dh_params.dh_g.length, NULL);
  BIGNUM *pub = BN_bin2bn((uint8_t *) x0.dh_public.data, x0.dh_public.length, NULL);
  FAIL_IF(p == NULL || g == NULL || pub == NULL,
          "OpenSSL allocation failure p/q/pub");
  BIGNUM *prv = NULL;
  if (x0.dh_private.tag == FStar_Pervasives_Native_Some) {
    prv = BN_bin2bn((uint8_t *) x0.dh_private.val.case_Some.v.data,
                    x0.dh_private.val.case_Some.v.length, NULL);
    FAIL_IF(prv == NULL, "OpenSSL allocation failure prv");
  }
  DH_set0_pqg(dh, p, NULL, g);
  DH_set0_key(dh, pub, prv);

  uint32_t len = DH_size(dh);
  char *out = malloc(len);

  FAIL_IF(DH_compute_key((uint8_t *) out, pub, dh) < 0, "OpenSSL failure DH_compute_key");

  if (prv != NULL)
    BN_free(prv);
  BN_free(pub);
  BN_free(g);
  BN_free(p);
  DH_free(dh);

  FStar_Bytes_bytes ret = {
    .length = len,
    .data = out
  };
  return ret;
}

static inline
FStar_Bytes_bytes bytes_of_bn(const BIGNUM *bn) {
  size_t len = BN_num_bytes(bn);
  char *data = malloc(len);
  BN_bn2bin(bn, (uint8_t *) data);
  FStar_Bytes_bytes ret = {
    .length = len,
    .data = data
  };
  return ret;
}

CoreCrypto_dh_key CoreCrypto_dh_gen_key(CoreCrypto_dh_params x0) {
  DH *dh = DH_new();
  FAIL_IF(dh == NULL, "OpenSSL allocation failure dh");
  BIGNUM *p = BN_bin2bn((uint8_t *) x0.dh_p.data, x0.dh_p.length, NULL);
  BIGNUM *g = BN_bin2bn((uint8_t *) x0.dh_g.data, x0.dh_g.length, NULL);
  FAIL_IF(p == NULL || g == NULL, "OpenSSL allocation failure p/g");
  DH_set0_pqg(dh, p, NULL, g);
  FAIL_IF(DH_generate_key(dh) == 0, "OpenSSL failure DH_generate_key");

  const BIGNUM *pub, *prv;
  DH_get0_key(dh, &pub, &prv);

  size_t p_byte_len = BN_num_bytes(pub);

  CoreCrypto_dh_key ret = {
    .dh_params = x0,
    .dh_public = bytes_of_bn(pub),
    .dh_private = {
      .tag = FStar_Pervasives_Native_Some,
      .val = { .case_Some = { .v = bytes_of_bn(prv) } }
    }
  };
  return ret;
    
}

FStar_Bytes_bytes CoreCrypto_ecdh_agreement(CoreCrypto_ec_key x0,
                                            CoreCrypto_ec_point x1) {
  TODO(FStar_Bytes_bytes);
}

CoreCrypto_ec_key CoreCrypto_ec_gen_key(CoreCrypto_ec_params x0) {
  TODO(CoreCrypto_ec_key);
}

bool CoreCrypto_ec_is_on_curve(CoreCrypto_ec_params x0,
                               CoreCrypto_ec_point x1) {
  TODO(bool);
}

FStar_Pervasives_Native_option__CoreCrypto_key
CoreCrypto_get_key_from_cert(FStar_Bytes_bytes x0) {
  // unused
  TODO(FStar_Pervasives_Native_option__CoreCrypto_key);
}

static inline
Crypto_HMAC_alg hacl_alg_of_corecrypto_alg(CoreCrypto_hash_alg h) {
  switch (h) {
  case CoreCrypto_SHA256:
    return Crypto_HMAC_SHA256;
  case CoreCrypto_SHA384:
    return Crypto_HMAC_SHA384;
  case CoreCrypto_SHA512:
    return Crypto_HMAC_SHA512;
  default:
    return -1;
  }
}

FStar_Bytes_bytes CoreCrypto_hash(CoreCrypto_hash_alg x0,
                                  FStar_Bytes_bytes x1) {
  Crypto_HMAC_alg a = hacl_alg_of_corecrypto_alg(x0);
  FAIL_IF(a == -1,
          "CoreCrypto_hash implemented using HACL*, unsupported algorithm");
  uint32_t len = Crypto_HMAC_hash_size(a);
  char *out = malloc(len);
  Crypto_HMAC_agile_hash(a, (uint8_t *)out, (uint8_t *)x1.data, x1.length);

  FStar_Bytes_bytes ret = {.length = len, .data = out};
  return ret;
}

FStar_Pervasives_Native_option__Prims_list__FStar_Bytes_bytes
CoreCrypto_load_chain(Prims_string x0) {
  // unused
  TODO(FStar_Pervasives_Native_option__Prims_list__FStar_Bytes_bytes);
}

#ifdef __WINDOWS__
FStar_Bytes_bytes CoreCrypto_random(Prims_nat x0) {
  char *data = malloc(x0);

  HCRYPTPROV ctxt;
  if (!(CryptAcquireContext(&ctxt, NULL, NULL, PROV_RSA_FULL,
                            CRYPT_VERIFYCONTEXT))) {
    DWORD error = GetLastError();
    fprintf(e, "Cannot acquire crypto context: 0x%lx\n", error);
    exit(255);
  }
  if (!(CryptGenRandom(ctxt, x0, data))) {
    fprintf(stderr, "Cannot read random bytes\n");
    exit(255);
  }
  CryptReleaseContext(ctxt, 0);

  FStar_Bytes_bytes ret = {.length = x0, .data = data};
  return ret;
}
#else
FStar_Bytes_bytes CoreCrypto_random(Prims_nat x0) {
  char *data = malloc(x0);

  int fd = open("/dev/urandom", O_RDONLY);
  if (fd == -1) {
    fprintf(stderr, "Cannot open /dev/urandom\n");
    exit(255);
  }
  uint64_t res = read(fd, data, x0);
  if (res != x0) {
    fprintf(stderr,
            "Error on reading, expected %" PRIi32 " bytes, got %" PRIu64
            " bytes\n",
            x0, res);
    exit(255);
  }
  close(fd);

  FStar_Bytes_bytes ret = {.length = x0, .data = data};
  return ret;
}
#endif

CoreCrypto_rsa_key CoreCrypto_rsa_gen_key(Prims_int x0) {
  // unused
  TODO(CoreCrypto_rsa_key);
}

bool CoreCrypto_validate_chain(Prims_list__FStar_Bytes_bytes *x0, bool x1,
                               FStar_Pervasives_Native_option__Prims_string x2,
                               Prims_string x3) {
  // unused
  TODO(bool);
}

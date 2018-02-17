#include "CoreCrypto.h"
#include "kremlib.h"

#if defined(_MSC_VER) || defined(__MINGW32__)
#define IS_WINDOWS 1
  #ifdef _KERNEL_MODE
    #include <nt.h>
    #include <ntrtl.h>
    #include <bcrypt.h>
  #else
    #include <windows.h>
    #include <wincrypt.h>
  #endif
#else
#define IS_WINDOWS 0
#include <unistd.h>
#endif
#include <fcntl.h>

#define FAIL_IF(test, msg)                                                     \
  do {                                                                         \
    if (!(test))                                                               \
      continue;                                                                \
    KRML_HOST_PRINTF("%s %s\n", __FUNCTION__, msg);                            \
    KRML_HOST_EXIT(253);                                                       \
  } while (0)

#define TODO(t)                                                                \
  {                                                                            \
    t _x = {0};                                                                \
    KRML_HOST_PRINTF("%s TODO\n", __FUNCTION__);                               \
    KRML_HOST_EXIT(252);                                                       \
    return _x;                                                                 \
  }

#ifndef NO_OPENSSL

#include <openssl/bn.h>
#include <openssl/conf.h>
#include <openssl/dh.h>
#include <openssl/dsa.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/obj_mac.h>
#include <openssl/objects.h>
#include <openssl/pem.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>

FStar_Bytes_bytes CoreCrypto_dh_agreement(CoreCrypto_dh_key x0,
                                          FStar_Bytes_bytes x1) {
  DH *dh = DH_new();
  FAIL_IF(dh == NULL, "OpenSSL allocation failure dh");

  BIGNUM *p = BN_bin2bn((uint8_t *)x0.dh_params.dh_p.data,
                        x0.dh_params.dh_p.length, NULL);
  BIGNUM *g = BN_bin2bn((uint8_t *)x0.dh_params.dh_g.data,
                        x0.dh_params.dh_g.length, NULL);
  BIGNUM *pub =
      BN_bin2bn((uint8_t *)x0.dh_public.data, x0.dh_public.length, NULL);
  BIGNUM *opub = BN_bin2bn((uint8_t *)x1.data, x1.length, NULL);
  FAIL_IF(p == NULL || g == NULL || pub == NULL || opub == NULL,
          "OpenSSL allocation failure p/g/pub");
  BIGNUM *prv = NULL;
  if (x0.dh_private.tag == FStar_Pervasives_Native_Some) {
    prv = BN_bin2bn((uint8_t *)x0.dh_private.v.data, x0.dh_private.v.length,
                    NULL);
    FAIL_IF(prv == NULL, "OpenSSL allocation failure prv");
  }
  DH_set0_pqg(dh, p, NULL, g);
  DH_set0_key(dh, pub, prv);

  uint32_t len = DH_size(dh);
  char *out = KRML_HOST_MALLOC(len);

  FAIL_IF(DH_compute_key((uint8_t *)out, opub, dh) < 0,
          "OpenSSL failure DH_compute_key");

  // Memory management of p, g, pub, and prv has been transfered to dh
  DH_free(dh);
  BN_free(opub);

  FStar_Bytes_bytes ret = {.length = len, .data = out};
  return ret;
}

static inline FStar_Bytes_bytes bytes_of_bn(const BIGNUM *bn) {
  size_t len = BN_num_bytes(bn);
  char *data = KRML_HOST_MALLOC(len);
  BN_bn2bin(bn, (uint8_t *)data);
  FStar_Bytes_bytes ret = {.length = len, .data = data};
  return ret;
}

CoreCrypto_dh_key CoreCrypto_dh_gen_key(CoreCrypto_dh_params x0) {
  DH *dh = DH_new();
  FAIL_IF(dh == NULL, "OpenSSL allocation failure dh");
  BIGNUM *p = BN_bin2bn((uint8_t *)x0.dh_p.data, x0.dh_p.length, NULL);
  BIGNUM *g = BN_bin2bn((uint8_t *)x0.dh_g.data, x0.dh_g.length, NULL);
  FAIL_IF(p == NULL || g == NULL, "OpenSSL allocation failure p/g");
  DH_set0_pqg(dh, p, NULL, g);
  FAIL_IF(DH_generate_key(dh) == 0, "OpenSSL failure DH_generate_key");

  const BIGNUM *pub, *prv;
  DH_get0_key(dh, &pub, &prv);

  CoreCrypto_dh_key ret = {.dh_params = x0,
                           .dh_public = bytes_of_bn(pub),
                           .dh_private = {.tag = FStar_Pervasives_Native_Some,
                                          .v = bytes_of_bn(prv)}};

  DH_free(dh);

  return ret;
}

EC_KEY *key_of_core_crypto_curve(CoreCrypto_ec_curve c) {
  EC_KEY *k = NULL;
  switch (c) {
  case CoreCrypto_ECC_P256:
    k = EC_KEY_new_by_curve_name(OBJ_txt2nid(SN_X9_62_prime256v1));
    break;
  case CoreCrypto_ECC_P384:
    k = EC_KEY_new_by_curve_name(OBJ_txt2nid(SN_secp384r1));
    break;
  case CoreCrypto_ECC_P521:
    k = EC_KEY_new_by_curve_name(OBJ_txt2nid(SN_secp521r1));
    break;
  case CoreCrypto_ECC_X25519:
    k = EC_KEY_new_by_curve_name(OBJ_txt2nid(SN_X25519));
    break;
  default:
    FAIL_IF(true, "Unsupported curve");
  }
  return k;
}

uint32_t size_of_curve(CoreCrypto_ec_curve x) {
  switch (x) {
  case CoreCrypto_ECC_P256:
    return 32;
  case CoreCrypto_ECC_P384:
    return 48;
  case CoreCrypto_ECC_P521:
    return 66;
  case CoreCrypto_ECC_X25519:
    return 32;
  case CoreCrypto_ECC_X448:
    return 56;
  }
  exit(255);
}

FStar_Bytes_bytes CoreCrypto_ecdh_agreement(CoreCrypto_ec_key x0,
                                            CoreCrypto_ec_point x1) {
  EC_KEY *k = key_of_core_crypto_curve(x0.ec_params.curve);
  EC_GROUP *g = EC_GROUP_dup(EC_KEY_get0_group(k));

  if (x0.ec_params.point_compression)
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_COMPRESSED);
  else
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_UNCOMPRESSED);

  BIGNUM *px =
      BN_bin2bn((uint8_t *)x0.ec_point.ecx.data, x0.ec_point.ecx.length, NULL);
  BIGNUM *py =
      BN_bin2bn((uint8_t *)x0.ec_point.ecy.data, x0.ec_point.ecy.length, NULL);
  EC_KEY_set_public_key_affine_coordinates(k, px, py);

  BIGNUM *pr = NULL;
  if (x0.ec_priv.tag == FStar_Pervasives_Native_Some) {
    pr = BN_bin2bn((uint8_t *)x0.ec_priv.v.data, x0.ec_priv.v.length, NULL);
    EC_KEY_set_private_key(k, pr);
  }

  size_t field_size = EC_GROUP_get_degree(g);
  size_t len = (field_size + 7) / 8;
  char *out = KRML_HOST_MALLOC(len);
  memset(out, 0, len);

  EC_POINT *pp = EC_POINT_new(g);
  BIGNUM *ppx = BN_bin2bn((uint8_t *)x1.ecx.data, x1.ecx.length, NULL);
  BIGNUM *ppy = BN_bin2bn((uint8_t *)x1.ecy.data, x1.ecy.length, NULL);
  EC_POINT_set_affine_coordinates_GFp(g, pp, ppx, ppy, NULL);

  size_t olen = ECDH_compute_key((uint8_t *)out, len, pp, k, NULL);

  BN_free(ppy);
  BN_free(ppx);
  EC_POINT_free(pp);
  if (pr != NULL)
    BN_free(pr);
  BN_free(py);
  BN_free(px);
  EC_GROUP_free(g);
  EC_KEY_free(k);

  FStar_Bytes_bytes ret = {.length = olen, .data = out};
  return ret;
}

CoreCrypto_ec_key CoreCrypto_ec_gen_key(CoreCrypto_ec_params x0) {
  EC_KEY *k = key_of_core_crypto_curve(x0.curve);
  FAIL_IF(EC_KEY_generate_key(k) == 0, "EC_KEY_generate_key failed");

  EC_GROUP *g = EC_GROUP_dup(EC_KEY_get0_group(k));
  if (x0.point_compression)
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_COMPRESSED);
  else
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_UNCOMPRESSED);

  const EC_POINT *p = EC_KEY_get0_public_key(k);
  BIGNUM *x = BN_new(), *y = BN_new();
  EC_POINT_get_affine_coordinates_GFp(g, p, x, y, NULL);
  const BIGNUM *pr = EC_KEY_get0_private_key(k);

  uint32_t n = size_of_curve(x0.curve);
  CoreCrypto_ec_key ret = {
      .ec_params = x0,
      .ec_point =
          {.ecx = FStar_Bytes_append(FStar_Bytes_create(n - BN_num_bytes(x), 0),
                                     bytes_of_bn(x)),
           .ecy = FStar_Bytes_append(FStar_Bytes_create(n - BN_num_bytes(y), 0),
                                     bytes_of_bn(y))},
      .ec_priv = {.tag = FStar_Pervasives_Native_Some, .v = bytes_of_bn(pr)}};

  BN_free(y);
  BN_free(x);
  EC_GROUP_free(g);
  EC_KEY_free(k);

  return ret;
}

static inline const EVP_MD *get_md(CoreCrypto_hash_alg h){
  switch (h) {
  case CoreCrypto_MD5:
    return EVP_md5();
  case CoreCrypto_SHA1:
    return EVP_sha1();
  case CoreCrypto_SHA224:
    return EVP_sha224();
  case CoreCrypto_SHA256:
    return EVP_sha256();
  case CoreCrypto_SHA384:
    return EVP_sha384();
  case CoreCrypto_SHA512:
    return EVP_sha512();
  default:
    return EVP_md_null();
  }
}

FStar_Bytes_bytes CoreCrypto_hash(CoreCrypto_hash_alg x0, FStar_Bytes_bytes x1) {
  const EVP_MD *md = get_md(x0);
  EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
  EVP_DigestInit_ex(mdctx, md, NULL);
  size_t len = EVP_MD_CTX_size(mdctx);

  unsigned char *out = KRML_HOST_MALLOC(len);
  FAIL_IF(out == NULL, "Allocation failure");
  EVP_DigestUpdate(mdctx, x1.data, x1.length);
  EVP_DigestFinal_ex(mdctx, out, NULL);

  EVP_MD_CTX_free(mdctx);
  FStar_Bytes_bytes ret = {.length = len, .data = (const char*)out};
  return ret;
}

FStar_Bytes_bytes CoreCrypto_hmac(CoreCrypto_hash_alg x0, FStar_Bytes_bytes x1,
                                  FStar_Bytes_bytes x2) {
  const EVP_MD *md = get_md(x0);
  EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
  EVP_DigestInit_ex(mdctx, md, NULL);
  size_t len = EVP_MD_CTX_size(mdctx);

  unsigned char *out = KRML_HOST_MALLOC(len);
  FAIL_IF(out == NULL, "Allocation failure");
  out = HMAC(md, x1.data, x1.length, (const unsigned char*)x2.data, x2.length, out, NULL);
  FAIL_IF(out == NULL, "HMAC computation");

  FStar_Bytes_bytes ret = {.length = len, .data = (const char*)out};
  return ret;
}

// REMARK: used only in tests
CoreCrypto_rsa_key CoreCrypto_rsa_gen_key(Prims_int size) {
  RSA *rsa = RSA_new();
  BIGNUM *e = BN_new();
  FAIL_IF(e == NULL || rsa == NULL, "OpenSSL allocation failure");

  BN_hex2bn(&e, "010001"); // 65537
  if (RSA_generate_key_ex(rsa, size, e, NULL) != 1) {
    FAIL_IF(true, "Key generation failure");
  }

  const BIGNUM *b_n, *b_e, *b_d;
  RSA_get0_key(rsa, &b_n, &b_e, &b_d);

  CoreCrypto_rsa_key ret = {.rsa_mod = bytes_of_bn(b_n),
                            .rsa_pub_exp = bytes_of_bn(b_e),
                            .rsa_prv_exp = {.tag = FStar_Pervasives_Native_Some,
                                            .v = bytes_of_bn(b_d)}};

  RSA_free(rsa);
  BN_free(e);

  return ret;
}

FStar_Bytes_bytes CoreCrypto_rsa_encrypt(CoreCrypto_rsa_key key,
                                         CoreCrypto_rsa_padding padding,
                                         FStar_Bytes_bytes data) {
  BIGNUM *mod =
      BN_bin2bn((uint8_t *)key.rsa_mod.data, key.rsa_mod.length, NULL);
  BIGNUM *exp =
      BN_bin2bn((uint8_t *)key.rsa_pub_exp.data, key.rsa_pub_exp.length, NULL);
  RSA *rsa = RSA_new();
  FAIL_IF(mod == NULL || exp == NULL || rsa == NULL,
          "OpenSSL allocation failure");

  RSA_set0_key(rsa, mod, exp, NULL);

  size_t pdsz = 0;
  int openssl_padding = -1;
  switch (padding) {
  case CoreCrypto_Pad_none:
    pdsz = 0;
    openssl_padding = RSA_NO_PADDING;
    break;

  case CoreCrypto_Pad_PKCS1:
    pdsz = 11;
    openssl_padding = RSA_PKCS1_PADDING;
    break;

  default:
    abort();
  }

  size_t rsasz = RSA_size(rsa);
  FAIL_IF(data.length > rsasz - pdsz, "Cannot encrypt as much data");

  char *out = KRML_HOST_MALLOC(rsasz);
  FAIL_IF(out == NULL, "Allocation failure");

  if (RSA_public_encrypt(data.length, (uint8_t *)data.data, (uint8_t *)out, rsa,
                         openssl_padding) < 0) {
    unsigned long err = ERR_peek_last_error();
    char *err_string = ERR_error_string(err, NULL);
    FAIL_IF(true, err_string);
  }

  RSA_free(rsa);

  FStar_Bytes_bytes ret = {.length = rsasz, .data = out};
  return ret;
}

// REMARK: used only in tests
FStar_Pervasives_Native_option__FStar_Bytes_bytes
CoreCrypto_rsa_decrypt(CoreCrypto_rsa_key key, CoreCrypto_rsa_padding padding,
                       FStar_Bytes_bytes data) {
  BIGNUM *mod =
      BN_bin2bn((uint8_t *)key.rsa_mod.data, key.rsa_mod.length, NULL);
  BIGNUM *pub =
      BN_bin2bn((uint8_t *)key.rsa_pub_exp.data, key.rsa_pub_exp.length, NULL);
  BIGNUM *prv = NULL;
  if (key.rsa_prv_exp.tag == FStar_Pervasives_Native_Some) {
    prv = BN_bin2bn((uint8_t *)key.rsa_prv_exp.v.data, key.rsa_prv_exp.v.length,
                    NULL);
  } else {
    FAIL_IF(true, "Missing private exponent in RSA key");
  }
  RSA *rsa = RSA_new();
  FAIL_IF(mod == NULL || pub == NULL || prv == NULL || rsa == NULL,
          "OpenSSL allocation failure");

  RSA_set0_key(rsa, mod, pub, prv);

  int openssl_padding = -1;
  switch (padding) {
  case CoreCrypto_Pad_none:
    openssl_padding = RSA_NO_PADDING;
    break;

  case CoreCrypto_Pad_PKCS1:
    openssl_padding = RSA_PKCS1_PADDING;
    break;

  default:
    abort();
  }

  size_t rsasz = RSA_size(rsa);
  FAIL_IF(data.length != rsasz, "Incorrect ciphertext length");

  char *out = KRML_HOST_MALLOC(rsasz);
  FAIL_IF(out == NULL, "Allocation failure");

  int len;
  if ((len = RSA_private_decrypt(data.length, (uint8_t *)data.data,
                                 (uint8_t *)out, rsa, openssl_padding)) < 0) {
    unsigned long err = ERR_peek_last_error();
    char *err_string = ERR_error_string(err, NULL);
    FAIL_IF(true, err_string);
  }

  RSA_free(rsa);

  FStar_Pervasives_Native_option__FStar_Bytes_bytes ret = {
      .tag = FStar_Pervasives_Native_Some, .v = {.length = len, .data = out}};
  return ret;
}

bool CoreCrypto_ec_is_on_curve(CoreCrypto_ec_params x0,
                               CoreCrypto_ec_point x1) {

  EC_KEY *k = key_of_core_crypto_curve(x0.curve);
  const EC_GROUP *group = EC_KEY_get0_group(k);

  EC_POINT *point = EC_POINT_new(group);
  BIGNUM *ppx = BN_bin2bn((uint8_t *)x1.ecx.data, x1.ecx.length, NULL);
  BIGNUM *ppy = BN_bin2bn((uint8_t *)x1.ecy.data, x1.ecy.length, NULL);
  EC_POINT_set_affine_coordinates_GFp(group, point, ppx, ppy, NULL);

  bool ret = EC_POINT_is_on_curve(group, point, NULL);

  BN_free(ppy);
  BN_free(ppx);
  EC_POINT_free(point);
  EC_KEY_free(k);
  return ret;
}

#else // NO_OPENSSL

FStar_Bytes_bytes CoreCrypto_dh_agreement(CoreCrypto_dh_key x0,
                                          FStar_Bytes_bytes x1) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Bytes_bytes ret = {.length = 0, .data = 0};
  return ret;
}

FStar_Bytes_bytes CoreCrypto_rsa_encrypt(CoreCrypto_rsa_key key,
                                         CoreCrypto_rsa_padding padding,
                                         FStar_Bytes_bytes data) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Bytes_bytes ret = {.length = 0, .data = 0};
  return ret;
}

static inline FStar_Bytes_bytes bytes_of_bn(const void *bn) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Bytes_bytes ret = {.length = 0, .data = 0};
  return ret;
}

CoreCrypto_dh_key CoreCrypto_dh_gen_key(CoreCrypto_dh_params x0) {
  FAIL_IF(true, "No OpenSSL support.");
  CoreCrypto_dh_key ret = {.dh_params = x0,
                           .dh_public = 0,
                           .dh_private = {.tag = FStar_Pervasives_Native_Some,
                                          .v = {.length = 0, .data = 0}}};
  return ret;
}

CoreCrypto_ec_key CoreCrypto_ec_gen_key(CoreCrypto_ec_params x0) {
  FAIL_IF(true, "No OpenSSL support.");
  CoreCrypto_ec_key ret = {.ec_params = x0,
                           .ec_point = {.ecx = 0, .ecy = 0},
                           .ec_priv = {.tag = FStar_Pervasives_Native_Some,
                                       .v = {.length = 0, .data = 0}}};
  return ret;
}

FStar_Bytes_bytes CoreCrypto_ecdh_agreement(CoreCrypto_ec_key x0,
                                            CoreCrypto_ec_point x1) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Bytes_bytes ret = {.length = 0, .data = 0};
  return ret;
}

CoreCrypto_rsa_key CoreCrypto_rsa_gen_key(Prims_int size) {
  FAIL_IF(true, "No OpenSSL support.");
  CoreCrypto_rsa_key ret = {
      .rsa_mod = 0,
      .rsa_pub_exp = 0,
      .rsa_prv_exp = {.tag = FStar_Pervasives_Native_Some, .v = 0}};

  return ret;
}

// REMARK: used only in tests
FStar_Pervasives_Native_option__FStar_Bytes_bytes
CoreCrypto_rsa_decrypt(CoreCrypto_rsa_key key, CoreCrypto_rsa_padding padding,
                       FStar_Bytes_bytes data) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Pervasives_Native_option__FStar_Bytes_bytes ret = {
      .tag = FStar_Pervasives_Native_Some, .v = {.length = 0, .data = 0}};
  return ret;
}

FStar_Bytes_bytes CoreCrypto_hash(CoreCrypto_hash_alg x0,
                                  FStar_Bytes_bytes x1) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Bytes_bytes ret = {.length = 0, .data = 0};
  return ret;
}

FStar_Bytes_bytes CoreCrypto_hmac(CoreCrypto_hash_alg x0, FStar_Bytes_bytes x1,
                                  FStar_Bytes_bytes x2) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Bytes_bytes ret = {.length = 0, .data = 0};
  return ret;
}

bool CoreCrypto_ec_is_on_curve(CoreCrypto_ec_params x0,
                               CoreCrypto_ec_point x1) {

  FAIL_IF(true, "No OpenSSL support.");
  return false;
}

#endif // NO_OPENSSL

#if IS_WINDOWS
FStar_Bytes_bytes CoreCrypto_random(Prims_nat x0) {
#ifdef _KERNEL_MODE
  BCRYPT_ALG_HANDLE hAlg;
  NTSTATUS st;

  PUCHAR data = KRML_HOST_MALLOC(x0);

  // This is called at APC_LEVEL, so the USE_SYSTEM_PREFERRED_RNG option isn't supported.
  st = BCryptOpenAlgorithmProvider(&hAlg, BCRYPT_RNG_ALGORITHM, NULL, BCRYPT_PROV_DISPATCH);
  if (!NT_SUCCESS(st)) {
    KRML_HOST_EPRINTF("BCryptOpenAlgorithmProvider failed: 0x%x\n", st);
    KRML_HOST_EXIT(255);
  }
  st = BCryptGenRandom(hAlg, data, x0, 0);
  BCryptCloseAlgorithmProvider(hAlg, 0);
  if (!NT_SUCCESS(st)) {
    KRML_HOST_EPRINTF("Cannot read random bytes: 0x%x\n", st);
    KRML_HOST_EXIT(255);
  }
#else
  BYTE *data = KRML_HOST_MALLOC(x0);

  HCRYPTPROV ctxt;
  if (!(CryptAcquireContext(&ctxt, NULL, NULL, PROV_RSA_FULL,
                            CRYPT_VERIFYCONTEXT))) {
    DWORD error = GetLastError();
    KRML_HOST_EPRINTF("Cannot acquire crypto context: 0x%lx\n", error);
    KRML_HOST_EXIT(255);
  }
  if (!(CryptGenRandom(ctxt, x0, data))) {
    KRML_HOST_EPRINTF("Cannot read random bytes\n");
    KRML_HOST_EXIT(255);
  }
  CryptReleaseContext(ctxt, 0);
#endif

  FStar_Bytes_bytes ret = {.length = x0, .data = (char *)data};
  return ret;
}
#else
FStar_Bytes_bytes CoreCrypto_random(Prims_nat x0) {
  char *data = KRML_HOST_MALLOC(x0);

  int fd = open("/dev/urandom", O_RDONLY);
  if (fd == -1) {
    KRML_HOST_EPRINTF("Cannot open /dev/urandom\n");
    exit(255);
  }
  uint64_t res = read(fd, data, x0);
  if (res != x0) {
    KRML_HOST_EPRINTF(
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

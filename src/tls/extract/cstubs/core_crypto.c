#include "CoreCrypto.h"
#include "kremlib.h"

#if defined(_MSC_VER) || defined(__MINGW32__)
#define IS_WINDOWS 1
  #ifdef _KERNEL_MODE
    #include <nt.h>
    #include <ntrtl.h>
  #else
    #include <windows.h>
  #endif
  #include <bcrypt.h>
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

FStar_Bytes_bytes CoreCrypto_dh_agreement_(CoreCrypto_dh_key *x0,
                                          FStar_Bytes_bytes x1) {
  DH *dh = DH_new();
  FAIL_IF(dh == NULL, "OpenSSL allocation failure dh");

  BIGNUM *p = BN_bin2bn((uint8_t *)x0->dh_params.dh_p.data,
                        x0->dh_params.dh_p.length, NULL);
  BIGNUM *g = BN_bin2bn((uint8_t *)x0->dh_params.dh_g.data,
                        x0->dh_params.dh_g.length, NULL);
  BIGNUM *pub =
      BN_bin2bn((uint8_t *)x0->dh_public.data, x0->dh_public.length, NULL);
  BIGNUM *opub = BN_bin2bn((uint8_t *)x1.data, x1.length, NULL);
  FAIL_IF(p == NULL || g == NULL || pub == NULL || opub == NULL,
          "OpenSSL allocation failure p/g/pub");
  BIGNUM *prv = NULL;
  if (x0->dh_private.tag == FStar_Pervasives_Native_Some) {
    prv = BN_bin2bn((uint8_t *)x0->dh_private.v.data, x0->dh_private.v.length,
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
#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_dh_agreement CoreCrypto_dh_agreement_
#else
FStar_Bytes_bytes CoreCrypto_dh_agreement(CoreCrypto_dh_key x0,
                                          FStar_Bytes_bytes x1) {
  return CoreCrypto_dh_agreement_(&x0, x1);
}
#endif

static inline FStar_Bytes_bytes bytes_of_bn(const BIGNUM *bn) {
  size_t len = BN_num_bytes(bn);
  char *data = KRML_HOST_MALLOC(len);
  BN_bn2bin(bn, (uint8_t *)data);
  FStar_Bytes_bytes ret = {.length = len, .data = data};
  return ret;
}

void CoreCrypto_dh_gen_key_(CoreCrypto_dh_params *x0, CoreCrypto_dh_key *ret) {
  DH *dh = DH_new();
  FAIL_IF(dh == NULL, "OpenSSL allocation failure dh");
  BIGNUM *p = BN_bin2bn((uint8_t *)x0->dh_p.data, x0->dh_p.length, NULL);
  BIGNUM *g = BN_bin2bn((uint8_t *)x0->dh_g.data, x0->dh_g.length, NULL);
  FAIL_IF(p == NULL || g == NULL, "OpenSSL allocation failure p/g");
  DH_set0_pqg(dh, p, NULL, g);
  FAIL_IF(DH_generate_key(dh) == 0, "OpenSSL failure DH_generate_key");

  const BIGNUM *pub, *prv;
  DH_get0_key(dh, &pub, &prv);

  *ret = ((CoreCrypto_dh_key){.dh_params = *x0,
                           .dh_public = bytes_of_bn(pub),
                           .dh_private = {.tag = FStar_Pervasives_Native_Some,
                                          .v = bytes_of_bn(prv)}});

  DH_free(dh);
}
#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_dh_gen_key CoreCrypto_dh_gen_key_
#else
CoreCrypto_dh_key CoreCrypto_dh_gen_key(CoreCrypto_dh_params x0) {
  CoreCrypto_dh_key ret;
  CoreCrypto_dh_gen_key_(&x0, &ret);
  return ret;
}
#endif

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
  KRML_HOST_EXIT(255);
}

FStar_Bytes_bytes CoreCrypto_ecdh_agreement_(CoreCrypto_ec_key *x0,
                                            CoreCrypto_ec_point *x1) {
  EC_KEY *k = key_of_core_crypto_curve(x0->ec_params.curve);
  EC_GROUP *g = EC_GROUP_dup(EC_KEY_get0_group(k));

  if (x0->ec_params.point_compression)
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_COMPRESSED);
  else
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_UNCOMPRESSED);

  BIGNUM *px =
      BN_bin2bn((uint8_t *)x0->ec_point.ecx.data, x0->ec_point.ecx.length, NULL);
  BIGNUM *py =
      BN_bin2bn((uint8_t *)x0->ec_point.ecy.data, x0->ec_point.ecy.length, NULL);
  EC_KEY_set_public_key_affine_coordinates(k, px, py);

  BIGNUM *pr = NULL;
  if (x0->ec_priv.tag == FStar_Pervasives_Native_Some) {
    pr = BN_bin2bn((uint8_t *)x0->ec_priv.v.data, x0->ec_priv.v.length, NULL);
    EC_KEY_set_private_key(k, pr);
  }

  size_t field_size = EC_GROUP_get_degree(g);
  size_t len = (field_size + 7) / 8;
  char *out = KRML_HOST_MALLOC(len);
  memset(out, 0, len);

  EC_POINT *pp = EC_POINT_new(g);
  BIGNUM *ppx = BN_bin2bn((uint8_t *)x1->ecx.data, x1->ecx.length, NULL);
  BIGNUM *ppy = BN_bin2bn((uint8_t *)x1->ecy.data, x1->ecy.length, NULL);
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
#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_ecdh_agreement CoreCrypto_ecdh_agreement_
#else
FStar_Bytes_bytes CoreCrypto_ecdh_agreement(CoreCrypto_ec_key x0,
                                            CoreCrypto_ec_point x1) {
  return CoreCrypto_ecdh_agreement_(&x0, &x1);
}
#endif

void CoreCrypto_ec_gen_key_(CoreCrypto_ec_params *x0, CoreCrypto_ec_key *ret) {
  EC_KEY *k = key_of_core_crypto_curve(x0->curve);
  FAIL_IF(EC_KEY_generate_key(k) == 0, "EC_KEY_generate_key failed");

  EC_GROUP *g = EC_GROUP_dup(EC_KEY_get0_group(k));
  if (x0->point_compression)
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_COMPRESSED);
  else
    EC_GROUP_set_point_conversion_form(g, POINT_CONVERSION_UNCOMPRESSED);

  const EC_POINT *p = EC_KEY_get0_public_key(k);
  BIGNUM *x = BN_new(), *y = BN_new();
  EC_POINT_get_affine_coordinates_GFp(g, p, x, y, NULL);
  const BIGNUM *pr = EC_KEY_get0_private_key(k);

  uint32_t n = size_of_curve(x0->curve);
  *ret = ((CoreCrypto_ec_key){
      .ec_params = *x0,
      .ec_point =
          {.ecx = FStar_Bytes_append(FStar_Bytes_create(n - BN_num_bytes(x), 0),
                                     bytes_of_bn(x)),
           .ecy = FStar_Bytes_append(FStar_Bytes_create(n - BN_num_bytes(y), 0),
                                     bytes_of_bn(y))},
      .ec_priv = {.tag = FStar_Pervasives_Native_Some, .v = bytes_of_bn(pr)}});

  BN_free(y);
  BN_free(x);
  EC_GROUP_free(g);
  EC_KEY_free(k);
}
#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_ec_gen_key CoreCrypto_ec_gen_key_
#else
CoreCrypto_ec_key CoreCrypto_ec_gen_key(CoreCrypto_ec_params x0) {
  CoreCrypto_ec_key ret;
  CoreCrypto_ec_gen_key_(&x0, &ret);
  return ret;
}
#endif

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
  }
  KRML_HOST_EXIT(255);
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
void CoreCrypto_rsa_gen_key_(Prims_int size, CoreCrypto_rsa_key *ret) {
  RSA *rsa = RSA_new();
  BIGNUM *e = BN_new();
  FAIL_IF(e == NULL || rsa == NULL, "OpenSSL allocation failure");

  BN_hex2bn(&e, "010001"); // 65537
  if (RSA_generate_key_ex(rsa, size, e, NULL) != 1) {
    FAIL_IF(true, "Key generation failure");
  }

  const BIGNUM *b_n, *b_e, *b_d;
  RSA_get0_key(rsa, &b_n, &b_e, &b_d);

  *ret = ((CoreCrypto_rsa_key ) {.rsa_mod = bytes_of_bn(b_n),
                            .rsa_pub_exp = bytes_of_bn(b_e),
                            .rsa_prv_exp = {.tag = FStar_Pervasives_Native_Some,
                                            .v = bytes_of_bn(b_d)}});

  RSA_free(rsa);
  BN_free(e);
}
#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_rsa_gen_key CoreCrypto_rsa_gen_key_
#else
CoreCrypto_rsa_key CoreCrypto_rsa_gen_key(Prims_int size) {
  CoreCrypto_rsa_key ret;
  CoreCrypto_rsa_gen_key_(size, &ret);
  return ret;
}
#endif

FStar_Bytes_bytes CoreCrypto_rsa_encrypt_(CoreCrypto_rsa_key *key,
                                         CoreCrypto_rsa_padding padding,
                                         FStar_Bytes_bytes data) {
  BIGNUM *mod =
      BN_bin2bn((uint8_t *)key->rsa_mod.data, key->rsa_mod.length, NULL);
  BIGNUM *exp =
      BN_bin2bn((uint8_t *)key->rsa_pub_exp.data, key->rsa_pub_exp.length, NULL);
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

#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_rsa_encrypt CoreCrypto_rsa_encrypt_
#else
FStar_Bytes_bytes CoreCrypto_rsa_encrypt(CoreCrypto_rsa_key key,
                                         CoreCrypto_rsa_padding padding,
                                         FStar_Bytes_bytes data) {
  return CoreCrypto_rsa_encrypt_(&key, padding, data);
}
#endif

// REMARK: used only in tests
FStar_Pervasives_Native_option__FStar_Bytes_bytes
CoreCrypto_rsa_decrypt_(CoreCrypto_rsa_key *key, CoreCrypto_rsa_padding padding,
                       FStar_Bytes_bytes data) {
  BIGNUM *mod =
      BN_bin2bn((uint8_t *)key->rsa_mod.data, key->rsa_mod.length, NULL);
  BIGNUM *pub =
      BN_bin2bn((uint8_t *)key->rsa_pub_exp.data, key->rsa_pub_exp.length, NULL);
  BIGNUM *prv = NULL;
  if (key->rsa_prv_exp.tag == FStar_Pervasives_Native_Some) {
    prv = BN_bin2bn((uint8_t *)key->rsa_prv_exp.v.data, key->rsa_prv_exp.v.length,
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

#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_rsa_decrypt CoreCrypto_rsa_decrypt_
#else
FStar_Pervasives_Native_option__FStar_Bytes_bytes
CoreCrypto_rsa_decrypt(CoreCrypto_rsa_key key, CoreCrypto_rsa_padding padding,
                       FStar_Bytes_bytes data) {
  return CoreCrypto_rsa_decrypt_(&key, padding, data);
}
#endif

bool CoreCrypto_ec_is_on_curve_(CoreCrypto_ec_params *x0,
                               CoreCrypto_ec_point *x1) {

  EC_KEY *k = key_of_core_crypto_curve(x0->curve);
  const EC_GROUP *group = EC_KEY_get0_group(k);

  EC_POINT *point = EC_POINT_new(group);
  BIGNUM *ppx = BN_bin2bn((uint8_t *)x1->ecx.data, x1->ecx.length, NULL);
  BIGNUM *ppy = BN_bin2bn((uint8_t *)x1->ecy.data, x1->ecy.length, NULL);
  EC_POINT_set_affine_coordinates_GFp(group, point, ppx, ppy, NULL);

  bool ret = EC_POINT_is_on_curve(group, point, NULL);

  BN_free(ppy);
  BN_free(ppx);
  EC_POINT_free(point);
  EC_KEY_free(k);
  return ret;
}
#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_ec_is_on_curve CoreCrypto_ec_is_on_curve_
#else
bool CoreCrypto_ec_is_on_curve(CoreCrypto_ec_params x0,
                               CoreCrypto_ec_point x1) {
  return CoreCrypto_ec_is_on_curve_(&x0, &x1);
}
#endif

FStar_Bytes_bytes
CoreCrypto_aead_encrypt(CryptoTypes_aead_cipher x0,
                        FStar_Bytes_bytes x1,
                        FStar_Bytes_bytes x2,
                        FStar_Bytes_bytes x3,
                        FStar_Bytes_bytes x4) {
  // Hardcoded tag length, may need to be revised for other ciphers
  int olen, tlen = 16;
  EVP_CIPHER_CTX *ctx = NULL;
  const EVP_CIPHER *cipher = NULL;

  switch (x0) {
  case CryptoTypes_AES_128_GCM:
    cipher = EVP_aes_128_gcm();
    break;
  case CryptoTypes_AES_256_GCM:
    cipher = EVP_aes_256_gcm();
    break;
#ifndef OPENSSL_IS_BORINGSSL
  case CryptoTypes_CHACHA20_POLY1305:
    cipher = EVP_chacha20_poly1305();
    break;
#endif
  default:
    FAIL_IF(true, "Unsupported AEAD cipher");
  }

  ctx = EVP_CIPHER_CTX_new();
  FAIL_IF(ctx == NULL, "OpenSSL allocation failure: EVP_CIPHER_CTX_new");

  // Set all parameters to NULL except the cipher type in this initial call
  // Give remaining parameters in subsequent calls (e.g. EVP_CIPHER_set_key),
  // all of which have cipher type set to NULL
  if (EVP_CipherInit_ex(ctx, cipher, NULL, NULL, NULL, 1) == 0)
    FAIL_IF(true, "Cannot initialize cipher context");

  // Disable padding: total amount of data encrypted or decrypted must be a
  // multiple of the block size or an error will occur
  EVP_CIPHER_CTX_set_padding(ctx, 0);

  if (EVP_CIPHER_CTX_set_key_length(ctx, x1.length) == 0)
    FAIL_IF(true, "cannot set CIPHER_CTX key length");

  if (EVP_CipherInit_ex(ctx, NULL, NULL, (uint8_t*) x1.data, NULL, -1) == 0)
    FAIL_IF(true, "cannot set CIPHER_CTX key");

  if(EVP_CIPHER_iv_length(cipher) != x2.length)
    FAIL_IF(true, "wrong IV length");

  if (EVP_CipherInit_ex(ctx, NULL, NULL, NULL, (uint8_t*) x2.data, -1) == 0)
    FAIL_IF(true, "cannot set CIPHER_CTX IV");

  // To specify additional authenticated data a call to EVP_CipherUpdate()
  // should be made with the output parameter out set to NULL.
  if (EVP_CipherUpdate(ctx, NULL, &olen, (uint8_t*) x3.data, x3.length) == 0)
    FAIL_IF(true, "failed to set additional data");

  if (olen != x3.length)
    FAIL_IF(true, "failed to set complete additional data");

  unsigned char *output = KRML_HOST_MALLOC(x4.length + tlen);

  if (EVP_CipherUpdate(ctx, output, &olen, (uint8_t*) x4.data, x4.length) == 0)
    FAIL_IF(true, "encryption failed");

  if (olen != x4.length)
    FAIL_IF(true, "failed to encrypt all data");

  if ((EVP_EncryptFinal_ex(ctx, output, &olen) != 1) || (olen != 0))
    FAIL_IF(true, "final encryption failed");

  unsigned char* tag = output + x4.length;
  if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, tlen, tag) != 1)
    FAIL_IF(true, "failed to get AEAD tag");

  EVP_CIPHER_CTX_free(ctx);

  FStar_Bytes_bytes ret = {.length = x4.length + tlen, .data = (const char*)output};
  return ret;
}


void
CoreCrypto_aead_decrypt_(CryptoTypes_aead_cipher x0,
                        FStar_Bytes_bytes x1,
                        FStar_Bytes_bytes x2,
                        FStar_Bytes_bytes x3,
                        FStar_Bytes_bytes x4, FStar_Pervasives_Native_option__FStar_Bytes_bytes *ret) {
  // Hardcoded tag length, may need to be revised for other ciphers
  int olen, tlen = 16;
  EVP_CIPHER_CTX *ctx = NULL;
  const EVP_CIPHER *cipher = NULL;

  switch (x0) {
  case CryptoTypes_AES_128_GCM:
    cipher = EVP_aes_128_gcm();
    break;
  case CryptoTypes_AES_256_GCM:
    cipher = EVP_aes_256_gcm();
    break;
#ifndef OPENSSL_IS_BORINGSSL
  case CryptoTypes_CHACHA20_POLY1305:
    cipher = EVP_chacha20_poly1305();
    break;
#endif
  default:
    FAIL_IF(true, "Unsupported AEAD cipher");
  }

  ctx = EVP_CIPHER_CTX_new();
  FAIL_IF(ctx == NULL, "OpenSSL allocation failure: EVP_CIPHER_CTX_new");

  // Set all parameters to NULL except the cipher type in this initial call
  // Give remaining parameters in subsequent calls (e.g. EVP_CIPHER_CTX_set_key),
  // all of which have cipher type set to NULL
  if (EVP_CipherInit_ex(ctx, cipher, NULL, NULL, NULL, 0) == 0)
    FAIL_IF(true, "Cannot initialize cipher context");

  // Disable padding: total amount of data encrypted or decrypted must be a
  // multiple of the block size or an error will occur
  EVP_CIPHER_CTX_set_padding(ctx, 0);

  if (EVP_CIPHER_CTX_set_key_length(ctx, x1.length) == 0)
    FAIL_IF(true, "cannot set CIPHER_CTX key length");

  if (EVP_CipherInit_ex(ctx, NULL, NULL, (uint8_t*) x1.data, NULL, -1) == 0)
    FAIL_IF(true, "cannot set CIPHER_CTX key");

  if(EVP_CIPHER_iv_length(cipher) != x2.length)
    FAIL_IF(true, "wrong IV length");

  if (EVP_CipherInit_ex(ctx, NULL, NULL, NULL, (uint8_t*) x2.data, -1) == 0)
    FAIL_IF(true, "cannot set CIPHER_CTX IV");

  // To specify additional authenticated data a call to EVP_CipherUpdate()
  // should be made with the output parameter out set to NULL.
  if (EVP_CipherUpdate(ctx, NULL, &olen, (uint8_t*) x3.data, x3.length) == 0)
    FAIL_IF(true, "failed to set additional data");

  if (olen != x3.length)
    FAIL_IF(true, "failed to set complete additional data");

  unsigned char *output = KRML_HOST_MALLOC(x4.length);

  if (EVP_CipherUpdate(ctx, output, &olen, (uint8_t*) x4.data, x4.length - tlen) == 0)
    FAIL_IF(true, "decryption failed");

  if (olen != x4.length - tlen)
    FAIL_IF(true, "failed to decrypt all data");

  unsigned char* tag = (unsigned char *)x4.data + x4.length - tlen;
  if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, tlen, tag) != 1)
    FAIL_IF(true, "failed to set AEAD tag");

  if ((EVP_DecryptFinal_ex(ctx, output, &olen) != 1)) {
    *ret = ((FStar_Pervasives_Native_option__FStar_Bytes_bytes){
      .tag = FStar_Pervasives_Native_None,
      .v = {.length = 0, .data = 0}});
  } else {
    EVP_CIPHER_CTX_free(ctx);
    *ret = ((FStar_Pervasives_Native_option__FStar_Bytes_bytes){
      .tag = FStar_Pervasives_Native_Some,
      .v = {.length = x4.length - tlen, .data = (const char*)output}});
  }
}

#ifdef KRML_NOSTRUCT_PASSING
#define CoreCrypto_aead_decrypt CoreCrypto_aead_decrypt_
#else
FStar_Pervasives_Native_option__FStar_Bytes_bytes
CoreCrypto_aead_decrypt(CryptoTypes_aead_cipher x0,
                        FStar_Bytes_bytes x1,
                        FStar_Bytes_bytes x2,
                        FStar_Bytes_bytes x3,
                        FStar_Bytes_bytes x4) {
  FStar_Pervasives_Native_option__FStar_Bytes_bytes ret;
  CoreCrypto_aead_decrypt_(x0, x1, x2, x3, x4, &ret);
  return ret;
}
#endif


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
                           .dh_private = {.tag = FStar_Pervasives_Native_None,
                                          .v = {.length = 0, .data = 0}}};
  return ret;
}

CoreCrypto_ec_key CoreCrypto_ec_gen_key(CoreCrypto_ec_params x0) {
  FAIL_IF(true, "No OpenSSL support.");
  CoreCrypto_ec_key ret = {.ec_params = x0,
                           .ec_point = {.ecx = 0, .ecy = 0},
                           .ec_priv = {.tag = FStar_Pervasives_Native_None,
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
      .rsa_prv_exp = {.tag = FStar_Pervasives_Native_None, .v = 0}};

  return ret;
}

// REMARK: used only in tests
FStar_Pervasives_Native_option__FStar_Bytes_bytes
CoreCrypto_rsa_decrypt(CoreCrypto_rsa_key key, CoreCrypto_rsa_padding padding,
                       FStar_Bytes_bytes data) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Pervasives_Native_option__FStar_Bytes_bytes ret = {
      .tag = FStar_Pervasives_Native_None, .v = {.length = 0, .data = 0}};
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

FStar_Bytes_bytes CoreCrypto_aead_encrypt(CryptoTypes_aead_cipher x0,
                                          FStar_Bytes_bytes x1,
                                          FStar_Bytes_bytes x2,
                                          FStar_Bytes_bytes x3,
                                          FStar_Bytes_bytes x4) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Bytes_bytes ret = {.length = 0, .data = 0};
  return ret;
}

FStar_Pervasives_Native_option__FStar_Bytes_bytes
CoreCrypto_aead_decrypt(CryptoTypes_aead_cipher x0,
                        FStar_Bytes_bytes x1,
                        FStar_Bytes_bytes x2,
                        FStar_Bytes_bytes x3,
                        FStar_Bytes_bytes x4) {
  FAIL_IF(true, "No OpenSSL support.");
  FStar_Pervasives_Native_option__FStar_Bytes_bytes ret = {
    .tag = FStar_Pervasives_Native_None, .v = {.length = 0, .data = 0}};
  return ret;
}
#endif // NO_OPENSSL

#if IS_WINDOWS

#ifndef _KERNEL_MODE
#define NT_SUCCESS(Status)          (((NTSTATUS)(Status)) >= 0)
#endif

static BCRYPT_ALG_HANDLE g_hAlgRandom;

// Perform per-process initialization, called from FFI_mitls_init.  Return 0 for failure.
int CoreCrypto_Initialize(void)
{

  NTSTATUS st = BCryptOpenAlgorithmProvider(&g_hAlgRandom, BCRYPT_RNG_ALGORITHM, NULL,
#ifdef _KERNEL_MODE
                    BCRYPT_PROV_DISPATCH
#else
                    0
#endif
                    );
  if (!NT_SUCCESS(st)) {
    KRML_HOST_EPRINTF("BCryptOpenAlgorithmProvider failed: 0x%x\n", (unsigned int)st);
    return 0;
  }
  return 1;
}

// Perform per-process termination, called from FFI_mitls_cleanup.
void CoreCrypto_Terminate(void)
{
    BCryptCloseAlgorithmProvider(g_hAlgRandom, 0);
}

FStar_Bytes_bytes CoreCrypto_random(Prims_nat x0) {
  NTSTATUS st;

  PUCHAR data = KRML_HOST_MALLOC(x0);

  st = BCryptGenRandom(g_hAlgRandom, data, x0, 0);
  if (!NT_SUCCESS(st)) {
    KRML_HOST_EPRINTF("Cannot read random bytes: 0x%x\n", (unsigned int)st);
    KRML_HOST_EXIT(255);
  }

  FStar_Bytes_bytes ret = {.length = x0, .data = (char *)data};
  return ret;
}
#else

// Perform per-process initialization, called from FFI_mitls_init.  Return 0 for failure.
int CoreCrypto_Initialize(void)
{
    return 1;
}

// Perform per-process termination, called from FFI_mitls_cleanup.
void CoreCrypto_Terminate(void)
{
}

FStar_Bytes_bytes CoreCrypto_random(Prims_nat x0) {
  char *data = KRML_HOST_MALLOC(x0);

  int fd = open("/dev/urandom", O_RDONLY);
  if (fd == -1) {
    KRML_HOST_EPRINTF("Cannot open /dev/urandom\n");
    KRML_HOST_EXIT(255);
  }
  uint64_t res = read(fd, data, x0);
  if (res != x0) {
    KRML_HOST_EPRINTF(
            "Error on reading, expected %" PRIi32 " bytes, got %" PRIu64
            " bytes\n",
            x0, res);
    KRML_HOST_EXIT(255);
  }
  close(fd);

  FStar_Bytes_bytes ret = {.length = x0, .data = data};
  return ret;
}
#endif

// We need this to expose CoreCrypto_Initialize from F* where
// identifiers must start with lowercase
int CoreCrypto_init(void)
{
  return CoreCrypto_Initialize();
}

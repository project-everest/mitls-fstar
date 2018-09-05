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

#else // NO_OPENSSL

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

#endif // NO_OPENSSL

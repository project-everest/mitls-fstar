#include "CoreCrypto.h"
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>

#define FAIL_IF(msg) do { fprintf(stderr, "%s %s\n", __FUNCTION__, msg); exit(253); } while (0)
#define TODO(t) { t _x = { 0 }; fprintf(stderr, "%s TODO\n", __FUNCTION__); exit(252); return _x; }

FStar_Bytes_bytes CoreCrypto_dh_agreement(CoreCrypto_dh_key x0,
                                          FStar_Bytes_bytes x1) {
  /* DH *dh = DH_new();
  BIGNUM *p = BN_bin2bn(x0.dh_params.dh_p.data, x0.dh_params.dh_p.length, NULL);
  BIGNUM *q = BN_bin2bn(x0.dh_params.dh_q.data, x0.dh_params.dh_q.length, NULL);
  BIGNUM *pub = BN_bin2bn(x0.dh_public.data, x0.dh_public.length, NULL);
  FAIL_IF("OpenSSL allocation failure p/q/pub", p == NULL || q == NULL || pub == NULL);
  BIGNUM *prv = NULL;
  if (x0.dh_private.tag == FStar_Pervasives_Native_Some) {
    prv = BN_bin2bn(x0.dh_private.val.case_Some.data, x0.dh_private.val.case_Some.length, NULL);
    FAIL_IF("OpenSSL allocation failure prv", prv == NULL);
  }
  DH_set0_pqg(dh, p, NULL, g);
  DH_set0_key(dh, pub, prv); */
  TODO(FStar_Bytes_bytes);
}

CoreCrypto_dh_key CoreCrypto_dh_gen_key(CoreCrypto_dh_params x0) {
  TODO(CoreCrypto_dh_key);
}

FStar_Bytes_bytes CoreCrypto_ecdh_agreement(CoreCrypto_ec_key x0,
                                            CoreCrypto_ec_point x1) {
  TODO(FStar_Bytes_bytes);
}

CoreCrypto_ec_key CoreCrypto_ec_gen_key(CoreCrypto_ec_params x0) {
  TODO(CoreCrypto_ec_key);
}

bool CoreCrypto_ec_is_on_curve(CoreCrypto_ec_params x0, CoreCrypto_ec_point x1) {
  TODO(bool);
}

FStar_Pervasives_Native_option__CoreCrypto_key
CoreCrypto_get_key_from_cert(FStar_Bytes_bytes x0) {
  TODO(FStar_Pervasives_Native_option__CoreCrypto_key);
}

FStar_Bytes_bytes CoreCrypto_hash(CoreCrypto_hash_alg x0, FStar_Bytes_bytes x1) {
  TODO(FStar_Bytes_bytes);
}

FStar_Pervasives_Native_option__Prims_list__FStar_Bytes_bytes
CoreCrypto_load_chain(Prims_string x0) {
  TODO(FStar_Pervasives_Native_option__Prims_list__FStar_Bytes_bytes);
}

#ifdef __WINDOWS__
FStar_Bytes_bytes CoreCrypto_random(Prims_nat x0) {
  char *data = malloc(x0);

  HCRYPTPROV ctxt;
  if (! (CryptAcquireContext(&ctxt, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT))) {
    DWORD error = GetLastError();
    fprintf(e, "Cannot acquire crypto context: 0x%lx\n", error);
    exit(255);
  }
  if (! (CryptGenRandom(ctxt, x0, data))) {
    fprintf(stderr, "Cannot read random bytes\n");
    exit(255);
  }
  CryptReleaseContext(ctxt, 0);

  FStar_Bytes_bytes ret = { .length = x0, .data = data };
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
    fprintf(stderr, "Error on reading, expected %" PRIi32 " bytes, got %" PRIu64 " bytes\n", x0, res);
    exit(255);
  }
  close(fd);

  FStar_Bytes_bytes ret = { .length = x0, .data = data };
  return ret;
}
#endif

CoreCrypto_rsa_key CoreCrypto_rsa_gen_key(Prims_int x0) {
  TODO(CoreCrypto_rsa_key);
}

bool CoreCrypto_validate_chain(Prims_list__FStar_Bytes_bytes *x0, bool x1,
                               FStar_Pervasives_Native_option__Prims_string x2,
                               Prims_string x3) {
  TODO(bool);
}

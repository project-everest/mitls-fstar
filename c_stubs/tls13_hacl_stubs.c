#include "tls13_hacl_stubs.h"

#include <limits.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_AEAD_Chacha20Poly1305.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_Hash_SHA2.h"
#include "Lib_RandomBuffer_System.h"

static bool fits_u32(size_t len) {
  return len <= UINT32_MAX;
}

bool tls13_hacl_random_bytes(uint8_t *out, size_t out_len) {
  if (out_len != 0 && out == NULL) {
    return false;
  }
  if (!fits_u32(out_len)) {
    return false;
  }
  return Lib_RandomBuffer_System_randombytes(out, (uint32_t)out_len);
}

bool tls13_hacl_sha256(uint8_t out[32], const uint8_t *input, size_t input_len) {
  if (out == NULL || (input_len != 0 && input == NULL) || !fits_u32(input_len)) {
    return false;
  }
  Hacl_Hash_SHA2_hash_256(out, (uint8_t *)input, (uint32_t)input_len);
  return true;
}

bool tls13_hacl_hmac_sha256(
    uint8_t out[32],
    const uint8_t *key,
    size_t key_len,
    const uint8_t *input,
    size_t input_len) {
  if (out == NULL || (key_len != 0 && key == NULL) ||
      (input_len != 0 && input == NULL) || !fits_u32(key_len) ||
      !fits_u32(input_len)) {
    return false;
  }
  Hacl_HMAC_compute_sha2_256(
      out, (uint8_t *)key, (uint32_t)key_len, (uint8_t *)input, (uint32_t)input_len);
  return true;
}

bool tls13_hacl_hkdf_extract_sha256(
    uint8_t out[32],
    const uint8_t *salt,
    size_t salt_len,
    const uint8_t *ikm,
    size_t ikm_len) {
  if (out == NULL || (salt_len != 0 && salt == NULL) ||
      (ikm_len != 0 && ikm == NULL) || !fits_u32(salt_len) || !fits_u32(ikm_len)) {
    return false;
  }
  Hacl_HKDF_extract_sha2_256(
      out, (uint8_t *)salt, (uint32_t)salt_len, (uint8_t *)ikm, (uint32_t)ikm_len);
  return true;
}

bool tls13_hacl_hkdf_expand_sha256(
    uint8_t *out,
    size_t out_len,
    const uint8_t prk[32],
    const uint8_t *info,
    size_t info_len) {
  if ((out_len != 0 && out == NULL) || prk == NULL ||
      (info_len != 0 && info == NULL) || !fits_u32(out_len) || !fits_u32(info_len)) {
    return false;
  }
  Hacl_HKDF_expand_sha2_256(
      out, (uint8_t *)prk, 32, (uint8_t *)info, (uint32_t)info_len, (uint32_t)out_len);
  return true;
}

bool tls13_hacl_hkdf_expand_label_sha256(
    uint8_t *out,
    size_t out_len,
    const uint8_t prk[32],
    const uint8_t *label,
    size_t label_len,
    const uint8_t *context,
    size_t context_len) {
  static const uint8_t prefix[] = {'t', 'l', 's', '1', '3', ' '};
  uint8_t info[2 + 1 + sizeof prefix + 255 + 1 + 255];
  size_t full_label_len = sizeof prefix + label_len;
  size_t info_len = 2 + 1 + full_label_len + 1 + context_len;

  if ((out_len != 0 && out == NULL) || prk == NULL ||
      (label_len != 0 && label == NULL) || (context_len != 0 && context == NULL) ||
      out_len > UINT16_MAX || label_len > 249 || context_len > 255 ||
      !fits_u32(out_len)) {
    return false;
  }

  info[0] = (uint8_t)(out_len >> 8);
  info[1] = (uint8_t)out_len;
  info[2] = (uint8_t)full_label_len;
  memcpy(&info[3], prefix, sizeof prefix);
  if (label_len != 0) {
    memcpy(&info[3 + sizeof prefix], label, label_len);
  }
  info[3 + full_label_len] = (uint8_t)context_len;
  if (context_len != 0) {
    memcpy(&info[4 + full_label_len], context, context_len);
  }

  return tls13_hacl_hkdf_expand_sha256(out, out_len, prk, info, info_len);
}

bool tls13_hacl_finished_verify_data_sha256(
    uint8_t out[32],
    const uint8_t base_key[32],
    const uint8_t transcript_hash[32]) {
  static const uint8_t label[] = {'f', 'i', 'n', 'i', 's', 'h', 'e', 'd'};
  uint8_t finished_key[32];

  if (out == NULL || base_key == NULL || transcript_hash == NULL) {
    return false;
  }
  if (!tls13_hacl_hkdf_expand_label_sha256(
          finished_key, sizeof finished_key, base_key, label, sizeof label, NULL, 0)) {
    return false;
  }
  return tls13_hacl_hmac_sha256(out, finished_key, sizeof finished_key, transcript_hash, 32);
}

bool tls13_hacl_x25519_public_from_private(uint8_t out[32], const uint8_t sk[32]) {
  if (out == NULL || sk == NULL) {
    return false;
  }
  Hacl_Curve25519_51_secret_to_public(out, (uint8_t *)sk);
  return true;
}

bool tls13_hacl_x25519_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[32]) {
  if (out == NULL || sk == NULL || pk == NULL) {
    return false;
  }
  return Hacl_Curve25519_51_ecdh(out, (uint8_t *)sk, (uint8_t *)pk);
}

bool tls13_record_nonce(uint8_t out[12], const uint8_t static_iv[12], uint64_t sequence_number) {
  if (out == NULL || static_iv == NULL) {
    return false;
  }
  memcpy(out, static_iv, 12);
  for (size_t i = 0; i < 8; ++i) {
    uint8_t seq_byte = (uint8_t)(sequence_number >> (56 - 8 * i));
    out[4 + i] ^= seq_byte;
  }
  return true;
}

bool tls13_hacl_chacha20_poly1305_seal(
    uint8_t *ciphertext,
    uint8_t tag[16],
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len) {
  if ((plaintext_len != 0 && (ciphertext == NULL || plaintext == NULL)) ||
      (aad_len != 0 && aad == NULL) || tag == NULL || key == NULL || nonce == NULL ||
      !fits_u32(aad_len) || !fits_u32(plaintext_len)) {
    return false;
  }
  Hacl_AEAD_Chacha20Poly1305_encrypt(
      ciphertext,
      tag,
      (uint8_t *)plaintext,
      (uint32_t)plaintext_len,
      (uint8_t *)aad,
      (uint32_t)aad_len,
      (uint8_t *)key,
      (uint8_t *)nonce);
  return true;
}

bool tls13_hacl_chacha20_poly1305_open(
    uint8_t *plaintext,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext,
    size_t ciphertext_len,
    const uint8_t tag[16]) {
  if ((ciphertext_len != 0 && (plaintext == NULL || ciphertext == NULL)) ||
      (aad_len != 0 && aad == NULL) || tag == NULL || key == NULL || nonce == NULL ||
      !fits_u32(aad_len) || !fits_u32(ciphertext_len)) {
    return false;
  }
  return Hacl_AEAD_Chacha20Poly1305_decrypt(
             plaintext,
             (uint8_t *)ciphertext,
             (uint32_t)ciphertext_len,
             (uint8_t *)aad,
             (uint32_t)aad_len,
             (uint8_t *)key,
             (uint8_t *)nonce,
             (uint8_t *)tag) == 0;
}

bool tls13_hacl_chacha20_poly1305_seal_combined(
    uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len) {
  if (plaintext_len > SIZE_MAX - 16 || ciphertext_and_tag_len != plaintext_len + 16) {
    return false;
  }
  return tls13_hacl_chacha20_poly1305_seal(
      ciphertext_and_tag,
      ciphertext_and_tag + plaintext_len,
      key,
      nonce,
      aad,
      aad_len,
      plaintext,
      plaintext_len);
}

bool tls13_hacl_chacha20_poly1305_open_combined(
    uint8_t *plaintext,
    size_t plaintext_len,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len) {
  if (plaintext_len > SIZE_MAX - 16 || ciphertext_and_tag_len != plaintext_len + 16) {
    return false;
  }
  return tls13_hacl_chacha20_poly1305_open(
      plaintext,
      key,
      nonce,
      aad,
      aad_len,
      ciphertext_and_tag,
      plaintext_len,
      ciphertext_and_tag + plaintext_len);
}

#ifndef TLS13_USE_EXTRACTED_RECORD
static bool tls13_record_state_valid(TLS13_Record_record_state st) {
  return st.key != NULL && st.iv != NULL && st.seq != NULL && st.installed != NULL;
}

TLS13_Record_record_state TLS13_Record_record_state_new(void) {
  TLS13_Record_record_state st = {
      .key = calloc(32, sizeof(uint8_t)),
      .iv = calloc(12, sizeof(uint8_t)),
      .seq = calloc(1, sizeof(uint64_t)),
      .installed = calloc(1, sizeof(bool)),
  };
  if (!tls13_record_state_valid(st)) {
    TLS13_Record_record_state_free(st);
    TLS13_Record_record_state empty = {0};
    return empty;
  }
  return st;
}

void TLS13_Record_record_state_free(TLS13_Record_record_state st) {
  free(st.key);
  free(st.iv);
  free(st.seq);
  free(st.installed);
}

bool TLS13_Record_can_advance_seq(TLS13_Record_record_state st) {
  return tls13_record_state_valid(st) && *st.seq != UINT64_MAX;
}

bool TLS13_Record_seq_eq(TLS13_Record_record_state st, uint64_t expected) {
  return tls13_record_state_valid(st) && *st.seq == expected;
}

bool TLS13_Record_application_keys_match(
    TLS13_Record_record_state st,
    uint8_t *key,
    uint8_t *iv) {
  return tls13_record_state_valid(st) && *st.installed && key != NULL && iv != NULL &&
         memcmp(st.key, key, 32) == 0 && memcmp(st.iv, iv, 12) == 0;
}

bool TLS13_Record_has_seal_keys(TLS13_Record_record_state st) {
  return tls13_record_state_valid(st) && *st.installed;
}

void TLS13_Record_advance_seq(TLS13_Record_record_state st) {
  if (TLS13_Record_can_advance_seq(st)) {
    ++*st.seq;
  }
}

void TLS13_Record_install_keys(
    TLS13_Record_record_state st,
    TLS13_Record_Spec_epoch epoch,
    uint8_t *key,
    uint8_t *iv) {
  (void)epoch;
  if (!tls13_record_state_valid(st) || key == NULL || iv == NULL) {
    return;
  }
  memcpy(st.key, key, 32);
  memcpy(st.iv, iv, 12);
  *st.seq = 0;
  *st.installed = true;
}

void TLS13_Record_install_handshake_keys_runtime(
    TLS13_Record_record_state st,
    uint8_t *key,
    uint8_t *iv) {
  TLS13_Record_install_keys(st, TLS13_Record_Spec_Handshake, key, iv);
}

void TLS13_Record_install_application_keys_runtime(
    TLS13_Record_record_state st,
    uint8_t *key,
    uint8_t *iv) {
  TLS13_Record_install_keys(st, TLS13_Record_Spec_Application, key, iv);
}

static bool tls13_record_seal(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out,
    bool update_seq) {
  if (!tls13_record_state_valid(st) || !*st.installed ||
      (aad_len != 0 && aad == NULL) || (plain_len != 0 && plain == NULL) ||
      (plain_len != 0 && out == NULL) || plain_len > SIZE_MAX - 16 ||
      (update_seq && *st.seq == UINT64_MAX)) {
    return false;
  }
  uint8_t nonce[12];
  if (!tls13_record_nonce(nonce, st.iv, *st.seq) ||
      !tls13_hacl_chacha20_poly1305_seal_combined(
          out, plain_len + 16, st.key, nonce, aad, aad_len, plain, plain_len)) {
    return false;
  }
  if (update_seq) {
    ++*st.seq;
  }
  return true;
}

bool TLS13_Record_seal_application(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out) {
  return tls13_record_seal(st, aad, aad_len, plain, plain_len, out, true);
}

bool TLS13_Record_seal_application_no_update(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out) {
  return tls13_record_seal(st, aad, aad_len, plain, plain_len, out, false);
}

bool TLS13_Record_seal_application_runtime(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out) {
  return tls13_record_seal(st, aad, aad_len, plain, plain_len, out, true);
}

static bool tls13_record_open(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out,
    bool update_seq) {
  if (!tls13_record_state_valid(st) || !*st.installed ||
      (aad_len != 0 && aad == NULL) || cipher_len < 16 ||
      (cipher_len != 16 && (cipher == NULL || out == NULL)) ||
      (update_seq && *st.seq == UINT64_MAX)) {
    return false;
  }
  uint8_t nonce[12];
  size_t plain_len = cipher_len - 16;
  if (!tls13_record_nonce(nonce, st.iv, *st.seq) ||
      !tls13_hacl_chacha20_poly1305_open_combined(
          out, plain_len, st.key, nonce, aad, aad_len, cipher, cipher_len)) {
    return false;
  }
  if (update_seq) {
    ++*st.seq;
  }
  return true;
}

bool TLS13_Record_open_application(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out) {
  return tls13_record_open(st, aad, aad_len, cipher, cipher_len, out, true);
}

bool TLS13_Record_peek_open_application(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out) {
  return tls13_record_open(st, aad, aad_len, cipher, cipher_len, out, false);
}

bool TLS13_Record_open_application_runtime(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out) {
  return tls13_record_open(st, aad, aad_len, cipher, cipher_len, out, true);
}
#endif

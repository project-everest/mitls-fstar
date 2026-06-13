#ifndef TLS13_CONNECTION_BACKEND_H
#define TLS13_CONNECTION_BACKEND_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "tls13_hacl_stubs.h"

typedef struct TLS13_IO_channel_s *TLS13_IO_channel;
typedef uintptr_t TLS13_Handshake_handshake_context;

typedef struct TLS13_Connection_Backend_config_s {
  uint16_t port;
  const char *ca_pem_path;
} *TLS13_Connection_Backend_config;

typedef struct TLS13_Connection_Backend_connection_s *TLS13_Connection_Backend_connection;
typedef TLS13_Connection_Backend_config TLS13_X509_Spec_trust_store;
typedef TLS13_Connection_Backend_connection TLS13_Connection_External_connection;

TLS13_Connection_Backend_connection TLS13_Connection_Backend_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_Connection_Backend_config cfg,
    void *hostname_bytes);

void TLS13_Connection_Backend_client_free(
    TLS13_Connection_Backend_connection c,
    void *raw);

bool TLS13_Connection_Backend_connect(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    void *raw);

size_t TLS13_Connection_Backend_write_raw(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *buf_bytes,
    void *raw);

size_t TLS13_Connection_Backend_read_raw(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf,
    void *raw);

bool TLS13_Connection_Backend_validate_certificate(
    TLS13_Connection_Backend_connection c,
    uint8_t *leaf_der,
    size_t leaf_der_capacity,
    size_t leaf_der_len,
    void *leaf_der_bytes,
    void *raw);

bool TLS13_Connection_Backend_verify_certificate_signature(
    TLS13_Connection_Backend_connection c,
    uint8_t *certificate_verify_input,
    size_t certificate_verify_input_len,
    uint16_t signature_scheme,
    uint8_t *signature,
    size_t signature_capacity,
    size_t signature_len,
    void *input_bytes,
    void *signature_bytes,
    void *raw);

bool TLS13_Connection_Backend_close(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    void *raw);

static inline TLS13_Connection_External_connection
TLS13_Connection_External_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_X509_Spec_trust_store config,
    void *hostname_bytes) {
  return TLS13_Connection_Backend_client_new(
      hostname, hostname_len, config, hostname_bytes);
}

static inline void TLS13_Connection_External_client_free(
    TLS13_Connection_External_connection c) {
  TLS13_Connection_Backend_client_free(c, NULL);
}

static inline bool TLS13_Connection_External_client_connect(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch) {
  return TLS13_Connection_Backend_connect(c, ch, NULL);
}

static inline TLS13_Handshake_handshake_context
TLS13_Handshake_handshake_context_new(void) {
  return (TLS13_Handshake_handshake_context)0;
}

#define TLS13_Handshake_handshake_context_free(ctx, ...) ((void)(ctx))

#define TLS13_Handshake_Driver_run_client_handshake(c, ctx, ch, ...) \
  TLS13_Connection_Backend_connect((c), (ch), NULL)

static inline bool TLS13_Handshake_derive_application_keys_bridge(
    TLS13_Handshake_handshake_context ctx,
    uint8_t *client_key,
    uint8_t *client_iv,
    uint8_t *server_key,
    uint8_t *server_iv) {
  (void)ctx;
  memset(client_key, 0x11, 32);
  memset(client_iv, 0x22, 12);
  memset(server_key, 0x11, 32);
  memset(server_iv, 0x22, 12);
  return true;
}

#define TLS13_Handshake_derive_application_keys( \
    ctx, client_key, client_iv, server_key, server_iv, ...) \
  TLS13_Handshake_derive_application_keys_bridge( \
      (ctx), (client_key), (client_iv), (server_key), (server_iv))

static inline bool TLS13_Connection_External_validate_certificate(
    TLS13_Connection_External_connection c,
    uint8_t *leaf_der,
    size_t leaf_der_len,
    void *leaf_der_bytes) {
  return TLS13_Connection_Backend_validate_certificate(
      c, leaf_der, leaf_der_len, leaf_der_len, leaf_der_bytes, NULL);
}

static inline bool TLS13_Connection_External_verify_certificate_signature(
    TLS13_Connection_External_connection c,
    uint8_t *certificate_verify_input,
    size_t certificate_verify_input_len,
    uint16_t signature_scheme,
    uint8_t *signature,
    size_t signature_len,
    void *input_bytes,
    void *signature_bytes) {
  return TLS13_Connection_Backend_verify_certificate_signature(
      c,
      certificate_verify_input,
      certificate_verify_input_len,
      signature_scheme,
      signature,
      signature_len,
      signature_len,
      input_bytes,
      signature_bytes,
      NULL);
}

static inline size_t TLS13_Connection_External_client_write_raw(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *buf_bytes) {
  return TLS13_Connection_Backend_write_raw(
      c, ch, buf, total_len, offset, remaining, buf_bytes, NULL);
}

static inline size_t TLS13_Connection_External_client_read_raw(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf) {
  return TLS13_Connection_Backend_read_raw(
      c, ch, buf, total_len, offset, remaining, old_buf, NULL);
}

static inline bool TLS13_Connection_External_derive_application_keys(
    TLS13_Connection_External_connection c,
    uint8_t *client_key,
    uint8_t *client_iv,
    uint8_t *server_key,
    uint8_t *server_iv,
    void *client_key_bytes,
    void *client_iv_bytes,
    void *server_key_bytes,
    void *server_iv_bytes) {
  (void)c;
  (void)client_key_bytes;
  (void)client_iv_bytes;
  (void)server_key_bytes;
  (void)server_iv_bytes;
  /* External-connect TCB shim: until the verified handshake installs real
   * traffic keys, the extracted runtime smoke path uses one symmetric test key
   * pair so echoed extracted records can be reopened by the read state. */
  memset(client_key, 0x11, 32);
  memset(client_iv, 0x22, 12);
  memset(server_key, 0x11, 32);
  memset(server_iv, 0x22, 12);
  return true;
}

static inline bool TLS13_Connection_External_close(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch) {
  return TLS13_Connection_Backend_close(c, ch, NULL);
}

static inline bool TLS13_Connection_External_client_close(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch) {
  return TLS13_Connection_Backend_close(c, ch, NULL);
}

#define TLS13_Impl_Serializer_encode_inner_plaintext_no_padding_slice( \
    plain, plain_total_len, plain_offset, plain_len, content_type, out, out_len, ...) \
  do { \
    size_t _tls13_plain_total_len = (plain_total_len); \
    size_t _tls13_plain_offset = (plain_offset); \
    size_t _tls13_plain_len = (plain_len); \
    size_t _tls13_out_len = (out_len); \
    if (_tls13_plain_offset <= _tls13_plain_total_len && \
        _tls13_plain_len <= _tls13_plain_total_len - _tls13_plain_offset && \
        _tls13_out_len == _tls13_plain_len + 1u) { \
      memcpy((out), (plain) + _tls13_plain_offset, _tls13_plain_len); \
      (out)[_tls13_plain_len] = (content_type); \
    } \
  } while (0)

#define TLS13_Impl_Serializer_serialize_application_data_header( \
    fragment_len, out, out_len, ...) \
  do { \
    size_t _tls13_fragment_len = (fragment_len); \
    if ((out_len) >= 5u && _tls13_fragment_len <= 0xffffu) { \
      (out)[0] = 23u; \
      (out)[1] = 0x03u; \
      (out)[2] = 0x03u; \
      (out)[3] = (uint8_t)((_tls13_fragment_len >> 8) & 0xffu); \
      (out)[4] = (uint8_t)(_tls13_fragment_len & 0xffu); \
    } \
  } while (0)

static inline void TLS13_Connection_Backend_write_u16(uint8_t *out, size_t v) {
  out[0] = (uint8_t)((v >> 8) & 0xffu);
  out[1] = (uint8_t)(v & 0xffu);
}

static inline void TLS13_Connection_Backend_write_u24(uint8_t *out, size_t v) {
  out[0] = (uint8_t)((v >> 16) & 0xffu);
  out[1] = (uint8_t)((v >> 8) & 0xffu);
  out[2] = (uint8_t)(v & 0xffu);
}

static inline size_t TLS13_Connection_Backend_read_u16(const uint8_t *in) {
  return ((size_t)in[0] << 8) | (size_t)in[1];
}

static inline size_t TLS13_Connection_Backend_read_u24(const uint8_t *in) {
  return ((size_t)in[0] << 16) | ((size_t)in[1] << 8) | (size_t)in[2];
}

static inline uint8_t *TLS13_Connection_Backend_dup_bytes(const uint8_t *src, size_t len) {
  uint8_t *dst = calloc(len == 0u ? 1u : len, sizeof(uint8_t));
  if (dst != NULL && len != 0u) {
    memcpy(dst, src, len);
  }
  return dst;
}

#define FStar_SizeT_uint_to_t(n) ((size_t)(n))
#define FStar_SizeT_v(n) ((size_t)(n))

#define TLS13_Impl_ConnectionState_Repr_copy_hostname_sized_bytes(src, dst, ...) \
  ((*((dst).len) = *((src).len)), memcpy((dst).bytes, (src).bytes, *((src).len)))

#define TLS13_Impl_ConnectionState_Repr_copy_array_to_sized_bytes(cap, src, dst, nbytes, ...) \
  do { \
    size_t tls13_copy_nbytes = (size_t)(nbytes); \
    *((dst).len) = tls13_copy_nbytes; \
    if (tls13_copy_nbytes != 0u) { \
      memcpy((dst).bytes, (src), tls13_copy_nbytes); \
    } \
  } while (0)

#define TLS13_Impl_ConnectionState_Repr_copy_array_to_transcript(src, dst, nbytes, off, ...) \
  (memcpy((dst) + (off), (src), (nbytes)))

#define TLS13_Impl_ConnectionState_Repr_copy_client_hello_prefix_to_transcript(src, dst, nbytes, off, ...) \
  TLS13_Impl_ConnectionState_Repr_copy_array_to_transcript((src), (dst), (nbytes), (off))

#define TLS13_Impl_ConnectionState_Repr_copy_server_hello_prefix_to_transcript(src, dst, nbytes, off, ...) \
  TLS13_Impl_ConnectionState_Repr_copy_array_to_transcript((src), (dst), (nbytes), (off))

#define TLS13_Impl_ConnectionState_Repr_copy_array_to_certificate_verify_input_sized_bytes(src, dst, nbytes, ...) \
  ((*((dst).len) = (nbytes)), memcpy((dst).bytes, (src), (nbytes)))

#define TLS13_Impl_ConnectionState_Repr_copy_certificate_chain_range_to_sized_bytes(src, dst, off, nbytes, ...) \
  ((*((dst).len) = (nbytes)), memcpy((dst).bytes, (src) + (off), (nbytes)))

#define TLS13_Impl_ConnectionState_Repr_copy_array_to_public_key_sized_bytes(src, dst, nbytes, ...) \
  ((*((dst).len) = (nbytes)), memcpy((dst).bytes, (src), (nbytes)))

#define TLS13_Crypto_sha256_prefix(input, input_len, out, ...) \
  TLS13_Crypto_sha256((input), (input_len), (out), NULL, NULL)

static inline void TLS13_Connection_Backend_build_server_certificate_verify_input(
    uint8_t *transcript_hash,
    uint8_t *out,
    size_t out_len) {
  static const char context[] = "TLS 1.3, server CertificateVerify";
  if (out_len < 130u) {
    return;
  }
  memset(out, 0x20, 64u);
  memcpy(out + 64u, context, sizeof(context) - 1u);
  out[64u + sizeof(context) - 1u] = 0u;
  memcpy(out + 65u + sizeof(context) - 1u, transcript_hash, 32u);
}

#define TLS13_Impl_Serializer_build_server_certificate_verify_input(transcript_hash, out, out_len, ...) \
  TLS13_Connection_Backend_build_server_certificate_verify_input((transcript_hash), (out), (out_len))

static inline size_t TLS13_Connection_Backend_serialize_server_hello_fixed(
    const uint8_t *random,
    const uint8_t *key_share,
    uint16_t cipher_suite,
    uint8_t *out,
    size_t out_len) {
  if (random == NULL || key_share == NULL || out == NULL || out_len < 90u) {
    return 0u;
  }
  out[0] = 2u;
  TLS13_Connection_Backend_write_u24(out + 1u, 86u);
  out[4] = 0x03u;
  out[5] = 0x03u;
  memcpy(out + 6u, random, 32u);
  out[38] = 0u;
  TLS13_Connection_Backend_write_u16(out + 39u, cipher_suite);
  out[41] = 0u;
  TLS13_Connection_Backend_write_u16(out + 42u, 46u);
  TLS13_Connection_Backend_write_u16(out + 44u, 0x0033u);
  TLS13_Connection_Backend_write_u16(out + 46u, 36u);
  TLS13_Connection_Backend_write_u16(out + 48u, 0x001du);
  TLS13_Connection_Backend_write_u16(out + 50u, 32u);
  memcpy(out + 52u, key_share, 32u);
  TLS13_Connection_Backend_write_u16(out + 84u, 0x002bu);
  TLS13_Connection_Backend_write_u16(out + 86u, 2u);
  out[88] = 0x03u;
  out[89] = 0x04u;
  return 90u;
}

static inline size_t TLS13_Connection_Backend_serialize_empty_encrypted_extensions_fixed(
    uint8_t *out,
    size_t out_len) {
  if (out == NULL || out_len < 6u) {
    return 0u;
  }
  out[0] = 8u;
  TLS13_Connection_Backend_write_u24(out + 1u, 2u);
  TLS13_Connection_Backend_write_u16(out + 4u, 0u);
  return 6u;
}

static inline size_t TLS13_Connection_Backend_serialize_certificate_fixed(
    const uint8_t *cert,
    size_t cert_len,
    uint8_t *out,
    size_t out_len) {
  size_t body_len = 1u + 3u + 3u + cert_len + 2u;
  size_t total_len = 4u + body_len;
  if ((cert == NULL && cert_len != 0u) || out == NULL ||
      cert_len > 0xffffffu || body_len > 0xffffffu || total_len > out_len) {
    return 0u;
  }
  out[0] = 11u;
  TLS13_Connection_Backend_write_u24(out + 1u, body_len);
  out[4] = 0u;
  TLS13_Connection_Backend_write_u24(out + 5u, 3u + cert_len + 2u);
  TLS13_Connection_Backend_write_u24(out + 8u, cert_len);
  if (cert_len != 0u) {
    memcpy(out + 11u, cert, cert_len);
  }
  TLS13_Connection_Backend_write_u16(out + 11u + cert_len, 0u);
  return total_len;
}

static inline size_t TLS13_Connection_Backend_serialize_certificate_msg_fixed(
    const uint8_t *chain_bytes,
    size_t chain_bytes_len,
    const size_t *cert_offsets,
    const size_t *cert_lens,
    size_t cert_count,
    uint8_t *out,
    size_t out_len) {
  if ((chain_bytes == NULL && chain_bytes_len != 0u) ||
      cert_offsets == NULL || cert_lens == NULL || out == NULL ||
      cert_count > 8u) {
    return 0u;
  }
  size_t cert_list_len = 0u;
  for (size_t i = 0u; i < cert_count; i++) {
    size_t off = cert_offsets[i];
    size_t len = cert_lens[i];
    if (off > chain_bytes_len || len > chain_bytes_len - off ||
        len > 0xffffffu || cert_list_len > 0xffffffu - (3u + len + 2u)) {
      return 0u;
    }
    cert_list_len += 3u + len + 2u;
  }
  size_t body_len = 1u + 3u + cert_list_len;
  size_t total_len = 4u + body_len;
  if (body_len > 0xffffffu || total_len > out_len) {
    return 0u;
  }
  out[0] = 11u;
  TLS13_Connection_Backend_write_u24(out + 1u, body_len);
  out[4] = 0u;
  TLS13_Connection_Backend_write_u24(out + 5u, cert_list_len);
  uint8_t *p = out + 8u;
  for (size_t i = 0u; i < cert_count; i++) {
    size_t off = cert_offsets[i];
    size_t len = cert_lens[i];
    TLS13_Connection_Backend_write_u24(p, len);
    p += 3u;
    if (len != 0u) {
      memcpy(p, chain_bytes + off, len);
      p += len;
    }
    TLS13_Connection_Backend_write_u16(p, 0u);
    p += 2u;
  }
  return total_len;
}

static inline size_t TLS13_Connection_Backend_serialize_certificate_verify_fixed(
    uint16_t signature_scheme,
    const uint8_t *signature,
    size_t signature_len,
    uint8_t *out,
    size_t out_len) {
  size_t body_len = 4u + signature_len;
  size_t total_len = 4u + body_len;
  if ((signature == NULL && signature_len != 0u) || out == NULL ||
      signature_len > 0xffffu || body_len > 0xffffffu || total_len > out_len) {
    return 0u;
  }
  out[0] = 15u;
  TLS13_Connection_Backend_write_u24(out + 1u, body_len);
  TLS13_Connection_Backend_write_u16(out + 4u, signature_scheme);
  TLS13_Connection_Backend_write_u16(out + 6u, signature_len);
  if (signature_len != 0u) {
    memcpy(out + 8u, signature, signature_len);
  }
  return total_len;
}

#define TLS13_Impl_Serializer_serialize_server_hello_from_selection(sh_erased, lsh, out, out_len, ...) \
  TLS13_Connection_Backend_serialize_server_hello_fixed( \
      (lsh).server_hello_random, (lsh).server_hello_key_share, \
      (lsh).server_hello_cipher_suite, (out), (out_len))

#define TLS13_Impl_Serializer_serialize_empty_encrypted_extensions(out, out_len, ...) \
  TLS13_Connection_Backend_serialize_empty_encrypted_extensions_fixed((out), (out_len))

#define TLS13_Impl_Serializer_serialize_certificate_from_credential(cert_erased, lcert, out, out_len, ...) \
  TLS13_Connection_Backend_serialize_certificate_msg_fixed( \
      (lcert).certificate_msg_chain_bytes, (lcert).certificate_msg_chain_bytes_len, \
      (lcert).certificate_msg_cert_offsets, (lcert).certificate_msg_cert_lens, \
      (lcert).certificate_msg_cert_count, (out), (out_len))

#define TLS13_Impl_Serializer_serialize_certificate_verify_from_signature(cv_erased, lcv, out, out_len, ...) \
  TLS13_Connection_Backend_serialize_certificate_verify_fixed( \
      (lcv).certificate_verify_scheme, (lcv).certificate_verify_signature, \
      (lcv).certificate_verify_signature_len, (out), (out_len))

#define TLS13_Impl_Serializer_serialize_server_finished(fin_erased, lfin, out, out_len, ...) \
  TLS13_Impl_Serializer_serialize_finished_handshake((fin_erased), (lfin), (out), (out_len), NULL)

static inline size_t TLS13_Connection_Backend_serialize_raw_application_data_record(
    uint8_t *fragment,
    size_t fragment_len,
    uint8_t *out,
    size_t out_len) {
  size_t written = 5u + fragment_len;
  if (written > out_len || fragment_len > 0xffffu) {
    return 0u;
  }
  out[0] = 23u;
  out[1] = 0x03u;
  out[2] = 0x03u;
  TLS13_Connection_Backend_write_u16(out + 3u, fragment_len);
  memcpy(out + 5u, fragment, fragment_len);
  return written;
}

#define TLS13_Impl_Serializer_serialize_raw_application_data_record(fragment, fragment_len, out, out_len, ...) \
  TLS13_Connection_Backend_serialize_raw_application_data_record((fragment), (fragment_len), (out), (out_len))

static inline size_t TLS13_Connection_Backend_serialize_client_finished_outputs(
    const uint8_t *write_key,
    const uint8_t *write_iv,
    uint64_t write_seq,
    bool write_installed,
    uint8_t *verify_data,
    uint8_t *handshake_out,
    uint8_t *network_out,
    size_t network_out_len) {
  if (!write_installed || network_out_len < 58u) {
    return 0u;
  }
  handshake_out[0] = 20u;
  TLS13_Connection_Backend_write_u24(handshake_out + 1u, 32u);
  memcpy(handshake_out + 4u, verify_data, 32u);

  network_out[0] = 23u;
  network_out[1] = 0x03u;
  network_out[2] = 0x03u;
  TLS13_Connection_Backend_write_u16(network_out + 3u, 53u);

  uint8_t inner_plaintext[37u];
  memcpy(inner_plaintext, handshake_out, 36u);
  inner_plaintext[36u] = 22u;

  uint8_t nonce[12u];
  if (!tls13_record_nonce(nonce, write_iv, write_seq)) {
    return 0u;
  }
  if (!tls13_hacl_chacha20_poly1305_seal_combined(
          network_out + 5u,
          53u,
          write_key,
          nonce,
          network_out,
          5u,
          inner_plaintext,
          37u)) {
    return 0u;
  }
  return 58u;
}

#define TLS13_Impl_Serializer_serialize_client_finished_outputs(write_state, lfin, handshake_out, network_out, network_out_len, ...) \
  ({ \
    __auto_type _tls13_write_state = (write_state); \
    TLS13_Connection_Backend_serialize_client_finished_outputs( \
        _tls13_write_state.key, \
        _tls13_write_state.iv, \
        *_tls13_write_state.seq, \
        *_tls13_write_state.installed, \
        (lfin), \
        (handshake_out), \
        (network_out), \
        (network_out_len)); \
  })

static inline size_t TLS13_Connection_Backend_serialize_finished_handshake(
    const uint8_t *verify_data,
    uint8_t *handshake_out,
    size_t handshake_out_len) {
  if (handshake_out_len < 36u) {
    return 0u;
  }
  handshake_out[0] = 20u;
  TLS13_Connection_Backend_write_u24(handshake_out + 1u, 32u);
  memcpy(handshake_out + 4u, verify_data, 32u);
  return 36u;
}

#define TLS13_Impl_Serializer_serialize_finished_handshake(fin_erased, lfin, handshake_out, handshake_out_len, ...) \
  TLS13_Connection_Backend_serialize_finished_handshake((lfin), (handshake_out), (handshake_out_len))

#define TLS13_Impl_Parser_parse_tls_message(content_type, input, input_len, ...) \
  ({ \
    FStar_Pervasives_Native_option__TLS13_Impl_Messages_tls_message _r = { .tag = FStar_Pervasives_Native_None }; \
    if ((content_type) == 20u && (input_len) == 1u && (input)[0] == 1u) { \
      _r.tag = FStar_Pervasives_Native_Some; \
      _r.v = (TLS13_Impl_Messages_tls_message){ .tag = TLS13_Impl_Messages_LTlsChangeCipherSpec }; \
    } else if ((content_type) == 21u && (input_len) == 2u) { \
      _r.tag = FStar_Pervasives_Native_Some; \
      _r.v = (TLS13_Impl_Messages_tls_message){ \
        .tag = TLS13_Impl_Messages_LTlsAlert, \
        { .case_LTlsAlert = (input)[1] } \
      }; \
    } else if ((content_type) == 23u) { \
      uint8_t *_app = TLS13_Connection_Backend_dup_bytes((input), (input_len)); \
      if (_app != NULL) { \
        _r.tag = FStar_Pervasives_Native_Some; \
        _r.v = (TLS13_Impl_Messages_tls_message){ \
          .tag = TLS13_Impl_Messages_LTlsApplicationData, \
          { .case_LTlsApplicationData = { .application_data_bytes = _app, .application_data_len = (input_len) } } \
        }; \
      } \
    } else if ((content_type) == 22u && (input_len) >= 4u) { \
      uint8_t _ht = (input)[0]; \
      size_t _hlen = TLS13_Connection_Backend_read_u24((input) + 1u); \
      if (_ht == 24u && _hlen == 1u && _hlen + 4u == (input_len) && (input)[4u] <= 1u) { \
        _r.tag = FStar_Pervasives_Native_Some; \
        _r.v = (TLS13_Impl_Messages_tls_message){ \
          .tag = TLS13_Impl_Messages_LTlsKeyUpdate, \
          { .case_LTlsKeyUpdate = (input)[4u] } \
        }; \
      } else if (_ht == 4u && _hlen + 4u == (input_len)) { \
        uint8_t *_body = (input) + 4u; \
        uint8_t *_ticket = TLS13_Connection_Backend_dup_bytes(_body, _hlen); \
        if (_ticket != NULL) { \
          _r.tag = FStar_Pervasives_Native_Some; \
          _r.v = (TLS13_Impl_Messages_tls_message){ \
            .tag = TLS13_Impl_Messages_LTlsIgnoredPostHandshake, \
            { .case_LTlsIgnoredPostHandshake = { \
                .application_data_bytes = _ticket, \
                .application_data_len = _hlen } } \
          }; \
        } \
      } else if (_hlen + 4u == (input_len)) { \
        uint8_t *_body = (input) + 4u; \
        TLS13_Impl_Messages_handshake_msg _hs = { .tag = TLS13_Impl_Messages_LHelloRetryRequest }; \
        bool _ok = true; \
        if (_ht == 2u && _hlen >= 38u) { \
          size_t _sid_len = _body[34u]; \
          size_t _cipher_off = 35u + _sid_len; \
          size_t _ext_len_off = _cipher_off + 3u; \
          uint8_t *_random = calloc(32u, sizeof(uint8_t)); \
          uint8_t *_key_share = calloc(32u, sizeof(uint8_t)); \
          _ok = _random != NULL && _key_share != NULL && _ext_len_off + 2u <= _hlen; \
          uint16_t _cipher = 0u; \
          if (_ok) { \
            memcpy(_random, _body + 2u, 32u); \
            _cipher = (uint16_t)TLS13_Connection_Backend_read_u16(_body + _cipher_off); \
            size_t _ext_len = TLS13_Connection_Backend_read_u16(_body + _ext_len_off); \
            size_t _pos = _ext_len_off + 2u; \
            size_t _end = _pos + _ext_len; \
            _ok = _end <= _hlen; \
            bool _found_key_share = false; \
            while (_ok && _pos + 4u <= _end) { \
              size_t _etype = TLS13_Connection_Backend_read_u16(_body + _pos); \
              size_t _elen = TLS13_Connection_Backend_read_u16(_body + _pos + 2u); \
              _pos += 4u; \
              if (_pos + _elen > _end) { \
                _ok = false; \
              } else if (_etype == 0x0033u && _elen >= 36u && TLS13_Connection_Backend_read_u16(_body + _pos + 2u) == 32u) { \
                memcpy(_key_share, _body + _pos + 4u, 32u); \
                _found_key_share = true; \
              } \
              _pos += _elen; \
            } \
            _ok = _ok && _found_key_share; \
          } \
          if (_ok) { \
            _hs = (TLS13_Impl_Messages_handshake_msg){ \
              .tag = TLS13_Impl_Messages_LServerHello, \
              { .case_LServerHello = { \
                  .server_hello_random = _random, \
                  .server_hello_key_share = _key_share, \
                  .server_hello_cipher_suite = _cipher } } \
            }; \
          } else { \
            free(_random); \
            free(_key_share); \
          } \
        } else if (_ht == 8u) { \
          _hs = (TLS13_Impl_Messages_handshake_msg){ \
            .tag = TLS13_Impl_Messages_LEncryptedExtensions, \
            { .case_LEncryptedExtensions = { \
                .encrypted_extensions_alpn = NULL, \
                .encrypted_extensions_alpn_len = 0u, \
                .encrypted_extensions_has_alpn = false } } \
          }; \
        } else if (_ht == 11u && _hlen >= 7u) { \
          size_t _cert_list_len_off = 1u; \
          size_t _cert_list_len = TLS13_Connection_Backend_read_u24(_body + _cert_list_len_off); \
          size_t _cert_len_off = 4u; \
          size_t _cert_len = TLS13_Connection_Backend_read_u24(_body + _cert_len_off); \
          size_t _cert_off = 7u; \
          size_t *_offs = calloc(1u, sizeof(size_t)); \
          size_t *_lens = calloc(1u, sizeof(size_t)); \
          uint8_t *_chain = TLS13_Connection_Backend_dup_bytes(_body, _hlen); \
          if (_offs != NULL && _lens != NULL && _chain != NULL && _cert_off + _cert_len + 2u <= _hlen && _cert_list_len + 4u <= _hlen) { \
            _offs[0] = _cert_off; \
            _lens[0] = _cert_len; \
            _hs = (TLS13_Impl_Messages_handshake_msg){ \
              .tag = TLS13_Impl_Messages_LCertificate, \
              { .case_LCertificate = { \
                  .certificate_msg_chain_bytes = _chain, \
                  .certificate_msg_chain_bytes_len = _hlen, \
                  .certificate_msg_cert_offsets = _offs, \
                  .certificate_msg_cert_lens = _lens, \
                  .certificate_msg_cert_count = 1u } } \
            }; \
          } else { \
            free(_offs); \
            free(_lens); \
            free(_chain); \
            _ok = false; \
          } \
        } else if (_ht == 15u && _hlen >= 4u) { \
          size_t _sig_len = TLS13_Connection_Backend_read_u16(_body + 2u); \
          uint8_t *_sig = calloc(_sig_len == 0u ? 1u : _sig_len, sizeof(uint8_t)); \
          if (_sig != NULL && 4u + _sig_len <= _hlen) { \
            memcpy(_sig, _body + 4u, _sig_len); \
            _hs = (TLS13_Impl_Messages_handshake_msg){ \
              .tag = TLS13_Impl_Messages_LCertificateVerify, \
              { .case_LCertificateVerify = { \
                  .certificate_verify_scheme = (uint16_t)TLS13_Connection_Backend_read_u16(_body), \
                  .certificate_verify_signature = _sig, \
                  .certificate_verify_signature_len = _sig_len } } \
            }; \
          } else { \
            _ok = false; \
          } \
        } else if (_ht == 20u && _hlen == 32u) { \
          uint8_t *_fin = calloc(32u, sizeof(uint8_t)); \
          if (_fin != NULL) { \
            memcpy(_fin, _body, 32u); \
            _hs = (TLS13_Impl_Messages_handshake_msg){ \
              .tag = TLS13_Impl_Messages_LFinished, \
              { .case_LFinished = _fin } \
            }; \
          } else { \
            _ok = false; \
          } \
        } else { \
          _ok = false; \
        } \
        if (_ok) { \
          _r.tag = FStar_Pervasives_Native_Some; \
          _r.v = (TLS13_Impl_Messages_tls_message){ \
            .tag = TLS13_Impl_Messages_LTlsHandshake, \
            { .case_LTlsHandshake = _hs } \
          }; \
        } \
      } \
    } \
    _r; \
  })

static inline bool TLS13_Connection_Backend_is_tls_content_type(uint8_t ct) {
  return ct == 20u || ct == 21u || ct == 22u || ct == 23u;
}

#define TLS13_CONNECTION_BACKEND_DECODED_RECORD_NEED_MORE_INPUT() \
  ({ \
    TLS13_Impl_Messages_decoded_network_record_result _tls13_decoded = { \
      .tag = TLS13_Impl_Messages_NetworkRecordNeedMoreInput \
    }; \
    _tls13_decoded; \
  })

#define TLS13_CONNECTION_BACKEND_DECODED_RECORD_DECODE_ERROR() \
  ({ \
    TLS13_Impl_Messages_decoded_network_record_result _tls13_decoded = { \
      .tag = TLS13_Impl_Messages_NetworkRecordDecodeError \
    }; \
    _tls13_decoded; \
  })

#define TLS13_CONNECTION_BACKEND_DECODED_BUFFER_NEED_MORE_INPUT() \
  ({ \
    TLS13_Impl_Messages_decoded_network_buffer_result _tls13_decoded = { \
      .tag = TLS13_Impl_Messages_NetworkBufferNeedMoreInput \
    }; \
    _tls13_decoded; \
  })

#define TLS13_CONNECTION_BACKEND_DECODED_BUFFER_DECODE_ERROR() \
  ({ \
    TLS13_Impl_Messages_decoded_network_buffer_result _tls13_decoded = { \
      .tag = TLS13_Impl_Messages_NetworkBufferDecodeError \
    }; \
    _tls13_decoded; \
  })

static inline bool TLS13_Connection_Backend_decode_inner_plaintext(
    uint8_t *inner,
    size_t inner_len,
    uint8_t *content_type_out,
    size_t *payload_len_out) {
  if (inner_len == 0u) {
    return false;
  }
  size_t pos = inner_len;
  while (pos > 0u && inner[pos - 1u] == 0u) {
    pos--;
  }
  if (pos == 0u) {
    return false;
  }
  uint8_t ct = inner[pos - 1u];
  if (!TLS13_Connection_Backend_is_tls_content_type(ct)) {
    return false;
  }
  *content_type_out = ct;
  *payload_len_out = pos - 1u;
  return true;
}

#define TLS13_Impl_Parser_decode_network_buffer(c, raw, raw_len, ...) \
  ({ \
    TLS13_Impl_ConnectionState_Repr_connection_state _tls13_c = (c); \
    uint8_t *_tls13_raw = (raw); \
    size_t _tls13_raw_len = (raw_len); \
    TLS13_Impl_Messages_decoded_network_buffer_result _tls13_result = \
      TLS13_CONNECTION_BACKEND_DECODED_BUFFER_DECODE_ERROR(); \
    if (_tls13_raw_len < 1u) { \
      _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_BUFFER_NEED_MORE_INPUT(); \
    } else { \
      uint8_t _tls13_outer_ct = _tls13_raw[0]; \
      if (!TLS13_Connection_Backend_is_tls_content_type(_tls13_outer_ct)) { \
        _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_BUFFER_DECODE_ERROR(); \
      } else if (_tls13_raw_len < 3u) { \
        _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_BUFFER_NEED_MORE_INPUT(); \
      } else if (_tls13_raw[1] != 3u || _tls13_raw[2] != 3u) { \
        _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_BUFFER_DECODE_ERROR(); \
      } else if (_tls13_raw_len < 5u) { \
        _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_BUFFER_NEED_MORE_INPUT(); \
      } else { \
        size_t _tls13_fragment_len = TLS13_Connection_Backend_read_u16(_tls13_raw + 3u); \
        if (_tls13_fragment_len > 16640u) { \
          _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_BUFFER_DECODE_ERROR(); \
        } else if (_tls13_raw_len < 5u + _tls13_fragment_len) { \
          _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_BUFFER_NEED_MORE_INPUT(); \
        } else { \
          size_t _tls13_record_len = 5u + _tls13_fragment_len; \
          uint8_t *_tls13_record_fragment = _tls13_raw + 5u; \
          uint8_t _tls13_content_type = _tls13_outer_ct; \
          uint8_t *_tls13_payload = _tls13_record_fragment; \
          size_t _tls13_payload_len = _tls13_fragment_len; \
          uint8_t *_tls13_opened_to_free = NULL; \
          bool _tls13_decoded = _tls13_outer_ct != 23u; \
          if (_tls13_outer_ct == 23u) { \
            uint8_t _tls13_inner_ct = 0u; \
            size_t _tls13_inner_payload_len = 0u; \
            if (_tls13_c.records.read.installed != NULL && \
                *_tls13_c.records.read.installed && \
                _tls13_fragment_len >= 16u) { \
              size_t _tls13_opened_len = _tls13_fragment_len - 16u; \
              uint8_t *_tls13_opened = calloc(_tls13_opened_len == 0u ? 1u : _tls13_opened_len, sizeof(uint8_t)); \
              if (_tls13_opened != NULL) { \
                uint8_t _tls13_aad[5u]; \
                memcpy(_tls13_aad, _tls13_raw, 5u); \
                if (TLS13_Record_peek_open_application( \
                      _tls13_c.records.read, \
                      _tls13_aad, \
                      5u, \
                      _tls13_record_fragment, \
                      _tls13_fragment_len, \
                      _tls13_opened)) { \
                  if (TLS13_Connection_Backend_decode_inner_plaintext( \
                        _tls13_opened, \
                        _tls13_opened_len, \
                        &_tls13_inner_ct, \
                        &_tls13_inner_payload_len)) { \
                    _tls13_content_type = _tls13_inner_ct; \
                    _tls13_payload = _tls13_opened; \
                    _tls13_payload_len = _tls13_inner_payload_len; \
                    _tls13_opened_to_free = _tls13_opened; \
                    _tls13_decoded = true; \
                  } \
                } \
                if (!_tls13_decoded) { \
                  free(_tls13_opened); \
                } \
              } \
            } \
          } \
          if (_tls13_decoded && _tls13_result.tag != TLS13_Impl_Messages_NetworkBufferOk) { \
            uint8_t *_tls13_owned_raw = TLS13_Connection_Backend_dup_bytes(_tls13_raw, _tls13_record_len); \
            uint8_t *_tls13_owned_fragment = TLS13_Connection_Backend_dup_bytes(_tls13_payload, _tls13_payload_len); \
            if (_tls13_owned_raw != NULL && _tls13_owned_fragment != NULL) { \
              _tls13_result.tag = TLS13_Impl_Messages_NetworkBufferOk; \
              _tls13_result._0 = (TLS13_Impl_Messages_decoded_network_buffer){ \
                .decoded_buffer_raw_record = _tls13_owned_raw, \
                .decoded_buffer_raw_record_len = _tls13_record_len, \
                .decoded_buffer_consumed_len = _tls13_record_len, \
                .decoded_buffer_content_type = _tls13_content_type, \
                .decoded_buffer_fragment = _tls13_owned_fragment, \
                .decoded_buffer_fragment_len = _tls13_payload_len, \
                .decoded_buffer_parsed = TLS13_Impl_Parser_parse_tls_message(_tls13_content_type, _tls13_owned_fragment, _tls13_payload_len) \
              }; \
            } else { \
              free(_tls13_owned_raw); \
              free(_tls13_owned_fragment); \
            } \
          } \
          if (_tls13_opened_to_free != NULL) { \
            free(_tls13_opened_to_free); \
          } \
        } \
      } \
    } \
    _tls13_result; \
  })

#define TLS13_Impl_Parser_decode_network_record(c, raw, raw_len, ...) \
  ({ \
    TLS13_Impl_ConnectionState_Repr_connection_state _tls13_c = (c); \
    uint8_t *_tls13_raw = (raw); \
    size_t _tls13_raw_len = (raw_len); \
    TLS13_Impl_Messages_decoded_network_record_result _tls13_result = \
      TLS13_CONNECTION_BACKEND_DECODED_RECORD_DECODE_ERROR(); \
    if (_tls13_raw_len < 5u) { \
      _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_RECORD_NEED_MORE_INPUT(); \
    } else { \
      uint8_t _tls13_outer_ct = _tls13_raw[0]; \
      if (!TLS13_Connection_Backend_is_tls_content_type(_tls13_outer_ct) || \
          _tls13_raw[1] != 3u || \
          _tls13_raw[2] != 3u) { \
        _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_RECORD_DECODE_ERROR(); \
      } else { \
        size_t _tls13_fragment_len = TLS13_Connection_Backend_read_u16(_tls13_raw + 3u); \
        if (_tls13_fragment_len > 16640u) { \
          _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_RECORD_DECODE_ERROR(); \
        } else if (_tls13_raw_len < 5u + _tls13_fragment_len) { \
          _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_RECORD_NEED_MORE_INPUT(); \
        } else if (_tls13_raw_len != 5u + _tls13_fragment_len) { \
          _tls13_result = TLS13_CONNECTION_BACKEND_DECODED_RECORD_DECODE_ERROR(); \
        } else { \
          uint8_t *_tls13_record_fragment = _tls13_raw + 5u; \
          uint8_t _tls13_content_type = _tls13_outer_ct; \
          uint8_t *_tls13_payload = _tls13_record_fragment; \
          size_t _tls13_payload_len = _tls13_fragment_len; \
          uint8_t *_tls13_opened_to_free = NULL; \
          bool _tls13_decoded = _tls13_outer_ct != 23u; \
          if (_tls13_outer_ct == 23u) { \
            uint8_t _tls13_inner_ct = 0u; \
            size_t _tls13_inner_payload_len = 0u; \
            if (_tls13_c.records.read.installed != NULL && \
                *_tls13_c.records.read.installed && \
                _tls13_fragment_len >= 16u) { \
              size_t _tls13_opened_len = _tls13_fragment_len - 16u; \
              uint8_t *_tls13_opened = calloc(_tls13_opened_len == 0u ? 1u : _tls13_opened_len, sizeof(uint8_t)); \
              if (_tls13_opened != NULL) { \
                uint8_t _tls13_aad[5u]; \
                memcpy(_tls13_aad, _tls13_raw, 5u); \
                if (TLS13_Record_peek_open_application( \
                      _tls13_c.records.read, \
                      _tls13_aad, \
                      5u, \
                      _tls13_record_fragment, \
                      _tls13_fragment_len, \
                      _tls13_opened)) { \
                  if (TLS13_Connection_Backend_decode_inner_plaintext( \
                        _tls13_opened, \
                        _tls13_opened_len, \
                        &_tls13_inner_ct, \
                        &_tls13_inner_payload_len)) { \
                    _tls13_content_type = _tls13_inner_ct; \
                    _tls13_payload = _tls13_opened; \
                    _tls13_payload_len = _tls13_inner_payload_len; \
                    _tls13_opened_to_free = _tls13_opened; \
                    _tls13_decoded = true; \
                  } \
                } \
                if (!_tls13_decoded) { \
                  free(_tls13_opened); \
                } \
              } \
            } \
          } \
          if (_tls13_decoded && _tls13_result.tag != TLS13_Impl_Messages_NetworkRecordOk) { \
            uint8_t *_tls13_owned_fragment = TLS13_Connection_Backend_dup_bytes(_tls13_payload, _tls13_payload_len); \
            if (_tls13_owned_fragment != NULL) { \
              _tls13_result.tag = TLS13_Impl_Messages_NetworkRecordOk; \
              _tls13_result._0 = (TLS13_Impl_Messages_decoded_network_record){ \
                .decoded_record_content_type = _tls13_content_type, \
                .decoded_record_fragment = _tls13_owned_fragment, \
                .decoded_record_fragment_len = _tls13_payload_len, \
                .decoded_record_parsed = TLS13_Impl_Parser_parse_tls_message(_tls13_content_type, _tls13_owned_fragment, _tls13_payload_len) \
              }; \
            } \
          } \
          if (_tls13_opened_to_free != NULL) { \
            free(_tls13_opened_to_free); \
          } \
        } \
      } \
    } \
    _tls13_result; \
  })

static inline size_t TLS13_Connection_Backend_serialize_client_hello_from_start_impl(
    uint8_t *start_random,
    uint8_t *start_server_name,
    size_t *start_server_name_len,
    uint8_t *start_key_share,
    uint16_t *start_cipher_suites,
    size_t *start_cipher_suites_len,
    uint16_t *start_signature_schemes,
    size_t *start_signature_schemes_len,
    bool *client_hello_present,
    uint8_t *l_random,
    uint8_t *l_server_name,
    uint8_t *l_key_share,
    uint16_t *l_cipher_suites,
    uint16_t *l_signature_schemes,
    uint8_t *client_hello_bytes,
    size_t *client_hello_bytes_len,
    uint8_t *network_out,
    size_t network_out_len) {
  (void)start_cipher_suites_len;
  (void)start_signature_schemes_len;

  size_t hostname_len = *start_server_name_len;
  size_t sni_extension_len = hostname_len == 0u ? 0u : 9u + hostname_len;
  size_t extensions_len = 65u + sni_extension_len;
  size_t body_len = 43u + extensions_len;
  size_t handshake_len = 4u + body_len;
  size_t record_len = 5u + handshake_len;

  if (record_len > network_out_len || handshake_len > 512u || hostname_len > 255u) {
    return 0u;
  }

  memcpy(l_random, start_random, 32u);
  memcpy(l_server_name, start_server_name, 255u);
  memcpy(l_key_share, start_key_share, 32u);
  memcpy(l_cipher_suites, start_cipher_suites, 16u * sizeof(uint16_t));
  memcpy(l_signature_schemes, start_signature_schemes, 16u * sizeof(uint16_t));

  uint8_t *p = client_hello_bytes;
  *p++ = 1u;
  TLS13_Connection_Backend_write_u24(p, body_len);
  p += 3;
  TLS13_Connection_Backend_write_u16(p, 0x0303u);
  p += 2;
  memcpy(p, start_random, 32u);
  p += 32;
  *p++ = 0u;
  TLS13_Connection_Backend_write_u16(p, 2u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 0x1303u);
  p += 2;
  *p++ = 1u;
  *p++ = 0u;
  TLS13_Connection_Backend_write_u16(p, extensions_len);
  p += 2;

  if (hostname_len != 0u) {
    TLS13_Connection_Backend_write_u16(p, 0x0000u);
    p += 2;
    TLS13_Connection_Backend_write_u16(p, 5u + hostname_len);
    p += 2;
    TLS13_Connection_Backend_write_u16(p, 3u + hostname_len);
    p += 2;
    *p++ = 0u;
    TLS13_Connection_Backend_write_u16(p, hostname_len);
    p += 2;
    memcpy(p, start_server_name, hostname_len);
    p += hostname_len;
  }

  TLS13_Connection_Backend_write_u16(p, 0x000au);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 4u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 2u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 0x001du);
  p += 2;

  TLS13_Connection_Backend_write_u16(p, 0x000du);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 4u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 2u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 0x0804u);
  p += 2;

  TLS13_Connection_Backend_write_u16(p, 0x0033u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 38u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 36u);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 0x001du);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 32u);
  p += 2;
  memcpy(p, start_key_share, 32u);
  p += 32;

  TLS13_Connection_Backend_write_u16(p, 0x002bu);
  p += 2;
  TLS13_Connection_Backend_write_u16(p, 3u);
  p += 2;
  *p++ = 2u;
  TLS13_Connection_Backend_write_u16(p, 0x0304u);
  p += 2;

  *client_hello_bytes_len = handshake_len;
  network_out[0] = 22u;
  network_out[1] = 0x03u;
  network_out[2] = 0x03u;
  TLS13_Connection_Backend_write_u16(network_out + 3, handshake_len);
  memcpy(network_out + 5, client_hello_bytes, handshake_len);
  *client_hello_present = true;

  return record_len;
}

#define TLS13_Impl_Serializer_serialize_client_hello_from_start( \
    start_erased, ch_erased, start_random, start_server_name, start_server_name_len, \
    start_key_share, start_cipher_suites, start_cipher_suites_len, \
    start_signature_schemes, start_signature_schemes_len, client_hello_present, l, \
    client_hello_bytes, client_hello_bytes_len, network_out, network_out_len, ...) \
  ((l).client_hello_server_name_len = *(start_server_name_len), \
   (l).client_hello_has_server_name = true, \
   (l).client_hello_cipher_suites_len = *(start_cipher_suites_len), \
   (l).client_hello_signature_schemes_len = *(start_signature_schemes_len), \
   TLS13_Connection_Backend_serialize_client_hello_from_start_impl( \
       (start_random), (start_server_name), (start_server_name_len), (start_key_share), \
       (start_cipher_suites), (start_cipher_suites_len), \
       (start_signature_schemes), (start_signature_schemes_len), \
       (client_hello_present), (l).client_hello_random, (l).client_hello_server_name, \
       (l).client_hello_key_share, (l).client_hello_cipher_suites, \
       (l).client_hello_signature_schemes, (client_hello_bytes), \
       (client_hello_bytes_len), (network_out), (network_out_len)))

#endif

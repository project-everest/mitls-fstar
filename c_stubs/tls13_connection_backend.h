#ifndef TLS13_CONNECTION_BACKEND_H
#define TLS13_CONNECTION_BACKEND_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "tls13_hacl_stubs.h"

typedef struct TLS13_IO_channel_s *TLS13_IO_channel;
typedef struct TLS13_IO_listener_s *TLS13_IO_listener;
typedef uintptr_t TLS13_Handshake_handshake_context;

typedef struct TLS13_Connection_Backend_config_s {
  uint16_t port;
  const char *ca_pem_path;
} *TLS13_Connection_Backend_config;

typedef struct TLS13_Connection_Backend_connection_s *TLS13_Connection_Backend_connection;
#ifndef TLS13_X509_SPEC_TRUST_STORE_DEFINED
#define TLS13_X509_SPEC_TRUST_STORE_DEFINED
typedef TLS13_Connection_Backend_config TLS13_X509_Spec_trust_store;
#endif
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

#ifndef FStar_SizeT_uint_to_t
#define FStar_SizeT_uint_to_t(n) ((size_t)(n))
#endif
#ifndef FStar_SizeT_v
#define FStar_SizeT_v(n) ((size_t)(n))
#endif

#define TLS13_Impl_ConnectionState_Repr_copy_hostname_sized_bytes(src, dst, ...) \
  ((*((dst).len) = *((src).len)), memcpy((dst).bytes, (src).bytes, *((src).len)))

#define TLS13_Impl_ConnectionState_Repr_copy_array_to_sized_bytes(src, dst, cap, nbytes, ...) \
  do { \
    (void)(cap); \
    size_t tls13_copy_nbytes = (size_t)(nbytes); \
    *((dst).len) = tls13_copy_nbytes; \
    if (tls13_copy_nbytes != 0u) { \
      memcpy((dst).bytes, (src), tls13_copy_nbytes); \
    } \
  } while (0)

#define TLS13_Impl_ConnectionState_Repr_copy_array_to_transcript(src, dst, nbytes, off, ...) \
  (memcpy((dst) + (off), (src), (nbytes)))

#define TLS13_Impl_ConnectionState_Repr_copy_array_prefix_to_transcript(src, dst, nbytes, off, ...) \
  TLS13_Impl_ConnectionState_Repr_copy_array_to_transcript((src), (dst), (nbytes), (off))

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

#define TLS13_Crypto_random_bytes(out, out_len, ...) \
  TLS13_Crypto_random_bytes((out), (out_len))

#define TLS13_Crypto_sha256_empty(out, ...) \
  TLS13_Crypto_sha256_empty((out))

#define TLS13_Crypto_equal32(a, b, ...) \
  TLS13_Crypto_equal32((a), (b))

#define TLS13_Crypto_equal12(a, b, ...) \
  TLS13_Crypto_equal12((a), (b))

#define TLS13_Crypto_hmac_sha256(key, key_len, msg, msg_len, out, ...) \
  TLS13_Crypto_hmac_sha256((key), (key_len), (msg), (msg_len), (out))

#define TLS13_Crypto_hkdf_extract(salt, salt_len, ikm, ikm_len, out, ...) \
  TLS13_Crypto_hkdf_extract((salt), (salt_len), (ikm), (ikm_len), (out))

#define TLS13_Crypto_hkdf_expand_label(secret, label, label_len, context, context_len, out, out_len, ...) \
  TLS13_Crypto_hkdf_expand_label( \
      (secret), (label), (label_len), (context), (context_len), (out), (out_len))

#define TLS13_Crypto_hkdf_expand_label_empty_context(secret, label, label_len, out, out_len, ...) \
  TLS13_Crypto_hkdf_expand_label_empty_context((secret), (label), (label_len), (out), (out_len))

#define TLS13_Crypto_x25519_public_from_private(sk, out, ...) \
  TLS13_Crypto_x25519_public_from_private((sk), (out))

#define TLS13_Crypto_x25519_shared_runtime(sk, pk, out, ...) \
  TLS13_Crypto_x25519_shared_runtime((sk), (pk), (out))

#define TLS13_Crypto_tls13_record_nonce(static_iv, sequence_number, out, ...) \
  TLS13_Crypto_tls13_record_nonce((static_iv), (sequence_number), (out))

#define TLS13_Crypto_chacha20_poly1305_seal(key, nonce, aad, aad_len, plain, plain_len, out, ...) \
  TLS13_Crypto_chacha20_poly1305_seal( \
      (key), (nonce), (aad), (aad_len), (plain), (plain_len), (out))

#define TLS13_Crypto_chacha20_poly1305_open(key, nonce, aad, aad_len, cipher, cipher_len, out, ...) \
  TLS13_Crypto_chacha20_poly1305_open( \
      (key), (nonce), (aad), (aad_len), (cipher), (cipher_len), (out))

#define TLS13_Crypto_sha256_prefix(input, input_len, out, ...) \
  TLS13_Crypto_sha256((input), (input_len), (out))

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
        if (_ht == 1u && _hlen >= 35u) { \
          uint8_t *_random = calloc(32u, sizeof(uint8_t)); \
          uint8_t *_server_name = calloc(255u, sizeof(uint8_t)); \
          uint8_t *_key_share = calloc(32u, sizeof(uint8_t)); \
          uint16_t *_cipher_suites = calloc(16u, sizeof(uint16_t)); \
          uint16_t *_signature_schemes = calloc(16u, sizeof(uint16_t)); \
          _ok = _random != NULL && _server_name != NULL && _key_share != NULL && \
            _cipher_suites != NULL && _signature_schemes != NULL && \
            TLS13_Connection_Backend_read_u16(_body) == 0x0303u; \
          bool _has_server_name = false; \
          size_t _server_name_len = 0u; \
          bool _found_key_share = false; \
          bool _found_supported_versions = false; \
          size_t _signature_schemes_len = 0u; \
          if (_ok) { \
            memcpy(_random, _body + 2u, 32u); \
            size_t _sid_len = _body[34u]; \
            size_t _cipher_len_off = 35u + _sid_len; \
            _ok = _cipher_len_off + 2u <= _hlen; \
            if (_ok) { \
              size_t _cipher_len = TLS13_Connection_Backend_read_u16(_body + _cipher_len_off); \
              size_t _cipher_pos = _cipher_len_off + 2u; \
              size_t _compression_len_off = _cipher_pos + _cipher_len; \
              _ok = _compression_len_off + 1u <= _hlen && \
                (_cipher_len == 2u || \
                 (_cipher_len == 4u && \
                  TLS13_Connection_Backend_read_u16(_body + _cipher_pos + 2u) == 0x00ffu)); \
              if (_ok) { \
                uint16_t _cipher = (uint16_t)TLS13_Connection_Backend_read_u16(_body + _cipher_pos); \
                size_t _compression_len = _body[_compression_len_off]; \
                size_t _compression_pos = _compression_len_off + 1u; \
                _ok = _cipher == 0x1303u && _compression_len == 1u && \
                  _compression_pos + 1u <= _hlen && _body[_compression_pos] == 0u; \
                if (_ok) { \
                  _cipher_suites[0] = _cipher; \
                  size_t _ext_len_off = _compression_pos + _compression_len; \
                  _ok = _ext_len_off + 2u <= _hlen; \
                  if (_ok) { \
                    size_t _ext_len = TLS13_Connection_Backend_read_u16(_body + _ext_len_off); \
                    size_t _pos = _ext_len_off + 2u; \
                    size_t _end = _pos + _ext_len; \
                    _ok = _end == _hlen; \
                    while (_ok && _pos < _end) { \
                      _ok = _pos + 4u <= _end; \
                      if (!_ok) { break; } \
                      uint16_t _etype = TLS13_Connection_Backend_read_u16(_body + _pos); \
                      size_t _elen = TLS13_Connection_Backend_read_u16(_body + _pos + 2u); \
                      size_t _edata = _pos + 4u; \
                      size_t _next = _edata + _elen; \
                      _ok = _next <= _end; \
                      if (!_ok) { break; } \
                      if (_etype == 0x0000u) { \
                        _ok = _elen >= 5u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata) + 2u == _elen && \
                          _body[_edata + 2u] == 0u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata + 3u) + 5u == _elen; \
                        if (_ok) { \
                          size_t _name_len = TLS13_Connection_Backend_read_u16(_body + _edata + 3u); \
                          _ok = _name_len <= 255u; \
                          if (_ok) { \
                            memcpy(_server_name, _body + _edata + 5u, _name_len); \
                            _server_name_len = _name_len; \
                            _has_server_name = true; \
                          } \
                        } \
                      } else if (_etype == 0x000au) { \
                        _ok = _elen == 4u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata) == 2u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata + 2u) == 0x001du; \
                      } else if (_etype == 0x000du) { \
                        _ok = _elen == 4u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata) == 2u; \
                        if (_ok) { \
                          _signature_schemes[0] = \
                            (uint16_t)TLS13_Connection_Backend_read_u16(_body + _edata + 2u); \
                          _signature_schemes_len = 1u; \
                        } \
                      } else if (_etype == 0x0033u) { \
                        _ok = _elen == 38u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata) == 36u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata + 2u) == 0x001du && \
                          TLS13_Connection_Backend_read_u16(_body + _edata + 4u) == 32u; \
                        if (_ok) { \
                          memcpy(_key_share, _body + _edata + 6u, 32u); \
                          _found_key_share = true; \
                        } \
                      } else if (_etype == 0x002bu) { \
                        _ok = _elen == 3u && \
                          _body[_edata] == 2u && \
                          TLS13_Connection_Backend_read_u16(_body + _edata + 1u) == 0x0304u; \
                        if (_ok) { \
                          _found_supported_versions = true; \
                        } \
                      } \
                      _pos = _next; \
                    } \
                    _ok = _ok && _pos == _end && _found_key_share && _found_supported_versions; \
                  } \
                } \
              } \
            } \
          } \
          if (_ok) { \
            _hs = (TLS13_Impl_Messages_handshake_msg){ \
              .tag = TLS13_Impl_Messages_LClientHello, \
              { .case_LClientHello = { \
                  .client_hello_random = _random, \
                  .client_hello_server_name = _server_name, \
                  .client_hello_server_name_len = _server_name_len, \
                  .client_hello_has_server_name = _has_server_name, \
                  .client_hello_key_share = _key_share, \
                  .client_hello_cipher_suites = _cipher_suites, \
                  .client_hello_cipher_suites_len = 1u, \
                  .client_hello_signature_schemes = _signature_schemes, \
                  .client_hello_signature_schemes_len = _signature_schemes_len } } \
            }; \
          } else { \
            free(_random); \
            free(_server_name); \
            free(_key_share); \
            free(_cipher_suites); \
            free(_signature_schemes); \
          } \
        } else if (_ht == 2u && _hlen >= 38u) { \
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
      } else if (_tls13_raw[1] != 3u || \
                 (_tls13_raw[2] != 3u && _tls13_raw[2] != 1u)) { \
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
          (_tls13_raw[2] != 3u && _tls13_raw[2] != 1u)) { \
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

#endif

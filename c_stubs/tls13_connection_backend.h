#ifndef TLS13_CONNECTION_BACKEND_H
#define TLS13_CONNECTION_BACKEND_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "tls13_hacl_stubs.h"

typedef struct TLS13_IO_channel_s *TLS13_IO_channel;

static inline void TLS13_Connection_Backend_write_u16(uint8_t *out, size_t v) {
  out[0] = (uint8_t)((v >> 8) & 0xffu);
  out[1] = (uint8_t)(v & 0xffu);
}

static inline void TLS13_Connection_Backend_write_u24(uint8_t *out, size_t v) {
  out[0] = (uint8_t)((v >> 16) & 0xffu);
  out[1] = (uint8_t)((v >> 8) & 0xffu);
  out[2] = (uint8_t)(v & 0xffu);
}

#define FStar_SizeT_uint_to_t(n) ((size_t)(n))

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

#endif

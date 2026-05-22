#include "tls13_wire_stubs.h"

#include <string.h>

#define TLS13_WIRE_HANDSHAKE_TYPE_SERVER_HELLO 2u
#define TLS13_WIRE_LEGACY_VERSION_TLS12 0x0303u
#define TLS13_WIRE_VERSION_TLS13 0x0304u
#define TLS13_WIRE_CIPHER_SUITE_CHACHA20_POLY1305_SHA256 0x1303u
#define TLS13_WIRE_NAMED_GROUP_X25519 0x001du
#define TLS13_WIRE_EXT_SUPPORTED_VERSIONS 0x002bu
#define TLS13_WIRE_EXT_KEY_SHARE 0x0033u
#define TLS13_WIRE_EXT_SERVER_NAME 0x0000u
#define TLS13_WIRE_EXT_SUPPORTED_GROUPS 0x000au
#define TLS13_WIRE_EXT_SIGNATURE_ALGORITHMS 0x000du
#define TLS13_WIRE_SIGNATURE_RSA_PSS_RSAE_SHA256 0x0804u

static uint16_t read_u16(const uint8_t *p) {
  return ((uint16_t)p[0] << 8) | (uint16_t)p[1];
}

static uint32_t read_u24(const uint8_t *p) {
  return ((uint32_t)p[0] << 16) | ((uint32_t)p[1] << 8) | (uint32_t)p[2];
}

static void write_u16(uint8_t *p, uint16_t x) {
  p[0] = (uint8_t)(x >> 8);
  p[1] = (uint8_t)x;
}

bool tls13_wire_parse_record_header(
    const uint8_t *input,
    size_t input_len,
    uint8_t *content_type,
    uint16_t *legacy_version,
    uint16_t *fragment_len) {
  if (input == NULL || content_type == NULL || legacy_version == NULL || fragment_len == NULL ||
      input_len < TLS13_WIRE_RECORD_HEADER_LEN) {
    return false;
  }

  uint16_t len = ((uint16_t)input[3] << 8) | (uint16_t)input[4];
  if (len > TLS13_WIRE_MAX_RECORD_FRAGMENT_LEN + 256u) {
    return false;
  }

  *content_type = input[0];
  *legacy_version = ((uint16_t)input[1] << 8) | (uint16_t)input[2];
  *fragment_len = len;
  return true;
}

bool tls13_wire_serialize_record_header(
    uint8_t out[TLS13_WIRE_RECORD_HEADER_LEN],
    uint8_t content_type,
    uint16_t legacy_version,
    uint16_t fragment_len) {
  if (out == NULL || fragment_len > TLS13_WIRE_MAX_RECORD_FRAGMENT_LEN + 256u) {
    return false;
  }
  out[0] = content_type;
  out[1] = (uint8_t)(legacy_version >> 8);
  out[2] = (uint8_t)legacy_version;
  out[3] = (uint8_t)(fragment_len >> 8);
  out[4] = (uint8_t)fragment_len;
  return true;
}

bool tls13_wire_parse_handshake_header(
    const uint8_t *input,
    size_t input_len,
    uint8_t *msg_type,
    uint32_t *body_len) {
  if (input == NULL || msg_type == NULL || body_len == NULL ||
      input_len < TLS13_WIRE_HANDSHAKE_HEADER_LEN) {
    return false;
  }
  *msg_type = input[0];
  *body_len = ((uint32_t)input[1] << 16) | ((uint32_t)input[2] << 8) | (uint32_t)input[3];
  return true;
}

bool tls13_wire_serialize_handshake_header(
    uint8_t out[TLS13_WIRE_HANDSHAKE_HEADER_LEN],
    uint8_t msg_type,
    uint32_t body_len) {
  if (out == NULL || body_len > TLS13_WIRE_MAX_HANDSHAKE_BODY_LEN) {
    return false;
  }
  out[0] = msg_type;
  out[1] = (uint8_t)(body_len >> 16);
  out[2] = (uint8_t)(body_len >> 8);
  out[3] = (uint8_t)body_len;
  return true;
}

bool tls13_wire_parse_supported_server_hello(
    const uint8_t *input,
    size_t input_len,
    uint8_t random[32],
    uint8_t key_share[32]) {
  static const uint8_t hello_retry_request_random[32] = {
      0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11,
      0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
      0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e,
      0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c};
  uint8_t parsed_random[32];
  uint8_t parsed_key_share[32];
  bool saw_supported_versions = false;
  bool saw_key_share = false;
  uint8_t msg_type = 0;
  uint32_t body_len = 0;

  if (input == NULL || random == NULL || key_share == NULL ||
      !tls13_wire_parse_handshake_header(input, input_len, &msg_type, &body_len) ||
      msg_type != TLS13_WIRE_HANDSHAKE_TYPE_SERVER_HELLO ||
      body_len != input_len - TLS13_WIRE_HANDSHAKE_HEADER_LEN) {
    return false;
  }

  const uint8_t *body = input + TLS13_WIRE_HANDSHAKE_HEADER_LEN;
  size_t pos = 0;
  if (body_len < 2 + 32 + 1 + 2 + 1 + 2) {
    return false;
  }
  if (read_u16(body + pos) != TLS13_WIRE_LEGACY_VERSION_TLS12) {
    return false;
  }
  pos += 2;
  memcpy(parsed_random, body + pos, sizeof parsed_random);
  if (memcmp(parsed_random, hello_retry_request_random, sizeof parsed_random) == 0) {
    return false;
  }
  pos += sizeof parsed_random;

  uint8_t session_id_len = body[pos++];
  if ((size_t)body_len - pos < (size_t)session_id_len + 2u + 1u + 2u) {
    return false;
  }
  pos += session_id_len;

  if (read_u16(body + pos) != TLS13_WIRE_CIPHER_SUITE_CHACHA20_POLY1305_SHA256) {
    return false;
  }
  pos += 2;
  if (body[pos++] != 0) {
    return false;
  }

  uint16_t extensions_len = read_u16(body + pos);
  pos += 2;
  if ((size_t)body_len - pos != extensions_len) {
    return false;
  }
  size_t extensions_end = pos + extensions_len;
  while (pos < extensions_end) {
    if (extensions_end - pos < 4) {
      return false;
    }
    uint16_t ext_type = read_u16(body + pos);
    uint16_t ext_len = read_u16(body + pos + 2);
    pos += 4;
    if (extensions_end - pos < ext_len) {
      return false;
    }
    const uint8_t *ext = body + pos;
    if (ext_type == TLS13_WIRE_EXT_SUPPORTED_VERSIONS) {
      if (ext_len != 2 || read_u16(ext) != TLS13_WIRE_VERSION_TLS13) {
        return false;
      }
      saw_supported_versions = true;
    } else if (ext_type == TLS13_WIRE_EXT_KEY_SHARE) {
      if (ext_len != 36 || read_u16(ext) != TLS13_WIRE_NAMED_GROUP_X25519 ||
          read_u16(ext + 2) != 32) {
        return false;
      }
      memcpy(parsed_key_share, ext + 4, sizeof parsed_key_share);
      saw_key_share = true;
    }
    pos += ext_len;
  }

  if (!saw_supported_versions || !saw_key_share) {
    return false;
  }
  memcpy(random, parsed_random, sizeof parsed_random);
  memcpy(key_share, parsed_key_share, sizeof parsed_key_share);
  return true;
}

bool tls13_wire_parse_certificate_leaf_der(
    const uint8_t *certificate_body,
    size_t certificate_body_len,
    const uint8_t **leaf_der,
    size_t *leaf_der_len) {
  if (certificate_body == NULL || leaf_der == NULL || leaf_der_len == NULL ||
      certificate_body_len < 4) {
    return false;
  }
  *leaf_der = NULL;
  *leaf_der_len = 0;

  size_t pos = 0;
  uint8_t request_context_len = certificate_body[pos++];
  if (certificate_body_len - pos < request_context_len + 3u) {
    return false;
  }
  pos += request_context_len;

  uint32_t certificate_list_len = read_u24(certificate_body + pos);
  pos += 3;
  if (certificate_list_len == 0 || certificate_list_len > certificate_body_len - pos) {
    return false;
  }
  size_t end = pos + (size_t)certificate_list_len;
  if (end != certificate_body_len) {
    return false;
  }

  while (pos < end) {
    if (end - pos < 5) {
      return false;
    }
    uint32_t cert_data_len = read_u24(certificate_body + pos);
    pos += 3;
    if (cert_data_len == 0 || cert_data_len > end - pos) {
      return false;
    }
    if (*leaf_der == NULL) {
      *leaf_der = certificate_body + pos;
      *leaf_der_len = (size_t)cert_data_len;
    }
    pos += cert_data_len;
    if (end - pos < 2) {
      return false;
    }
    uint16_t extensions_len = read_u16(certificate_body + pos);
    pos += 2;
    if (extensions_len > end - pos) {
      return false;
    }
    pos += extensions_len;
  }

  return *leaf_der != NULL;
}

bool tls13_wire_parse_certificate_verify(
    const uint8_t *certificate_verify_body,
    size_t certificate_verify_body_len,
    uint16_t *signature_scheme,
    const uint8_t **signature,
    size_t *signature_len) {
  if (certificate_verify_body == NULL || signature_scheme == NULL || signature == NULL ||
      signature_len == NULL || certificate_verify_body_len < 4) {
    return false;
  }
  uint16_t scheme = read_u16(certificate_verify_body);
  uint16_t sig_len = read_u16(certificate_verify_body + 2);
  if ((size_t)sig_len != certificate_verify_body_len - 4u) {
    return false;
  }
  *signature_scheme = scheme;
  *signature = certificate_verify_body + 4;
  *signature_len = sig_len;
  return true;
}

bool tls13_wire_build_server_certificate_verify_input(
    uint8_t out[TLS13_WIRE_CERTIFICATE_VERIFY_INPUT_LEN],
    const uint8_t transcript_hash[32]) {
  static const uint8_t context[] = "TLS 1.3, server CertificateVerify";
  if (out == NULL || transcript_hash == NULL) {
    return false;
  }

  size_t pos = 0;
  memset(out + pos, 0x20, 64);
  pos += 64;
  memcpy(out + pos, context, sizeof context - 1u);
  pos += sizeof context - 1u;
  out[pos++] = 0;
  memcpy(out + pos, transcript_hash, 32);
  pos += 32;
  return pos == TLS13_WIRE_CERTIFICATE_VERIFY_INPUT_LEN;
}

bool tls13_wire_serialize_supported_client_hello(
    uint8_t *out,
    size_t out_len,
    const uint8_t random[32],
    const uint8_t key_share[32],
    const uint8_t *hostname,
    size_t hostname_len,
    size_t *written) {
  if (out == NULL || random == NULL || key_share == NULL || written == NULL ||
      (hostname_len != 0 && hostname == NULL) ||
      hostname_len > TLS13_WIRE_MAX_HOSTNAME_LEN) {
    return false;
  }

  size_t sni_extension_len = hostname_len == 0 ? 0 : 9u + hostname_len;
  size_t extensions_len =
      sni_extension_len +
      8u +   /* supported_groups */
      8u +   /* signature_algorithms */
      42u +  /* key_share */
      7u;    /* supported_versions */
  size_t body_len = 43u + extensions_len;
  size_t total_len = TLS13_WIRE_HANDSHAKE_HEADER_LEN + body_len;
  if (body_len > TLS13_WIRE_MAX_HANDSHAKE_BODY_LEN || out_len < total_len) {
    return false;
  }

  size_t pos = 0;
  out[pos++] = 1u;
  out[pos++] = (uint8_t)(body_len >> 16);
  out[pos++] = (uint8_t)(body_len >> 8);
  out[pos++] = (uint8_t)body_len;
  write_u16(out + pos, TLS13_WIRE_LEGACY_VERSION_TLS12);
  pos += 2;
  memcpy(out + pos, random, 32);
  pos += 32;
  out[pos++] = 0u;
  write_u16(out + pos, 2u);
  pos += 2;
  write_u16(out + pos, TLS13_WIRE_CIPHER_SUITE_CHACHA20_POLY1305_SHA256);
  pos += 2;
  out[pos++] = 1u;
  out[pos++] = 0u;
  write_u16(out + pos, (uint16_t)extensions_len);
  pos += 2;

  if (hostname_len != 0) {
    write_u16(out + pos, TLS13_WIRE_EXT_SERVER_NAME);
    pos += 2;
    write_u16(out + pos, (uint16_t)(5u + hostname_len));
    pos += 2;
    write_u16(out + pos, (uint16_t)(3u + hostname_len));
    pos += 2;
    out[pos++] = 0u;
    write_u16(out + pos, (uint16_t)hostname_len);
    pos += 2;
    memcpy(out + pos, hostname, hostname_len);
    pos += hostname_len;
  }

  write_u16(out + pos, TLS13_WIRE_EXT_SUPPORTED_GROUPS);
  pos += 2;
  write_u16(out + pos, 4u);
  pos += 2;
  write_u16(out + pos, 2u);
  pos += 2;
  write_u16(out + pos, TLS13_WIRE_NAMED_GROUP_X25519);
  pos += 2;

  write_u16(out + pos, TLS13_WIRE_EXT_SIGNATURE_ALGORITHMS);
  pos += 2;
  write_u16(out + pos, 4u);
  pos += 2;
  write_u16(out + pos, 2u);
  pos += 2;
  write_u16(out + pos, TLS13_WIRE_SIGNATURE_RSA_PSS_RSAE_SHA256);
  pos += 2;

  write_u16(out + pos, TLS13_WIRE_EXT_KEY_SHARE);
  pos += 2;
  write_u16(out + pos, 38u);
  pos += 2;
  write_u16(out + pos, 36u);
  pos += 2;
  write_u16(out + pos, TLS13_WIRE_NAMED_GROUP_X25519);
  pos += 2;
  write_u16(out + pos, 32u);
  pos += 2;
  memcpy(out + pos, key_share, 32);
  pos += 32;

  write_u16(out + pos, TLS13_WIRE_EXT_SUPPORTED_VERSIONS);
  pos += 2;
  write_u16(out + pos, 3u);
  pos += 2;
  out[pos++] = 2u;
  write_u16(out + pos, TLS13_WIRE_VERSION_TLS13);
  pos += 2;

  if (pos != total_len) {
    return false;
  }
  *written = total_len;
  return true;
}

bool tls13_wire_encode_inner_plaintext(
    uint8_t *out,
    size_t out_len,
    const uint8_t *plaintext,
    size_t plaintext_len,
    uint8_t content_type,
    size_t padding_len) {
  if (plaintext_len > SIZE_MAX - 1 || plaintext_len + 1 > SIZE_MAX - padding_len ||
      out_len != plaintext_len + 1 + padding_len ||
      (out_len != 0 && out == NULL) ||
      (plaintext_len != 0 && plaintext == NULL)) {
    return false;
  }
  memcpy(out, plaintext, plaintext_len);
  out[plaintext_len] = content_type;
  memset(out + plaintext_len + 1, 0, padding_len);
  return true;
}

bool tls13_wire_decode_inner_plaintext(
    const uint8_t *inner_plaintext,
    size_t inner_plaintext_len,
    uint8_t *content_type,
    size_t *plaintext_len) {
  if (inner_plaintext == NULL || content_type == NULL || plaintext_len == NULL ||
      inner_plaintext_len == 0) {
    return false;
  }

  size_t i = inner_plaintext_len;
  while (i > 0 && inner_plaintext[i - 1] == 0) {
    --i;
  }
  if (i == 0) {
    return false;
  }
  *content_type = inner_plaintext[i - 1];
  *plaintext_len = i - 1;
  return true;
}

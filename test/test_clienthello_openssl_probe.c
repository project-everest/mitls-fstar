#include "tls13_hacl_stubs.h"
#include "tls13_io_stubs.h"
#include "tls13_openssl_stubs.h"
#include "tls13_wire_stubs.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t *read_file(const char *path, size_t *len_out) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return NULL;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fclose(f);
    return NULL;
  }
  long len = ftell(f);
  if (len < 0) {
    fclose(f);
    return NULL;
  }
  rewind(f);
  uint8_t *buf = malloc((size_t)len);
  if (buf == NULL) {
    fclose(f);
    return NULL;
  }
  if (fread(buf, 1, (size_t)len, f) != (size_t)len) {
    free(buf);
    fclose(f);
    return NULL;
  }
  fclose(f);
  *len_out = (size_t)len;
  return buf;
}

static int write_all(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = tls13_io_write_fd(fd, buf + off, len - off);
    if (n <= 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

static int read_exact(int fd, uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = tls13_io_read_fd(fd, buf + off, len - off);
    if (n <= 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

static int read_record(
    int fd,
    uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN],
    uint8_t *fragment,
    size_t fragment_capacity,
    uint8_t *content_type,
    uint16_t *legacy_version,
    uint16_t *fragment_len) {
  if (read_exact(fd, header, TLS13_WIRE_RECORD_HEADER_LEN) != 0) {
    return -1;
  }
  if (!tls13_wire_parse_record_header(
          header, TLS13_WIRE_RECORD_HEADER_LEN, content_type, legacy_version, fragment_len) ||
      *fragment_len > fragment_capacity) {
    return -1;
  }
  return read_exact(fd, fragment, *fragment_len);
}

static int derive_server_handshake_keys(
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t server_key_share[32],
    uint8_t handshake_secret[32],
    uint8_t client_handshake_traffic_secret[32],
    uint8_t server_handshake_traffic_secret[32],
    uint8_t client_key[32],
    uint8_t client_iv[12],
    uint8_t server_key[32],
    uint8_t server_iv[12]) {
  static const uint8_t client_private_key[32] = {
      0x49, 0xaf, 0x42, 0xba, 0x7f, 0x79, 0x94, 0x85,
      0x2d, 0x71, 0x3e, 0xf2, 0x78, 0x4b, 0xcb, 0xca,
      0xa7, 0x91, 0x1d, 0xe2, 0x6a, 0xdc, 0x56, 0x42,
      0xcb, 0x63, 0x45, 0x40, 0xe7, 0xea, 0x50, 0x05};
  static const uint8_t zero_secret[32] = {0};
  static const uint8_t label_derived[] = {'d', 'e', 'r', 'i', 'v', 'e', 'd'};
  static const uint8_t label_c_hs_traffic[] = {
      'c', ' ', 'h', 's', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_s_hs_traffic[] = {
      's', ' ', 'h', 's', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_key[] = {'k', 'e', 'y'};
  static const uint8_t label_iv[] = {'i', 'v'};

  uint8_t empty_hash[32];
  uint8_t early_secret[32];
  uint8_t derived_secret[32];
  uint8_t shared_secret[32];
  uint8_t transcript[1024];
  uint8_t transcript_hash[32];

  if (client_hello_len > sizeof transcript ||
      server_hello_len > sizeof transcript - client_hello_len) {
    return -1;
  }
  if (!tls13_hacl_sha256(empty_hash, NULL, 0) ||
      !tls13_hacl_hkdf_extract_sha256(
          early_secret, NULL, 0, zero_secret, sizeof zero_secret) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          derived_secret,
          sizeof derived_secret,
          early_secret,
          label_derived,
          sizeof label_derived,
          empty_hash,
          sizeof empty_hash) ||
      !tls13_hacl_x25519_shared(shared_secret, client_private_key, server_key_share) ||
      !tls13_hacl_hkdf_extract_sha256(
          handshake_secret,
          derived_secret,
          sizeof derived_secret,
          shared_secret,
          sizeof shared_secret)) {
    return -1;
  }

  memcpy(transcript, client_hello, client_hello_len);
  memcpy(transcript + client_hello_len, server_hello, server_hello_len);
  if (!tls13_hacl_sha256(transcript_hash, transcript, client_hello_len + server_hello_len) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_handshake_traffic_secret,
          32,
          handshake_secret,
          label_c_hs_traffic,
          sizeof label_c_hs_traffic,
          transcript_hash,
          sizeof transcript_hash) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_handshake_traffic_secret,
          32,
          handshake_secret,
          label_s_hs_traffic,
          sizeof label_s_hs_traffic,
          transcript_hash,
          sizeof transcript_hash) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_key,
          32,
          client_handshake_traffic_secret,
          label_key,
          sizeof label_key,
          NULL,
          0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_iv,
          12,
          client_handshake_traffic_secret,
          label_iv,
          sizeof label_iv,
          NULL,
          0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_key,
          32,
          server_handshake_traffic_secret,
          label_key,
          sizeof label_key,
          NULL,
          0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_iv,
          12,
          server_handshake_traffic_secret,
          label_iv,
          sizeof label_iv,
          NULL,
          0)) {
    return -1;
  }
  return 0;
}

static int compute_transcript_hash(
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t *server_handshake_messages,
    size_t server_handshake_len,
    uint8_t transcript_hash[32]) {
  uint8_t transcript[32768];
  if (client_hello_len > sizeof transcript ||
      server_hello_len > sizeof transcript - client_hello_len ||
      server_handshake_len > sizeof transcript - client_hello_len - server_hello_len) {
    return -1;
  }
  size_t pos = 0;
  memcpy(transcript + pos, client_hello, client_hello_len);
  pos += client_hello_len;
  memcpy(transcript + pos, server_hello, server_hello_len);
  pos += server_hello_len;
  memcpy(transcript + pos, server_handshake_messages, server_handshake_len);
  pos += server_handshake_len;
  return tls13_hacl_sha256(transcript_hash, transcript, pos) ? 0 : -1;
}

static int verify_server_finished(
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t *server_handshake_messages,
    size_t server_handshake_before_finished_len,
    const uint8_t finished_verify_data[32],
    const uint8_t server_handshake_traffic_secret[32]) {
  uint8_t transcript_hash[32];
  uint8_t expected[32];

  if (compute_transcript_hash(
          client_hello,
          client_hello_len,
          server_hello,
          server_hello_len,
          server_handshake_messages,
          server_handshake_before_finished_len,
          transcript_hash) != 0) {
    return -1;
  }
  if (!tls13_hacl_finished_verify_data_sha256(
          expected, server_handshake_traffic_secret, transcript_hash)) {
    return -1;
  }
  return memcmp(expected, finished_verify_data, 32) == 0 ? 0 : -1;
}

static int build_certificate_verify_input(
    const uint8_t transcript_hash[32],
    uint8_t *out,
    size_t out_capacity,
    size_t *out_len) {
  static const uint8_t context[] = "TLS 1.3, server CertificateVerify";
  const size_t needed = 64u + sizeof context - 1u + 1u + 32u;
  if (transcript_hash == NULL || out == NULL || out_len == NULL || out_capacity < needed) {
    return -1;
  }
  size_t pos = 0;
  memset(out + pos, 0x20, 64);
  pos += 64;
  memcpy(out + pos, context, sizeof context - 1u);
  pos += sizeof context - 1u;
  out[pos++] = 0;
  memcpy(out + pos, transcript_hash, 32);
  pos += 32;
  *out_len = pos;
  return 0;
}

static int verify_server_authentication(
    const uint8_t *ca_pem,
    size_t ca_pem_len,
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t *server_handshake_messages,
    size_t server_handshake_before_finished_len) {
  size_t pos = 0;
  bool saw_encrypted_extensions = false;
  bool saw_certificate = false;
  bool saw_certificate_verify = false;
  const uint8_t *leaf_der = NULL;
  size_t leaf_der_len = 0;
  uint16_t signature_scheme = 0;
  const uint8_t *signature = NULL;
  size_t signature_len = 0;
  size_t certificate_verify_offset = 0;

  while (pos < server_handshake_before_finished_len) {
    if (server_handshake_before_finished_len - pos < TLS13_WIRE_HANDSHAKE_HEADER_LEN) {
      fprintf(stderr, "truncated decrypted server handshake message\n");
      return -1;
    }
    uint8_t handshake_type = 0;
    uint32_t handshake_body_len = 0;
    if (!tls13_wire_parse_handshake_header(
            server_handshake_messages + pos,
            server_handshake_before_finished_len - pos,
            &handshake_type,
            &handshake_body_len)) {
      fprintf(stderr, "failed to parse server authentication handshake header\n");
      return -1;
    }
    size_t message_len = TLS13_WIRE_HANDSHAKE_HEADER_LEN + (size_t)handshake_body_len;
    if (message_len > server_handshake_before_finished_len - pos) {
      fprintf(stderr, "truncated server authentication handshake body\n");
      return -1;
    }
    const uint8_t *body = server_handshake_messages + pos + TLS13_WIRE_HANDSHAKE_HEADER_LEN;

    switch (handshake_type) {
    case 8:
      if (pos != 0 || saw_encrypted_extensions) {
        fprintf(stderr, "unexpected EncryptedExtensions ordering\n");
        return -1;
      }
      saw_encrypted_extensions = true;
      break;
    case 11:
      if (!saw_encrypted_extensions || saw_certificate) {
        fprintf(stderr, "unexpected Certificate ordering\n");
        return -1;
      }
      if (!tls13_wire_parse_certificate_leaf_der(
              body, handshake_body_len, &leaf_der, &leaf_der_len)) {
        fprintf(stderr, "failed to parse server Certificate\n");
        return -1;
      }
      saw_certificate = true;
      break;
    case 15:
      if (!saw_certificate || saw_certificate_verify) {
        fprintf(stderr, "unexpected CertificateVerify ordering\n");
        return -1;
      }
      certificate_verify_offset = pos;
      if (!tls13_wire_parse_certificate_verify(
              body, handshake_body_len, &signature_scheme, &signature, &signature_len)) {
        fprintf(stderr, "failed to parse server CertificateVerify\n");
        return -1;
      }
      saw_certificate_verify = true;
      break;
    default:
      fprintf(stderr, "unexpected server handshake message before Finished: %u\n", handshake_type);
      return -1;
    }
    pos += message_len;
  }

  if (!saw_encrypted_extensions || !saw_certificate || !saw_certificate_verify) {
    fprintf(stderr, "server authentication handshake messages incomplete\n");
    return -1;
  }

  tls13_peer_identity *peer = NULL;
  int rc = -1;
  uint8_t transcript_hash[32];
  uint8_t certificate_verify_input[130];
  size_t certificate_verify_input_len = 0;
  if (!tls13_openssl_validate_leaf_der(
          "localhost", ca_pem, ca_pem_len, leaf_der, leaf_der_len, &peer) ||
      peer == NULL) {
    fprintf(stderr, "failed to validate server certificate\n");
    goto done;
  }
  if (compute_transcript_hash(
          client_hello,
          client_hello_len,
          server_hello,
          server_hello_len,
          server_handshake_messages,
          certificate_verify_offset,
          transcript_hash) != 0 ||
      build_certificate_verify_input(
          transcript_hash,
          certificate_verify_input,
          sizeof certificate_verify_input,
          &certificate_verify_input_len) != 0) {
    fprintf(stderr, "failed to build CertificateVerify input\n");
    goto done;
  }
  if (!tls13_openssl_peer_verify_signature(
          peer,
          signature_scheme,
          certificate_verify_input,
          certificate_verify_input_len,
          signature,
          signature_len)) {
    fprintf(stderr, "failed to verify server CertificateVerify\n");
    goto done;
  }
  rc = 0;

done:
  tls13_openssl_peer_identity_free(peer);
  return rc;
}

static int derive_application_keys(
    const uint8_t handshake_secret[32],
    const uint8_t transcript_hash[32],
    uint8_t client_key[32],
    uint8_t client_iv[12],
    uint8_t server_key[32],
    uint8_t server_iv[12]) {
  static const uint8_t zero_secret[32] = {0};
  static const uint8_t label_derived[] = {'d', 'e', 'r', 'i', 'v', 'e', 'd'};
  static const uint8_t label_c_ap_traffic[] = {
      'c', ' ', 'a', 'p', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_s_ap_traffic[] = {
      's', ' ', 'a', 'p', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_key[] = {'k', 'e', 'y'};
  static const uint8_t label_iv[] = {'i', 'v'};
  uint8_t empty_hash[32];
  uint8_t derived_secret[32];
  uint8_t master_secret[32];
  uint8_t client_application_traffic_secret[32];
  uint8_t server_application_traffic_secret[32];

  if (!tls13_hacl_sha256(empty_hash, NULL, 0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          derived_secret,
          sizeof derived_secret,
          handshake_secret,
          label_derived,
          sizeof label_derived,
          empty_hash,
          sizeof empty_hash) ||
      !tls13_hacl_hkdf_extract_sha256(
          master_secret, derived_secret, sizeof derived_secret, zero_secret, sizeof zero_secret) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_application_traffic_secret,
          sizeof client_application_traffic_secret,
          master_secret,
          label_c_ap_traffic,
          sizeof label_c_ap_traffic,
          transcript_hash,
          32) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_application_traffic_secret,
          sizeof server_application_traffic_secret,
          master_secret,
          label_s_ap_traffic,
          sizeof label_s_ap_traffic,
          transcript_hash,
          32) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_key, 32, client_application_traffic_secret, label_key, sizeof label_key, NULL, 0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_iv, 12, client_application_traffic_secret, label_iv, sizeof label_iv, NULL, 0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_key, 32, server_application_traffic_secret, label_key, sizeof label_key, NULL, 0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_iv, 12, server_application_traffic_secret, label_iv, sizeof label_iv, NULL, 0)) {
    return -1;
  }
  return 0;
}

static int seal_record(
    const uint8_t key[32],
    const uint8_t iv[12],
    uint64_t sequence_number,
    uint8_t inner_content_type,
    const uint8_t *plaintext,
    size_t plaintext_len,
    uint8_t *record,
    size_t record_capacity,
    size_t *record_len) {
  uint8_t inner_plaintext[20000];
  uint8_t nonce[12];
  if (plaintext_len > sizeof inner_plaintext - 1u ||
      plaintext_len > UINT16_MAX - 17u ||
      record_capacity < TLS13_WIRE_RECORD_HEADER_LEN + plaintext_len + 1u + 16u) {
    return -1;
  }
  memcpy(inner_plaintext, plaintext, plaintext_len);
  inner_plaintext[plaintext_len] = inner_content_type;
  size_t inner_plaintext_len = plaintext_len + 1u;
  size_t ciphertext_len = inner_plaintext_len + 16u;
  if (!tls13_wire_serialize_record_header(record, 23, 0x0303, (uint16_t)ciphertext_len) ||
      !tls13_record_nonce(nonce, iv, sequence_number) ||
      !tls13_hacl_chacha20_poly1305_seal_combined(
          record + TLS13_WIRE_RECORD_HEADER_LEN,
          ciphertext_len,
          key,
          nonce,
          record,
          TLS13_WIRE_RECORD_HEADER_LEN,
          inner_plaintext,
          inner_plaintext_len)) {
    return -1;
  }
  *record_len = TLS13_WIRE_RECORD_HEADER_LEN + ciphertext_len;
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s HOST PORT CA_PEM\n", argv[0]);
    return 1;
  }

  char *end = NULL;
  long port_long = strtol(argv[2], &end, 10);
  if (*argv[2] == '\0' || *end != '\0' || port_long <= 0 || port_long > 65535) {
    fprintf(stderr, "invalid port\n");
    return 1;
  }

  size_t ca_pem_len = 0;
  uint8_t *ca_pem = read_file(argv[3], &ca_pem_len);
  if (ca_pem == NULL) {
    return 1;
  }

  static const uint8_t random[32] = {
      0xcb, 0x34, 0xec, 0xb1, 0xe7, 0x81, 0x63, 0xba,
      0x1c, 0x38, 0xc6, 0xda, 0xcb, 0x19, 0x6a, 0x6d,
      0xff, 0xa2, 0x1a, 0x8d, 0x99, 0x12, 0xec, 0x18,
      0xa2, 0xef, 0x62, 0x83, 0x02, 0x4d, 0xec, 0xe7};
  static const uint8_t key_share[32] = {
      0x99, 0x38, 0x1d, 0xe5, 0x60, 0xe4, 0xbd, 0x43,
      0xd2, 0x3d, 0x8e, 0x43, 0x5a, 0x7d, 0xba, 0xfe,
      0xb3, 0xc0, 0x6e, 0x51, 0xc1, 0x3c, 0xae, 0x4d,
      0x54, 0x13, 0x69, 0x1e, 0x52, 0x9a, 0xaf, 0x2c};
  static const uint8_t hostname[] = {'l', 'o', 'c', 'a', 'l', 'h', 'o', 's', 't'};

  uint8_t client_hello[512];
  size_t client_hello_len = 0;
  if (!tls13_wire_serialize_supported_client_hello(
          client_hello,
          sizeof client_hello,
          random,
          key_share,
          hostname,
          sizeof hostname,
          &client_hello_len)) {
    fprintf(stderr, "failed to serialize ClientHello\n");
    return 1;
  }

  uint8_t record[TLS13_WIRE_RECORD_HEADER_LEN + sizeof client_hello];
  if (!tls13_wire_serialize_record_header(
          record, 22, 0x0301, (uint16_t)client_hello_len)) {
    fprintf(stderr, "failed to serialize ClientHello record header\n");
    return 1;
  }
  memcpy(record + TLS13_WIRE_RECORD_HEADER_LEN, client_hello, client_hello_len);
  size_t record_len = TLS13_WIRE_RECORD_HEADER_LEN + client_hello_len;

  int fd = tls13_io_connect_tcp(argv[1], (uint16_t)port_long);
  if (fd < 0) {
    perror("connect");
    free(ca_pem);
    return 1;
  }

  int rc = 1;
  uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t server_hello_fragment[4096];
  uint8_t encrypted_fragment[20000];
  uint8_t encrypted_header[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t content_type = 0;
  uint16_t legacy_version = 0;
  uint16_t fragment_len = 0;
  uint8_t server_random[32];
  uint8_t server_key_share[32];

  if (write_all(fd, record, record_len) != 0) {
    perror("write ClientHello");
    goto done;
  }
  if (read_record(
          fd,
          header,
          server_hello_fragment,
          sizeof server_hello_fragment,
          &content_type,
          &legacy_version,
          &fragment_len) != 0 ||
      content_type != 22) {
    fprintf(stderr, "bad ServerHello record header\n");
    goto done;
  }
  if (!tls13_wire_parse_supported_server_hello(
          server_hello_fragment, fragment_len, server_random, server_key_share)) {
    fprintf(stderr, "failed to parse supported OpenSSL ServerHello\n");
    goto done;
  }
  size_t server_hello_len = fragment_len;

  uint8_t handshake_secret[32];
  uint8_t client_handshake_traffic_secret[32];
  uint8_t server_handshake_traffic_secret[32];
  uint8_t client_handshake_key[32];
  uint8_t client_handshake_iv[12];
  uint8_t server_handshake_key[32];
  uint8_t server_handshake_iv[12];
  if (derive_server_handshake_keys(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_key_share,
          handshake_secret,
          client_handshake_traffic_secret,
          server_handshake_traffic_secret,
          client_handshake_key,
          client_handshake_iv,
          server_handshake_key,
          server_handshake_iv) != 0) {
    fprintf(stderr, "failed to derive handshake traffic keys\n");
    goto done;
  }

  uint8_t server_handshake_messages[32768];
  size_t server_handshake_len = 0;
  size_t parsed_handshake_len = 0;
  size_t server_handshake_before_finished_len = 0;
  size_t server_handshake_through_finished_len = 0;
  uint8_t server_finished_verify_data[32];
  bool saw_finished = false;
  uint64_t server_sequence_number = 0;

  for (unsigned attempts = 0; attempts < 8 && !saw_finished; ++attempts) {
    if (read_record(
            fd,
            encrypted_header,
            encrypted_fragment,
            sizeof encrypted_fragment,
            &content_type,
            &legacy_version,
            &fragment_len) != 0) {
      fprintf(stderr, "failed to read encrypted handshake record\n");
      goto done;
    }
    if (content_type == 20 && fragment_len == 1 && encrypted_fragment[0] == 1) {
      continue;
    }
    if (content_type != 23 || fragment_len < 16) {
      fprintf(stderr, "unexpected record before server Finished: %u\n", content_type);
      goto done;
    }

    uint8_t nonce[12];
    uint8_t inner_plaintext[20000];
    size_t inner_plaintext_len = (size_t)fragment_len - 16u;
    if (!tls13_record_nonce(nonce, server_handshake_iv, server_sequence_number++) ||
        !tls13_hacl_chacha20_poly1305_open_combined(
            inner_plaintext,
            inner_plaintext_len,
            server_handshake_key,
            nonce,
            encrypted_header,
            TLS13_WIRE_RECORD_HEADER_LEN,
            encrypted_fragment,
            fragment_len)) {
      fprintf(stderr, "failed to decrypt OpenSSL encrypted handshake record\n");
      goto done;
    }

    uint8_t inner_content_type = 0;
    size_t handshake_plaintext_len = 0;
    if (!tls13_wire_decode_inner_plaintext(
            inner_plaintext, inner_plaintext_len, &inner_content_type, &handshake_plaintext_len) ||
        inner_content_type != 22 ||
        handshake_plaintext_len > sizeof server_handshake_messages - server_handshake_len) {
      fprintf(stderr, "failed to decode OpenSSL handshake inner plaintext\n");
      goto done;
    }
    memcpy(server_handshake_messages + server_handshake_len, inner_plaintext, handshake_plaintext_len);
    server_handshake_len += handshake_plaintext_len;

    while (server_handshake_len - parsed_handshake_len >= TLS13_WIRE_HANDSHAKE_HEADER_LEN) {
      uint8_t handshake_type = 0;
      uint32_t handshake_body_len = 0;
      if (!tls13_wire_parse_handshake_header(
              server_handshake_messages + parsed_handshake_len,
              server_handshake_len - parsed_handshake_len,
              &handshake_type,
              &handshake_body_len)) {
        fprintf(stderr, "failed to parse decrypted handshake header\n");
        goto done;
      }
      size_t message_len = TLS13_WIRE_HANDSHAKE_HEADER_LEN + (size_t)handshake_body_len;
      if (message_len > server_handshake_len - parsed_handshake_len) {
        break;
      }
      if (parsed_handshake_len == 0 && handshake_type != 8) {
        fprintf(stderr, "decrypted first OpenSSL handshake message is not EncryptedExtensions\n");
        goto done;
      }
      if (handshake_type == 20) {
        if (handshake_body_len != 32) {
          fprintf(stderr, "OpenSSL Finished has unexpected length\n");
          goto done;
        }
        server_handshake_before_finished_len = parsed_handshake_len;
        server_handshake_through_finished_len = parsed_handshake_len + message_len;
        memcpy(
            server_finished_verify_data,
            server_handshake_messages + parsed_handshake_len + TLS13_WIRE_HANDSHAKE_HEADER_LEN,
            sizeof server_finished_verify_data);
        saw_finished = true;
        break;
      }
      parsed_handshake_len += message_len;
    }
  }

  if (!saw_finished ||
      verify_server_authentication(
          ca_pem,
          ca_pem_len,
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          server_handshake_before_finished_len) != 0 ||
      verify_server_finished(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          server_handshake_before_finished_len,
          server_finished_verify_data,
          server_handshake_traffic_secret) != 0) {
    fprintf(stderr, "failed to verify OpenSSL server Finished\n");
    goto done;
  }

  uint8_t transcript_hash_through_server_finished[32];
  if (compute_transcript_hash(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          server_handshake_through_finished_len,
          transcript_hash_through_server_finished) != 0) {
    fprintf(stderr, "failed to hash transcript through server Finished\n");
    goto done;
  }

  uint8_t client_finished[36] = {20, 0, 0, 32};
  if (!tls13_hacl_finished_verify_data_sha256(
          client_finished + TLS13_WIRE_HANDSHAKE_HEADER_LEN,
          client_handshake_traffic_secret,
          transcript_hash_through_server_finished)) {
    fprintf(stderr, "failed to compute client Finished\n");
    goto done;
  }

  uint8_t client_record[20000];
  size_t client_record_len = 0;
  if (seal_record(
          client_handshake_key,
          client_handshake_iv,
          0,
          22,
          client_finished,
          sizeof client_finished,
          client_record,
          sizeof client_record,
          &client_record_len) != 0 ||
      write_all(fd, client_record, client_record_len) != 0) {
    fprintf(stderr, "failed to send client Finished\n");
    goto done;
  }

  uint8_t client_application_key[32];
  uint8_t client_application_iv[12];
  uint8_t server_application_key[32];
  uint8_t server_application_iv[12];
  if (derive_application_keys(
          handshake_secret,
          transcript_hash_through_server_finished,
          client_application_key,
          client_application_iv,
          server_application_key,
          server_application_iv) != 0) {
    fprintf(stderr, "failed to derive application traffic keys\n");
    goto done;
  }

  static const uint8_t echo_payload[] = {
      'a', 'g', 'e', 'n', 't', 'i', 'c', ' ', 't', 'l', 's', ' ', 'p', 'r', 'o', 'b', 'e'};
  if (seal_record(
          client_application_key,
          client_application_iv,
          0,
          23,
          echo_payload,
          sizeof echo_payload,
          client_record,
          sizeof client_record,
          &client_record_len) != 0 ||
      write_all(fd, client_record, client_record_len) != 0) {
    fprintf(stderr, "failed to send application-data probe record\n");
    goto done;
  }

  bool saw_echo = false;
  uint64_t server_application_sequence_number = 0;
  for (unsigned attempts = 0; attempts < 8 && !saw_echo; ++attempts) {
    if (read_record(
            fd,
            encrypted_header,
            encrypted_fragment,
            sizeof encrypted_fragment,
            &content_type,
            &legacy_version,
            &fragment_len) != 0 ||
        content_type != 23 ||
        fragment_len < 16) {
      fprintf(stderr, "failed to read application-data response record\n");
      goto done;
    }

    uint8_t nonce[12];
    uint8_t inner_plaintext[20000];
    size_t inner_plaintext_len = (size_t)fragment_len - 16u;
    if (!tls13_record_nonce(nonce, server_application_iv, server_application_sequence_number++) ||
        !tls13_hacl_chacha20_poly1305_open_combined(
            inner_plaintext,
            inner_plaintext_len,
            server_application_key,
            nonce,
            encrypted_header,
            TLS13_WIRE_RECORD_HEADER_LEN,
            encrypted_fragment,
            fragment_len)) {
      fprintf(stderr, "failed to decrypt application-data response record\n");
      goto done;
    }

    uint8_t inner_content_type = 0;
    size_t response_len = 0;
    if (!tls13_wire_decode_inner_plaintext(
            inner_plaintext, inner_plaintext_len, &inner_content_type, &response_len)) {
      fprintf(stderr, "failed to decode application-data response record\n");
      goto done;
    }
    if (inner_content_type == 22) {
      continue;
    }
    if (inner_content_type != 23 ||
        response_len != sizeof echo_payload ||
        memcmp(inner_plaintext, echo_payload, sizeof echo_payload) != 0) {
      fprintf(stderr, "OpenSSL echo application data mismatch\n");
      goto done;
    }
    saw_echo = true;
  }
  if (!saw_echo) {
    fprintf(stderr, "OpenSSL echo application data was not received\n");
    goto done;
  }

  printf("ClientHello/OpenSSL TLS echo probe passed\n");
  rc = 0;

done:
  tls13_io_close_fd(fd);
  free(ca_pem);
  return rc;
}

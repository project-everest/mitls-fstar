#include "TLS13_Impl_Client.h"
#include "TLS13_Impl_Client_Types.h"
#include "TLS13_Impl_ConnectionState.h"
#include "TLS13_KeySchedule.h"
#include "tls13_crypto_external.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static void write_u16(uint8_t *out, uint16_t v) {
  out[0] = (uint8_t)(v >> 8);
  out[1] = (uint8_t)v;
}

static void write_u24(uint8_t *out, size_t v) {
  out[0] = (uint8_t)(v >> 16);
  out[1] = (uint8_t)(v >> 8);
  out[2] = (uint8_t)v;
}

static int expect_step_ok(
    TLS13_Impl_Client_Types_client_response resp,
    const char *label) {
  if (resp.status != TLS13_Impl_Client_Types_StepOk) {
    fprintf(stderr, "%s failed with status %d\n", label, (int)resp.status);
    return 1;
  }
  return 0;
}

static int expect_handshake_stage(
    TLS13_Impl_ConnectionState_connection_state c,
    uint8_t expected_stage,
    const char *label) {
  TLS13_Impl_ConnectionState_control_snapshot snapshot = control_snapshot(c);
  if (snapshot.snapshot_control_tag != 1 ||
      snapshot.snapshot_handshake_stage_tag != expected_stage) {
    fprintf(stderr, "%s left unexpected stage %u/%u\n",
            label,
            (unsigned)snapshot.snapshot_control_tag,
            (unsigned)snapshot.snapshot_handshake_stage_tag);
    return 1;
  }
  return 0;
}

static int expect_control_tag(
    TLS13_Impl_ConnectionState_connection_state c,
    uint8_t expected_tag,
    const char *label) {
  TLS13_Impl_ConnectionState_control_snapshot snapshot = control_snapshot(c);
  if (snapshot.snapshot_control_tag != expected_tag) {
    fprintf(stderr, "%s left unexpected control tag %u\n",
            label,
            (unsigned)snapshot.snapshot_control_tag);
    return 1;
  }
  return 0;
}

static int expect_no_next_action(
    TLS13_Impl_ConnectionState_connection_state c,
    const char *label) {
  TLS13_Impl_Client_Types_next_local_action action =
      next_local_action(c, 2048, 32, 36);
  if (action.next_local_ready) {
    fprintf(stderr,
            "%s returned unexpected next action kind=%d payload=%d\n",
            label,
            (int)action.next_local_kind,
            (int)action.next_local_payload);
    return 1;
  }
  return 0;
}

static int run_suggested_local_step(
    TLS13_Impl_ConnectionState_connection_state c,
    TLS13_Impl_Client_Types_local_event_kind expected_kind,
    TLS13_Impl_Client_Types_local_payload_kind expected_payload,
    uint8_t *certificate_public_key,
    size_t certificate_public_key_len,
    uint8_t *network_out,
    size_t network_out_len,
    uint8_t *app_out,
    size_t app_out_len,
    TLS13_Impl_Client_Types_client_response *out_resp,
    const char *label) {
  TLS13_Impl_Client_Types_next_local_action action =
      next_local_action(c, network_out_len, certificate_public_key_len, 36);
  if (!action.next_local_ready ||
      action.next_local_kind != expected_kind ||
      action.next_local_payload != expected_payload) {
    fprintf(stderr,
            "%s returned next action ready=%d kind=%d payload=%d\n",
            label,
            (int)action.next_local_ready,
            (int)action.next_local_kind,
            (int)action.next_local_payload);
    return 1;
  }

  uint8_t empty_payload[1] = {0};
  uint8_t stored_finished[36] = {0};
  uint8_t *payload = empty_payload;
  size_t payload_len = 0;

  if (action.next_local_payload ==
      TLS13_Impl_Client_Types_LocalPayloadCertificatePublicKey) {
    payload = certificate_public_key;
    payload_len = certificate_public_key_len;
  } else if (action.next_local_payload ==
             TLS13_Impl_Client_Types_LocalPayloadServerFinishedHandshake) {
    uint8_t verify_data[32] = {0};
    size_t verify_data_len =
        copy_server_finished_verify_data(c, verify_data, sizeof verify_data);
    if (verify_data_len != 32) {
      fprintf(stderr, "%s could not copy server Finished verify_data\n", label);
      return 1;
    }
    stored_finished[0] = 20;
    write_u24(stored_finished + 1, verify_data_len);
    memcpy(stored_finished + 4, verify_data, verify_data_len);
    payload = stored_finished;
    payload_len = sizeof stored_finished;
  }

  TLS13_Impl_Client_Types_client_response resp =
      process_local_event(
          c,
          action.next_local_kind,
          payload,
          payload_len,
          network_out,
          network_out_len,
          app_out,
          app_out_len);
  if (out_resp != NULL) {
    *out_resp = resp;
  }
  return expect_step_ok(resp, label);
}

static int run_network_step(
    TLS13_Impl_ConnectionState_connection_state c,
    uint8_t content_type,
    uint8_t *fragment,
    size_t fragment_len,
    uint8_t expected_stage,
    const char *label) {
  uint8_t raw[512] = {0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  int protected_record = content_type == 22 && expected_stage >= 4;
  size_t record_fragment_len = fragment_len + (protected_record ? 1u : 0u);

  if (record_fragment_len + 6 > sizeof raw) {
    fprintf(stderr, "%s test fragment too large\n", label);
    return 1;
  }
  raw[0] = protected_record ? 23 : content_type;
  raw[1] = 3;
  raw[2] = 3;
  write_u16(raw + 3, (uint16_t)record_fragment_len);
  memcpy(raw + 5, fragment, fragment_len);
  if (protected_record) {
    raw[5 + fragment_len] = content_type;
  }
  raw[5 + record_fragment_len] = 0xa5;

  TLS13_Impl_Client_Types_client_buffer_response buffer_resp =
      process_network_bytes(
          c,
          raw,
          record_fragment_len + 6,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  TLS13_Impl_Client_Types_client_response resp = buffer_resp.response;
  if (expect_step_ok(resp, label) != 0) {
    return 1;
  }
  if (buffer_resp.consumed_len != record_fragment_len + 5) {
    fprintf(stderr, "%s consumed %zu bytes, expected %zu\n",
            label,
            (size_t)buffer_resp.consumed_len,
            record_fragment_len + 5);
    return 1;
  }
  return expect_handshake_stage(c, expected_stage, label);
}

static size_t build_protected_plaintext_record(
    uint8_t *out,
    size_t out_cap,
    const uint8_t *fragment,
    size_t fragment_len,
    uint8_t inner_type) {
  if (fragment_len + 6 > out_cap) {
    return 0;
  }
  out[0] = 23;
  out[1] = 3;
  out[2] = 3;
  write_u16(out + 3, (uint16_t)(fragment_len + 1));
  memcpy(out + 5, fragment, fragment_len);
  out[5 + fragment_len] = inner_type;
  return fragment_len + 6;
}

static int receive_application_stream(
    TLS13_Impl_ConnectionState_connection_state c,
    uint8_t *stream,
    size_t stream_len,
    const uint8_t **expected,
    const size_t *expected_lens,
    size_t expected_count) {
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  size_t offset = 0;

  for (size_t i = 0; i < expected_count; ++i) {
    memset(network_out, 0, sizeof network_out);
    memset(app_out, 0, sizeof app_out);
    TLS13_Impl_Client_Types_client_buffer_response buffer_resp =
        process_network_bytes(
            c,
            stream + offset,
            stream_len - offset,
            network_out,
            sizeof network_out,
            app_out,
            sizeof app_out);
    TLS13_Impl_Client_Types_client_response resp = buffer_resp.response;
    if (expect_step_ok(resp, "ApplicationData stream") != 0 ||
        buffer_resp.consumed_len == 0 ||
        buffer_resp.consumed_len > stream_len - offset ||
        resp.app_out_len != expected_lens[i] ||
        memcmp(app_out, expected[i], expected_lens[i]) != 0 ||
        expect_control_tag(c, 2, "ApplicationData stream") != 0) {
      fprintf(stderr, "ApplicationData stream step %zu failed\n", i);
      return 1;
    }
    offset += buffer_resp.consumed_len;
  }

  if (offset != stream_len) {
    fprintf(stderr, "ApplicationData stream left %zu trailing bytes\n", stream_len - offset);
    return 1;
  }
  return 0;
}

static int receive_close_notify(
    TLS13_Impl_ConnectionState_connection_state c) {
  uint8_t raw[8] = {23, 3, 3, 0, 3, 1, 0, 21};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  TLS13_Impl_Client_Types_client_buffer_response buffer_resp =
      process_network_bytes(
          c,
          raw,
          sizeof raw,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  TLS13_Impl_Client_Types_client_response resp = buffer_resp.response;
  if (expect_step_ok(resp, "CloseNotify") != 0 ||
      buffer_resp.consumed_len != sizeof raw ||
      expect_control_tag(c, 4, "CloseNotify") != 0) {
    fprintf(stderr, "CloseNotify failed\n");
    return 1;
  }
  return 0;
}

static int receive_key_update_not_requested(
    TLS13_Impl_ConnectionState_connection_state c) {
  uint8_t key_update[] = {24, 0, 0, 1, 0};
  uint8_t raw[16] = {0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  size_t raw_len =
      build_protected_plaintext_record(
          raw,
          sizeof raw,
          key_update,
          sizeof key_update,
          22);
  TLS13_Impl_Client_Types_client_buffer_response buffer_resp =
      process_network_bytes(
          c,
          raw,
          raw_len,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  TLS13_Impl_Client_Types_client_response resp = buffer_resp.response;
  if (expect_step_ok(resp, "KeyUpdate-not-requested") != 0 ||
      buffer_resp.consumed_len != raw_len ||
      resp.network_out_len != 0 ||
      resp.app_out_len != 0 ||
      expect_control_tag(c, 2, "KeyUpdate-not-requested") != 0 ||
      expect_no_next_action(c, "KeyUpdate-not-requested next action") != 0) {
    fprintf(stderr, "KeyUpdate-not-requested failed\n");
    return 1;
  }
  return 0;
}

static int receive_key_update_requested(
    TLS13_Impl_ConnectionState_connection_state c) {
  uint8_t key_update[] = {24, 0, 0, 1, 1};
  uint8_t raw[16] = {0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  size_t raw_len =
      build_protected_plaintext_record(
          raw,
          sizeof raw,
          key_update,
          sizeof key_update,
          22);
  TLS13_Impl_Client_Types_client_buffer_response buffer_resp =
      process_network_bytes(
          c,
          raw,
          raw_len,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  TLS13_Impl_Client_Types_client_response resp = buffer_resp.response;
  if (expect_step_ok(resp, "KeyUpdate-requested") != 0 ||
      buffer_resp.consumed_len != raw_len ||
      resp.network_out_len != 0 ||
      resp.app_out_len != 0 ||
      expect_control_tag(c, 2, "KeyUpdate-requested") != 0) {
    fprintf(stderr, "KeyUpdate-requested failed\n");
    return 1;
  }
  return 0;
}

static int test_network_buffer_decode_error(void) {
  TLS13_Impl_ConnectionState_connection_state c = new_client_default();
  uint8_t invalid_record_prefix[1] = {0xff};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  TLS13_Impl_Client_Types_client_buffer_response buffer_resp =
      process_network_bytes(
          c,
          invalid_record_prefix,
          sizeof invalid_record_prefix,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  if (buffer_resp.response.status != TLS13_Impl_Client_Types_DecodeError ||
      buffer_resp.consumed_len != 0 ||
      expect_control_tag(c, 5, "DecodeError") != 0) {
    fprintf(stderr, "DecodeError prefix handling failed\n");
    return 1;
  }
  return 0;
}

static size_t build_server_hello(uint8_t out[90]) {
  memset(out, 0, 90);
  out[0] = 2;
  write_u24(out + 1, 86);
  uint8_t *body = out + 4;
  body[0] = 3;
  body[1] = 3;
  for (size_t i = 0; i < 32; i++) {
    body[2 + i] = (uint8_t)(0xa0u + i);
  }
  body[34] = 0;
  write_u16(body + 35, 0x1303u);
  body[37] = 0;
  write_u16(body + 38, 46);
  size_t pos = 40;
  write_u16(body + pos, 0x0033u);
  write_u16(body + pos + 2, 36);
  write_u16(body + pos + 4, 0x001du);
  write_u16(body + pos + 6, 32);
  body[pos + 8] = 9;
  pos += 40;
  write_u16(body + pos, 0x000au);
  write_u16(body + pos + 2, 2);
  body[pos + 4] = 0;
  body[pos + 5] = 0;
  return 90;
}

static size_t build_empty_encrypted_extensions(uint8_t out[4]) {
  out[0] = 8;
  write_u24(out + 1, 0);
  return 4;
}

static size_t build_certificate(uint8_t out[14]) {
  memset(out, 0, 14);
  out[0] = 11;
  write_u24(out + 1, 10);
  uint8_t *body = out + 4;
  body[0] = 0;
  write_u24(body + 1, 6);
  write_u24(body + 4, 1);
  body[7] = 0x42;
  body[8] = 0;
  body[9] = 0;
  return 14;
}

static size_t build_certificate_verify(uint8_t out[9]) {
  memset(out, 0, 9);
  out[0] = 15;
  write_u24(out + 1, 5);
  uint8_t *body = out + 4;
  write_u16(body, 0x0804u);
  write_u16(body + 2, 1);
  body[4] = 0x5a;
  return 9;
}

static size_t build_expected_finished(
    TLS13_Impl_ConnectionState_connection_state c,
    uint8_t out[36]) {
  TLS13_Impl_ConnectionState_traffic_key_material_storage server_hs =
      c.handshake.keys.server_handshake_traffic;
  if (server_hs.present2 == NULL || !*server_hs.present2 ||
      server_hs.traffic_secret == NULL ||
      c.handshake.transcript.bytes == NULL ||
      c.handshake.transcript.len == NULL) {
    return 0;
  }
  uint8_t transcript_hash[32] = {0};
  TLS13_Crypto_sha256(
      c.handshake.transcript.bytes,
      *c.handshake.transcript.len,
      transcript_hash,
      NULL,
      NULL);
  out[0] = 20;
  write_u24(out + 1, 32);
  TLS13_KeySchedule_finished_verify_data(
      server_hs.traffic_secret,
      transcript_hash,
      out + 4);
  return 36;
}

static int expect_certificate_verify_input(uint8_t *input, size_t input_len) {
  static const char context[] = "TLS 1.3, server CertificateVerify";
  if (input_len != 130) {
    fprintf(stderr, "CertificateVerify input length was %zu\n", input_len);
    return 1;
  }
  for (size_t i = 0; i < 64; i++) {
    if (input[i] != 0x20) {
      fprintf(stderr, "CertificateVerify input prefix failed\n");
      return 1;
    }
  }
  if (memcmp(input + 64, context, sizeof context - 1) != 0 ||
      input[64 + sizeof context - 1] != 0) {
    fprintf(stderr, "CertificateVerify input context failed\n");
    return 1;
  }
  return 0;
}

static TLS13_Impl_ConnectionState_connection_state new_scripted_client(void) {
  uint8_t server_name[] = {'l', 'o', 'c', 'a', 'l', 'h', 'o', 's', 't'};
  uint8_t trust_anchors[] = {0xde, 0xad, 0xbe, 0xef};
  size_t validation_time_seconds = 123456789u;
  return new_client(
      server_name,
      sizeof server_name,
      trust_anchors,
      sizeof trust_anchors,
      validation_time_seconds);
}

static int advance_to_certificate_signature_verified(
    TLS13_Impl_ConnectionState_connection_state c) {
  uint8_t payload[1] = {0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  uint8_t public_key[32] = {0};
  public_key[0] = 9;

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalStartHandshake,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "setup LocalStartHandshake") != 0 ||
      run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalSendClientHello,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "setup LocalSendClientHello") != 0) {
    return 1;
  }

  uint8_t server_hello[90];
  if (run_network_step(
        c,
        22,
        server_hello,
        build_server_hello(server_hello),
        3,
        "setup ServerHello") != 0) {
    return 1;
  }

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalDeriveSharedSecret,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "setup LocalDeriveSharedSecret") != 0 ||
      run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallClientHandshakeTrafficKeys,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "setup LocalInstallClientHandshakeTrafficKeys") != 0 ||
      run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallServerHandshakeTrafficKeys,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "setup LocalInstallServerHandshakeTrafficKeys") != 0) {
    return 1;
  }

  uint8_t encrypted_extensions[4];
  if (run_network_step(
        c,
        22,
        encrypted_extensions,
        build_empty_encrypted_extensions(encrypted_extensions),
        4,
        "setup EncryptedExtensions") != 0) {
    return 1;
  }

  uint8_t certificate[14];
  if (run_network_step(
        c,
        22,
        certificate,
        build_certificate(certificate),
        5,
        "setup Certificate") != 0) {
    return 1;
  }

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalValidateCertificate,
        TLS13_Impl_Client_Types_LocalPayloadCertificatePublicKey,
        public_key,
        sizeof public_key,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "setup LocalValidateCertificate") != 0) {
    return 1;
  }

  uint8_t certificate_verify[9];
  if (run_network_step(
        c,
        22,
        certificate_verify,
        build_certificate_verify(certificate_verify),
        7,
        "setup CertificateVerify") != 0) {
    return 1;
  }

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalVerifyCertificateSignature,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "setup LocalVerifyCertificateSignature") != 0 ||
      expect_handshake_stage(c, 8, "setup certificate signature") != 0) {
    return 1;
  }
  return 0;
}

static int test_bad_server_finished_rejected(void) {
  TLS13_Impl_ConnectionState_connection_state c = new_scripted_client();
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};

  if (advance_to_certificate_signature_verified(c) != 0) {
    return 1;
  }

  uint8_t finished[36];
  size_t finished_len = build_expected_finished(c, finished);
  if (finished_len != sizeof finished) {
    fprintf(stderr, "could not build expected Finished\n");
    return 1;
  }
  finished[4] ^= 0x80u;
  if (run_network_step(
        c,
        22,
        finished,
        finished_len,
        9,
        "bad Finished") != 0) {
    return 1;
  }

  TLS13_Impl_Client_Types_next_local_action action =
      next_local_action(c, sizeof network_out, 0, 36);
  if (!action.next_local_ready ||
      action.next_local_kind != TLS13_Impl_Client_Types_LocalVerifyFinished ||
      action.next_local_payload != TLS13_Impl_Client_Types_LocalPayloadServerFinishedHandshake) {
    fprintf(stderr, "bad Finished next action was not LocalVerifyFinished\n");
    return 1;
  }

  uint8_t verify_data[32] = {0};
  size_t verify_data_len =
      copy_server_finished_verify_data(c, verify_data, sizeof verify_data);
  if (verify_data_len != 32 ||
      memcmp(verify_data, finished + 4, sizeof verify_data) != 0) {
    fprintf(stderr, "bad Finished stored verify_data snapshot failed\n");
    return 1;
  }

  uint8_t payload[36] = {0};
  payload[0] = 20;
  write_u24(payload + 1, verify_data_len);
  memcpy(payload + 4, verify_data, sizeof verify_data);
  TLS13_Impl_Client_Types_client_response resp =
      process_local_event(
          c,
          TLS13_Impl_Client_Types_LocalVerifyFinished,
          payload,
          sizeof payload,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  TLS13_Impl_ConnectionState_control_snapshot snapshot = control_snapshot(c);
  if (resp.status != TLS13_Impl_Client_Types_ConnectionFailed ||
      resp.network_out_len != 0 ||
      resp.app_out_len != 0 ||
      snapshot.snapshot_control_tag != 5 ||
      !snapshot.snapshot_failure_present ||
      snapshot.snapshot_failure_code != 7) {
    fprintf(stderr, "bad Finished was not rejected as BadFinished\n");
    return 1;
  }
  return 0;
}

static int test_client_hello_local_path(void) {
  TLS13_Impl_ConnectionState_connection_state c = new_scripted_client();
  uint8_t payload[1] = {0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};

  uint8_t short_record_prefix[2] = {22, 3};
  TLS13_Impl_Client_Types_client_buffer_response need_more =
      process_network_bytes(
          c,
          short_record_prefix,
          sizeof short_record_prefix,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  if (need_more.response.status != TLS13_Impl_Client_Types_NeedMoreInput ||
      need_more.consumed_len != 0 ||
      need_more.response.network_out_len != 0 ||
      need_more.response.app_out_len != 0 ||
      expect_control_tag(c, 0, "NeedMoreInput") != 0) {
    fprintf(stderr, "NeedMoreInput prefix handling failed\n");
    return 1;
  }

  TLS13_Impl_Client_Types_client_response start;
  if (run_suggested_local_step(
          c,
          TLS13_Impl_Client_Types_LocalStartHandshake,
          TLS13_Impl_Client_Types_LocalPayloadNone,
          payload,
          0,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out,
          &start,
          "LocalStartHandshake") != 0 ||
      start.network_out_len != 0 ||
      expect_handshake_stage(c, 1, "LocalStartHandshake") != 0) {
    fprintf(stderr, "LocalStartHandshake failed\n");
    return 1;
  }

  TLS13_Impl_Client_Types_client_response sent;
  if (run_suggested_local_step(
          c,
          TLS13_Impl_Client_Types_LocalSendClientHello,
          TLS13_Impl_Client_Types_LocalPayloadNone,
          payload,
          0,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out,
          &sent,
          "LocalSendClientHello") != 0) {
    return 1;
  }
  size_t record_len = ((size_t)network_out[3] << 8) | (size_t)network_out[4];
  if (sent.status != TLS13_Impl_Client_Types_StepOk ||
      sent.network_out_len < 5 ||
      sent.network_out_len != record_len + 5 ||
      network_out[0] != 22 ||
      network_out[1] != 3 ||
      network_out[2] != 3 ||
      network_out[5] != 1 ||
      expect_handshake_stage(c, 2, "LocalSendClientHello") != 0) {
    fprintf(stderr, "LocalSendClientHello failed\n");
    return 1;
  }

  if (expect_no_next_action(c, "post-ClientHello next action") != 0) {
    return 1;
  }

  uint8_t server_hello[90];
  size_t server_hello_len = build_server_hello(server_hello);
  if (run_network_step(
        c,
        22,
        server_hello,
        server_hello_len,
        3,
        "ServerHello") != 0) {
    return 1;
  }

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalDeriveSharedSecret,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalDeriveSharedSecret") != 0 ||
    run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallClientHandshakeTrafficKeys,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalInstallClientHandshakeTrafficKeys") != 0 ||
    run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallServerHandshakeTrafficKeys,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalInstallServerHandshakeTrafficKeys") != 0) {
    return 1;
  }

  if (expect_no_next_action(c, "post-handshake-keys next action") != 0) {
    return 1;
  }

  uint8_t encrypted_extensions[4];
  if (run_network_step(
        c,
        22,
        encrypted_extensions,
        build_empty_encrypted_extensions(encrypted_extensions),
        4,
        "EncryptedExtensions") != 0) {
    return 1;
  }

  uint8_t certificate[14];
  if (run_network_step(
        c,
        22,
        certificate,
        build_certificate(certificate),
        5,
        "Certificate") != 0) {
    return 1;
  }

  uint8_t cert_leaf[32768] = {0};
  size_t cert_leaf_len = copy_certificate_leaf_der(c, cert_leaf, sizeof cert_leaf);
  if (cert_leaf_len != 1 || cert_leaf[0] != 0x42) {
    fprintf(stderr, "copy_certificate_leaf_der failed\n");
    return 1;
  }

  uint8_t public_key[32] = {0};
  public_key[0] = 9;
  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalValidateCertificate,
        TLS13_Impl_Client_Types_LocalPayloadCertificatePublicKey,
        public_key,
        sizeof public_key,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalValidateCertificate") != 0 ||
      expect_handshake_stage(c, 6, "LocalValidateCertificate") != 0) {
    fprintf(stderr, "LocalValidateCertificate did not validate certificate\n");
    return 1;
  }

  if (expect_no_next_action(c, "post-certificate-validation next action") != 0) {
    return 1;
  }

  uint8_t certificate_verify[9];
  if (run_network_step(
        c,
        22,
        certificate_verify,
        build_certificate_verify(certificate_verify),
        7,
        "CertificateVerify") != 0) {
    return 1;
  }

  uint8_t cv_signature[4096] = {0};
  TLS13_Impl_ConnectionState_certificate_verify_signature_snapshot cv_sig =
      copy_certificate_verify_signature(c, cv_signature, sizeof cv_signature);
  if (cv_sig.cv_signature_scheme != 0x0804u ||
      cv_sig.cv_signature_len != 1 ||
      cv_signature[0] != 0x5a) {
    fprintf(stderr, "copy_certificate_verify_signature failed\n");
    return 1;
  }

  uint8_t cv_input[256] = {0};
  size_t cv_input_len = copy_certificate_verify_input(c, cv_input, sizeof cv_input);
  if (expect_certificate_verify_input(cv_input, cv_input_len) != 0) {
    return 1;
  }

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalVerifyCertificateSignature,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalVerifyCertificateSignature") != 0 ||
    expect_handshake_stage(c, 8, "LocalVerifyCertificateSignature") != 0) {
    fprintf(stderr, "LocalVerifyCertificateSignature did not verify signature\n");
    return 1;
  }

  if (expect_no_next_action(c, "post-certificate-signature next action") != 0) {
    return 1;
  }

  uint8_t finished[36];
  size_t finished_len = build_expected_finished(c, finished);
  if (finished_len != sizeof finished) {
    fprintf(stderr, "could not build expected Finished\n");
    return 1;
  }
  if (run_network_step(
        c,
        22,
        finished,
        finished_len,
        9,
        "Finished") != 0) {
    return 1;
  }

  uint8_t server_finished_verify_data[32] = {0};
  size_t server_finished_verify_data_len =
      copy_server_finished_verify_data(c, server_finished_verify_data, sizeof server_finished_verify_data);
  if (server_finished_verify_data_len != 32 ||
      memcmp(server_finished_verify_data, finished + 4, 32) != 0) {
    fprintf(stderr, "copy_server_finished_verify_data failed\n");
    return 1;
  }

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalVerifyFinished,
        TLS13_Impl_Client_Types_LocalPayloadServerFinishedHandshake,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalVerifyFinished") != 0 ||
    expect_handshake_stage(c, 10, "LocalVerifyFinished") != 0) {
    fprintf(stderr, "LocalVerifyFinished did not verify Finished\n");
    return 1;
  }

  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallClientApplicationTrafficKeys,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalInstallClientApplicationTrafficKeys") != 0 ||
    run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallServerApplicationTrafficKeys,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        NULL,
        "LocalInstallServerApplicationTrafficKeys") != 0) {
    return 1;
  }

  TLS13_Impl_Client_Types_client_response client_finished;
  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalSendClientFinished,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        &client_finished,
        "LocalSendClientFinished") != 0) {
    return 1;
  }
  if (expect_step_ok(client_finished, "LocalSendClientFinished") != 0 ||
    client_finished.network_out_len != 58 ||
    network_out[0] != 23 ||
    expect_control_tag(c, 2, "LocalSendClientFinished") != 0) {
    fprintf(stderr, "LocalSendClientFinished failed\n");
    return 1;
  }

  if (expect_no_next_action(c, "post-client-finished next action") != 0) {
    return 1;
  }

  uint8_t app_payload[] = {'p', 'i', 'n', 'g'};
  TLS13_Impl_Client_Types_client_response app_sent =
    process_local_event(
        c,
        TLS13_Impl_Client_Types_LocalSendApplicationData,
        app_payload,
        sizeof app_payload,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out);
  if (expect_step_ok(app_sent, "LocalSendApplicationData") != 0 ||
    app_sent.network_out_len != sizeof app_payload + 22 ||
    network_out[0] != 23) {
    fprintf(stderr, "LocalSendApplicationData failed\n");
    return 1;
  }

  uint8_t reply_payload_0[] = {'p', 'o', 'n', 'g'};
  uint8_t reply_payload_1[] = {'a', 'g', 'a', 'i', 'n'};
  uint8_t app_stream[64] = {0};
  size_t app_stream_len = 0;
  size_t app_record_len =
      build_protected_plaintext_record(
          app_stream,
          sizeof app_stream,
          reply_payload_0,
          sizeof reply_payload_0,
          23);
  app_stream_len += app_record_len;
  app_record_len =
      build_protected_plaintext_record(
          app_stream + app_stream_len,
          sizeof app_stream - app_stream_len,
          reply_payload_1,
          sizeof reply_payload_1,
          23);
  app_stream_len += app_record_len;
  const uint8_t *expected_app[] = {reply_payload_0, reply_payload_1};
  const size_t expected_app_lens[] = {sizeof reply_payload_0, sizeof reply_payload_1};
  if (app_stream_len == 0 ||
      receive_application_stream(
        c,
        app_stream,
        app_stream_len,
        expected_app,
        expected_app_lens,
        sizeof expected_app / sizeof expected_app[0]) != 0) {
    return 1;
  }

  if (receive_key_update_not_requested(c) != 0) {
    return 1;
  }

  if (receive_key_update_requested(c) != 0) {
    return 1;
  }

  TLS13_Impl_Client_Types_client_response key_update_sent;
  if (run_suggested_local_step(
        c,
        TLS13_Impl_Client_Types_LocalSendKeyUpdate,
        TLS13_Impl_Client_Types_LocalPayloadNone,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out,
        &key_update_sent,
        "LocalSendKeyUpdate") != 0) {
    return 1;
  }
  if (expect_step_ok(key_update_sent, "LocalSendKeyUpdate") != 0 ||
      key_update_sent.network_out_len != 27 ||
      key_update_sent.app_out_len != 0 ||
      network_out[0] != 23 ||
      expect_control_tag(c, 2, "LocalSendKeyUpdate") != 0 ||
      expect_no_next_action(c, "LocalSendKeyUpdate next action") != 0) {
    fprintf(stderr, "LocalSendKeyUpdate failed\n");
    return 1;
  }

  TLS13_Impl_Client_Types_client_response close_sent =
    process_local_event(
        c,
        TLS13_Impl_Client_Types_LocalSendCloseNotify,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out);
  if (expect_step_ok(close_sent, "LocalSendCloseNotify") != 0 ||
    close_sent.network_out_len <= 5 ||
    network_out[0] != 23 ||
    expect_control_tag(c, 3, "LocalSendCloseNotify") != 0) {
    fprintf(stderr, "LocalSendCloseNotify failed\n");
    return 1;
  }

  if (receive_close_notify(c) != 0) {
    return 1;
  }

  return 0;
}

int main(void) {
  if (test_network_buffer_decode_error() != 0 ||
      test_bad_server_finished_rejected() != 0 ||
      test_client_hello_local_path() != 0) {
    return 1;
  }
  printf("new client binding test passed\n");
  return 0;
}

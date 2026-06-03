#include "TLS13_Impl_Client.h"
#include "TLS13_Impl_Client_Types.h"
#include "TLS13_Impl_ConnectionState.h"

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

static int run_local_step(
    TLS13_Impl_ConnectionState_connection_state c,
    TLS13_Impl_Client_Types_local_event_kind kind,
    uint8_t *payload,
    size_t payload_len,
    const char *label) {
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  TLS13_Impl_Client_Types_client_response resp =
      process_local_event(
          c,
          kind,
          payload,
          payload_len,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
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

  if (fragment_len + 5 > sizeof raw) {
    fprintf(stderr, "%s test fragment too large\n", label);
    return 1;
  }
  raw[0] = content_type;
  raw[1] = 3;
  raw[2] = 3;
  write_u16(raw + 3, (uint16_t)fragment_len);
  memcpy(raw + 5, fragment, fragment_len);

  TLS13_Impl_Client_Types_client_response resp =
      process_network_event(
          c,
          content_type,
          raw,
          fragment_len + 5,
          fragment,
          fragment_len,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  if (expect_step_ok(resp, label) != 0) {
    return 1;
  }
  return expect_handshake_stage(c, expected_stage, label);
}

static int receive_application_data(
    TLS13_Impl_ConnectionState_connection_state c,
    uint8_t *fragment,
    size_t fragment_len,
    const char *label) {
  uint8_t raw[512] = {0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};

  if (fragment_len + 5 > sizeof raw) {
    fprintf(stderr, "%s test fragment too large\n", label);
    return 1;
  }
  raw[0] = 23;
  raw[1] = 3;
  raw[2] = 3;
  write_u16(raw + 3, (uint16_t)fragment_len);
  memcpy(raw + 5, fragment, fragment_len);

  TLS13_Impl_Client_Types_client_response resp =
      process_network_event(
          c,
          23,
          raw,
          fragment_len + 5,
          fragment,
          fragment_len,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  if (expect_step_ok(resp, label) != 0 ||
      resp.app_out_len != fragment_len ||
      memcmp(app_out, fragment, fragment_len) != 0 ||
      expect_control_tag(c, 2, label) != 0) {
    fprintf(stderr, "%s failed\n", label);
    return 1;
  }
  return 0;
}

static int receive_close_notify(
    TLS13_Impl_ConnectionState_connection_state c) {
  uint8_t alert[] = {1, 0};
  uint8_t raw[7] = {21, 3, 3, 0, 2, 1, 0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};
  TLS13_Impl_Client_Types_client_response resp =
      process_network_event(
          c,
          21,
          raw,
          sizeof raw,
          alert,
          sizeof alert,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  if (expect_step_ok(resp, "CloseNotify") != 0 ||
      expect_control_tag(c, 4, "CloseNotify") != 0) {
    fprintf(stderr, "CloseNotify failed\n");
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

static size_t build_finished(uint8_t out[36]) {
  out[0] = 20;
  write_u24(out + 1, 32);
  for (size_t i = 0; i < 32; i++) {
    out[4 + i] = (uint8_t)(0x70u + i);
  }
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

static int test_client_hello_local_path(void) {
  uint8_t server_name[] = {'l', 'o', 'c', 'a', 'l', 'h', 'o', 's', 't'};
  uint8_t trust_anchors[] = {0xde, 0xad, 0xbe, 0xef};
  size_t validation_time_seconds = 123456789u;
  TLS13_Impl_ConnectionState_connection_state c =
      new_client(
          server_name,
          sizeof server_name,
          trust_anchors,
          sizeof trust_anchors,
          validation_time_seconds);
  uint8_t payload[1] = {0};
  uint8_t network_out[2048] = {0};
  uint8_t app_out[16384] = {0};

  TLS13_Impl_Client_Types_client_response start =
      process_local_event(
          c,
          TLS13_Impl_Client_Types_LocalStartHandshake,
          payload,
          0,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
  if (start.status != TLS13_Impl_Client_Types_StepOk ||
      start.network_out_len != 0 ||
      expect_handshake_stage(c, 1, "LocalStartHandshake") != 0) {
    fprintf(stderr, "LocalStartHandshake failed\n");
    return 1;
  }

  TLS13_Impl_Client_Types_client_response sent =
      process_local_event(
          c,
          TLS13_Impl_Client_Types_LocalSendClientHello,
          payload,
          0,
          network_out,
          sizeof network_out,
          app_out,
          sizeof app_out);
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

  if (run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalDeriveSharedSecret,
        payload,
        0,
        "LocalDeriveSharedSecret") != 0 ||
    run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallClientHandshakeTrafficKeys,
        payload,
        0,
        "LocalInstallClientHandshakeTrafficKeys") != 0 ||
    run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallServerHandshakeTrafficKeys,
        payload,
        0,
        "LocalInstallServerHandshakeTrafficKeys") != 0) {
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
  if (run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalValidateCertificate,
        public_key,
        sizeof public_key,
        "LocalValidateCertificate") != 0 ||
      expect_handshake_stage(c, 6, "LocalValidateCertificate") != 0) {
    fprintf(stderr, "LocalValidateCertificate did not validate certificate\n");
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

  if (run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalVerifyCertificateSignature,
        payload,
        0,
        "LocalVerifyCertificateSignature") != 0 ||
    expect_handshake_stage(c, 8, "LocalVerifyCertificateSignature") != 0) {
    fprintf(stderr, "LocalVerifyCertificateSignature did not verify signature\n");
    return 1;
  }

  uint8_t finished[36];
  size_t finished_len = build_finished(finished);
  if (run_network_step(
        c,
        22,
        finished,
        finished_len,
        9,
        "Finished") != 0) {
    return 1;
  }

  if (run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalVerifyFinished,
        finished,
        finished_len,
        "LocalVerifyFinished") != 0 ||
    expect_handshake_stage(c, 10, "LocalVerifyFinished") != 0) {
    fprintf(stderr, "LocalVerifyFinished did not verify Finished\n");
    return 1;
  }

  if (run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallClientApplicationTrafficKeys,
        payload,
        0,
        "LocalInstallClientApplicationTrafficKeys") != 0 ||
    run_local_step(
        c,
        TLS13_Impl_Client_Types_LocalInstallServerApplicationTrafficKeys,
        payload,
        0,
        "LocalInstallServerApplicationTrafficKeys") != 0) {
    return 1;
  }

  TLS13_Impl_Client_Types_client_response client_finished =
    process_local_event(
        c,
        TLS13_Impl_Client_Types_LocalSendClientFinished,
        payload,
        0,
        network_out,
        sizeof network_out,
        app_out,
        sizeof app_out);
  if (expect_step_ok(client_finished, "LocalSendClientFinished") != 0 ||
    client_finished.network_out_len != 58 ||
    network_out[0] != 23 ||
    expect_control_tag(c, 2, "LocalSendClientFinished") != 0) {
    fprintf(stderr, "LocalSendClientFinished failed\n");
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
    app_sent.network_out_len != sizeof app_payload + 21 ||
    network_out[0] != 23) {
    fprintf(stderr, "LocalSendApplicationData failed\n");
    return 1;
  }

  uint8_t reply_payload[] = {'p', 'o', 'n', 'g'};
  if (receive_application_data(
        c,
        reply_payload,
        sizeof reply_payload,
        "ApplicationData") != 0) {
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
  if (test_client_hello_local_path() != 0) {
    return 1;
  }
  printf("new client binding test passed\n");
  return 0;
}

#include "TLS13_Impl_Client.h"
#include "TLS13_Impl_Client_Types.h"
#include "TLS13_Impl_ConnectionState.h"
#include "TLS13_Record.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t *u8s(size_t len) {
  return calloc(len == 0 ? 1 : len, sizeof(uint8_t));
}

static uint16_t *u16s(size_t len) {
  return calloc(len == 0 ? 1 : len, sizeof(uint16_t));
}

static size_t *sizet_box(size_t v) {
  size_t *p = malloc(sizeof *p);
  if (p != NULL) {
    *p = v;
  }
  return p;
}

static bool *bool_box(bool v) {
  bool *p = malloc(sizeof *p);
  if (p != NULL) {
    *p = v;
  }
  return p;
}

static uint8_t *u8_box(uint8_t v) {
  uint8_t *p = malloc(sizeof *p);
  if (p != NULL) {
    *p = v;
  }
  return p;
}

static TLS13_Impl_ConnectionState_sized_bytes sized_bytes(size_t cap) {
  return (TLS13_Impl_ConnectionState_sized_bytes){
      .bytes = u8s(cap),
      .len = sizet_box(0),
  };
}

static TLS13_Impl_ConnectionState_optional_sized_bytes optional_sized_bytes(size_t cap) {
  return (TLS13_Impl_ConnectionState_optional_sized_bytes){
      .present = bool_box(false),
      .value = sized_bytes(cap),
  };
}

static TLS13_Impl_ConnectionState_optional_fixed_bytes optional_fixed32(void) {
  return (TLS13_Impl_ConnectionState_optional_fixed_bytes){
      .present1 = bool_box(false),
      .bytes1 = u8s(32),
  };
}

static TLS13_Impl_ConnectionState_u16_list_storage u16_list(size_t cap) {
  return (TLS13_Impl_ConnectionState_u16_list_storage){
      .items = u16s(cap),
      .len1 = sizet_box(0),
  };
}

static TLS13_Impl_ConnectionState_optional_secret_storage optional_secret(void) {
  return (TLS13_Impl_ConnectionState_optional_secret_storage){
      .present3 = bool_box(false),
      .secret = u8s(32),
  };
}

static TLS13_Impl_ConnectionState_traffic_key_material_storage traffic_key_material(void) {
  return (TLS13_Impl_ConnectionState_traffic_key_material_storage){
      .present2 = bool_box(false),
      .traffic_secret = u8s(32),
      .traffic_key = u8s(32),
      .traffic_iv = u8s(12),
  };
}

static TLS13_Impl_Messages_client_hello client_hello_slot(void) {
  return (TLS13_Impl_Messages_client_hello){
      .client_hello_random = u8s(32),
      .client_hello_server_name = u8s(255),
      .client_hello_server_name_len = 0,
      .client_hello_has_server_name = false,
      .client_hello_key_share = u8s(32),
      .client_hello_cipher_suites = u16s(16),
      .client_hello_cipher_suites_len = 0,
      .client_hello_signature_schemes = u16s(16),
      .client_hello_signature_schemes_len = 0,
  };
}

static TLS13_Impl_ConnectionState_key_schedule_storage key_schedule_storage(void) {
  return (TLS13_Impl_ConnectionState_key_schedule_storage){
      .early_secret = optional_secret(),
      .shared_secret = optional_secret(),
      .handshake_secret = optional_secret(),
      .master_secret = optional_secret(),
      .client_handshake_traffic = traffic_key_material(),
      .server_handshake_traffic = traffic_key_material(),
      .client_application_traffic = traffic_key_material(),
      .server_application_traffic = traffic_key_material(),
      .exporter_master_secret = optional_secret(),
      .resumption_master_secret = optional_secret(),
  };
}

static TLS13_Impl_ConnectionState_connection_state new_client_state(void) {
  TLS13_Impl_ConnectionState_connection_state c;
  memset(&c, 0, sizeof c);

  c.config.role_tag = u8_box(0);
  c.config.server_name = sized_bytes(255);
  memcpy(c.config.server_name.bytes, "localhost", 9);
  *c.config.server_name.len = 9;
  c.config.trust_anchors = sized_bytes(65536);
  c.config.validation_time_seconds = sizet_box(0);
  c.config.cipher_suites = u16_list(16);
  c.config.cipher_suites.items[0] = 0x1303;
  *c.config.cipher_suites.len1 = 1;
  c.config.signature_schemes = u16_list(16);
  c.config.signature_schemes.items[0] = 0x0804;
  *c.config.signature_schemes.len1 = 1;

  c.control.control_tag = u8_box(0);
  c.control.handshake_stage_tag = u8_box(0);
  c.control.failure_present = bool_box(false);
  c.control.failure_code = u8_box(0);
  c.control.failure_alert = u8_box(0);

  c.records.read = TLS13_Record_record_state_new();
  c.records.write = TLS13_Record_record_state_new();

  c.handshake.start.present4 = bool_box(false);
  c.handshake.start.server_name1 = sized_bytes(255);
  c.handshake.start.client_random = u8s(32);
  c.handshake.start.client_key_share_private = optional_fixed32();
  c.handshake.start.client_key_share_public = u8s(32);
  c.handshake.start.cipher_suites1 = u16_list(16);
  c.handshake.start.signature_schemes1 = u16_list(16);

  c.handshake.messages.client_hello_present = bool_box(false);
  c.handshake.messages.client_hello = client_hello_slot();
  c.handshake.messages.server_hello = calloc(1, sizeof *c.handshake.messages.server_hello);
  c.handshake.messages.encrypted_extensions = calloc(1, sizeof *c.handshake.messages.encrypted_extensions);
  c.handshake.messages.certificate = calloc(1, sizeof *c.handshake.messages.certificate);
  c.handshake.messages.certificate_verify = calloc(1, sizeof *c.handshake.messages.certificate_verify);
  c.handshake.messages.server_finished = calloc(1, sizeof *c.handshake.messages.server_finished);
  c.handshake.messages.client_finished = calloc(1, sizeof *c.handshake.messages.client_finished);

  c.handshake.server_key_share = optional_fixed32();
  c.handshake.validated_peer.present5 = bool_box(false);
  c.handshake.validated_peer.validated_hostname = sized_bytes(255);
  c.handshake.validated_peer.leaf_public_key = sized_bytes(4096);
  c.handshake.validated_peer.permitted_signature_schemes = u16_list(16);
  c.handshake.certificate_verify_verified = bool_box(false);
  c.handshake.server_finished_verified = bool_box(false);
  c.handshake.transcript = sized_bytes(65536);
  c.handshake.buffers.client_hello_bytes = sized_bytes(512);
  c.handshake.buffers.server_hello_bytes = sized_bytes(4096);
  c.handshake.buffers.encrypted_server_handshake_bytes = sized_bytes(32768);
  c.handshake.buffers.encrypted_server_handshake_parsed = sizet_box(0);
  c.handshake.buffers.certificate_leaf_der = optional_sized_bytes(4096);
  c.handshake.buffers.certificate_verify_input = optional_sized_bytes(256);
  c.handshake.keys = key_schedule_storage();

  c.application.pending_plaintext = sized_bytes(32768);
  c.application.pending_source_record = sized_bytes(32768);
  c.application.pending_source_offset = sizet_box(0);
  c.application.pending_received_raw = sized_bytes(32768);

  return c;
}

static int test_client_hello_local_path(void) {
  TLS13_Impl_ConnectionState_connection_state c = new_client_state();
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
      *c.control.control_tag != 1 ||
      *c.control.handshake_stage_tag != 1 ||
      !*c.handshake.start.present4) {
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
      *c.control.handshake_stage_tag != 2 ||
      !*c.handshake.messages.client_hello_present ||
      *c.handshake.buffers.client_hello_bytes.len + 5 != sent.network_out_len) {
    fprintf(stderr, "LocalSendClientHello failed\n");
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

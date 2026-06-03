#include "TLS13_Impl_Client.h"
#include "TLS13_Impl_Client_Types.h"
#include "TLS13_Impl_ConnectionState.h"

#include <stdint.h>
#include <stdio.h>

static int test_client_hello_local_path(void) {
  TLS13_Impl_ConnectionState_connection_state c = new_client_default();
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

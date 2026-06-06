#include "TLS13_Impl_Client.h"
#include "TLS13_Impl_Client_Driver.h"
#include "TLS13_Impl_Client_Types.h"
#include "tls13_io_karamel.h"

#include <stdint.h>
#include <stdio.h>

int main(void) {
  TLS13_Impl_ConnectionState_Repr_connection_state client =
      new_client_default();
  TLS13_IO_channel ch = tls13_io_channel_from_fd(-1);
  if (ch == NULL) {
    fprintf(stderr, "failed to allocate TLS13_IO_channel\n");
    return 1;
  }
  driver d = {
      .driver_client = client,
      .driver_channel = ch,
  };

  uint8_t empty_payload[1] = {0};
  uint8_t network_out[1024] = {0};
  uint8_t app_out[1] = {0};

  ready_local_action_result first =
      driver_handshake_step(
          d,
          empty_payload,
          network_out,
          sizeof network_out,
          0,
          0,
          app_out,
          sizeof app_out);
  ready_local_action_result second =
      driver_handshake_step(
          d,
          empty_payload,
          network_out,
          sizeof network_out,
          0,
          0,
          app_out,
          sizeof app_out);

  tls13_io_channel_free(ch);

  if (!first.ready_local_processed) {
    fprintf(stderr, "expected the first local action to be processed\n");
    return 1;
  }
  if (first.ready_local_action.next_local_kind !=
      TLS13_Impl_Client_Types_LocalStartHandshake) {
    fprintf(stderr, "expected LocalStartHandshake as the first action\n");
    return 1;
  }
  if (first.ready_local_resp.status != TLS13_Impl_Client_Types_StepOk) {
    fprintf(stderr, "expected StepOk from first local action\n");
    return 1;
  }
  if (!second.ready_local_processed) {
    fprintf(stderr, "expected the second local action to be processed\n");
    return 1;
  }
  if (second.ready_local_action.next_local_kind !=
      TLS13_Impl_Client_Types_LocalSendClientHello) {
    fprintf(stderr, "expected LocalSendClientHello as the second action\n");
    return 1;
  }
  if (second.ready_local_resp.status != TLS13_Impl_Client_Types_StepOk) {
    fprintf(stderr, "expected StepOk from second local action\n");
    return 1;
  }

  TLS13_Impl_ConnectionState_Repr_connection_state loop_client =
      new_client_default();
  TLS13_IO_channel loop_ch = tls13_io_channel_from_fd(-1);
  if (loop_ch == NULL) {
    fprintf(stderr, "failed to allocate loop TLS13_IO_channel\n");
    return 1;
  }
  driver loop_driver = {
      .driver_client = loop_client,
      .driver_channel = loop_ch,
  };
  uint8_t loop_empty_payload[1] = {0};
  uint8_t loop_network_out[1024] = {0};
  uint8_t loop_app_out[1] = {0};
  driver_drain_result drain =
      driver_drain_local_actions(
          loop_driver,
          loop_empty_payload,
          loop_network_out,
          sizeof loop_network_out,
          0,
          0,
          loop_app_out,
          sizeof loop_app_out,
          2);
  tls13_io_channel_free(loop_ch);
  if (!drain.driver_drain_exhausted) {
    fprintf(stderr, "expected bounded local drain to exhaust its fuel\n");
    return 1;
  }
  if (drain.driver_drain_last.ready_local_processed) {
    fprintf(stderr, "expected exhausted drain to return an unprocessed final step\n");
    return 1;
  }

  TLS13_Impl_ConnectionState_Repr_connection_state buffered_client =
      new_client_default();
  TLS13_IO_channel buffered_ch = tls13_io_channel_from_fd(-1);
  if (buffered_ch == NULL) {
    fprintf(stderr, "failed to allocate buffered TLS13_IO_channel\n");
    return 1;
  }
  driver buffered_driver = {
      .driver_client = buffered_client,
      .driver_channel = buffered_ch,
  };
  uint8_t buffered_raw[64] = {0};
  uint8_t buffered_network_out[1024] = {0};
  uint8_t buffered_app_out[16384] = {0};
  buffered_network_result buffered_result =
      driver_process_buffered_network_bytes_compact_once(
          buffered_driver,
          buffered_raw,
          sizeof buffered_raw,
          0,
          buffered_network_out,
          sizeof buffered_network_out,
          buffered_app_out,
          sizeof buffered_app_out);
  buffered_network_loop_result buffered_loop =
      driver_process_buffered_network_records(
          buffered_driver,
          buffered_raw,
          sizeof buffered_raw,
          0,
          buffered_network_out,
          sizeof buffered_network_out,
          buffered_app_out,
          sizeof buffered_app_out,
          1);
  tls13_io_channel_free(buffered_ch);
  if (buffered_result.buffered_network_read.network_read_len != 0 ||
      buffered_result.buffered_network_new_len != 0) {
    fprintf(stderr, "expected empty buffered prefix length\n");
    return 1;
  }
  if (buffered_result.buffered_network_read.network_read_buffer_resp.response.status !=
      TLS13_Impl_Client_Types_NeedMoreInput) {
    fprintf(stderr, "expected empty buffered prefix to need more input\n");
    return 1;
  }
  if (buffered_loop.buffered_network_loop_exhausted ||
      buffered_loop.buffered_network_loop_last.buffered_network_new_len != 0) {
    fprintf(stderr, "expected empty buffered loop to stop without exhaustion\n");
    return 1;
  }

  TLS13_Impl_ConnectionState_Repr_connection_state read_client =
      new_client_default();
  TLS13_IO_channel read_ch = tls13_io_channel_from_fd(-1);
  if (read_ch == NULL) {
    fprintf(stderr, "failed to allocate read TLS13_IO_channel\n");
    return 1;
  }
  driver read_driver = {
      .driver_client = read_client,
      .driver_channel = read_ch,
  };
  uint8_t read_raw[64] = {0};
  uint8_t read_network_out[1024] = {0};
  uint8_t read_app_out[16384] = {0};
  network_read_result read_result =
      driver_read_application_data_once(
          read_driver,
          read_raw,
          sizeof read_raw,
          read_network_out,
          sizeof read_network_out,
          read_app_out,
          sizeof read_app_out);
  buffered_network_io_result read_buffered_result =
      driver_read_buffered_network_bytes_compact_once(
          read_driver,
          read_raw,
          sizeof read_raw,
          0,
          read_network_out,
          sizeof read_network_out,
          read_app_out,
          sizeof read_app_out);
  tls13_io_channel_free(read_ch);
  if (read_result.network_read_len != 0) {
    fprintf(stderr, "expected failed test fd read to return zero bytes\n");
    return 1;
  }
  if (read_buffered_result.buffered_network_io_read_len != 0 ||
      read_buffered_result.buffered_network_io_buffered.buffered_network_new_len != 0 ||
      read_buffered_result.buffered_network_io_buffered.buffered_network_read
              .network_read_buffer_resp.response.status != TLS13_Impl_Client_Types_NeedMoreInput) {
    fprintf(stderr, "expected failed buffered test fd read to need more input\n");
    return 1;
  }

  printf("extracted Pulse driver slice test passed\n");
  return 0;
}

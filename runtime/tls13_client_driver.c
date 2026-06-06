#include "tls13_client_driver.h"

#include "TLS13_Impl_Client_Driver.h"
#include "TLS13_Impl_Client_Types.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLS13_DRIVER_NETWORK_OUT_CAP 20000u
#define TLS13_DRIVER_APP_OUT_CAP 16384u
#define TLS13_DRIVER_RX_CAP 65536u
#define TLS13_DRIVER_HANDSHAKE_FUEL 1000u
#define TLS13_DRIVER_LOCAL_FUEL 100u
#define TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP 4096u
#define TLS13_DRIVER_AUTH_LEAF_DER_CAP 32768u
#define TLS13_DRIVER_CERTIFICATE_VERIFY_INPUT_CAP 256u
#define TLS13_DRIVER_SIGNATURE_CAP 4096u
#define TLS13_DRIVER_SERVER_FINISHED_PAYLOAD_LEN 36u

struct tls13_client_driver_s {
  top_driver verified_driver;
  bool channel_open;
  uint8_t network_out[TLS13_DRIVER_NETWORK_OUT_CAP];
  uint8_t app_out[TLS13_DRIVER_APP_OUT_CAP];
  uint8_t rx[TLS13_DRIVER_RX_CAP];
  size_t rx_len;
  uint8_t auth_leaf_der[TLS13_DRIVER_AUTH_LEAF_DER_CAP];
  uint8_t auth_payload[TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP];
  uint8_t auth_cv_input[TLS13_DRIVER_CERTIFICATE_VERIFY_INPUT_CAP];
  uint8_t auth_signature[TLS13_DRIVER_SIGNATURE_CAP];
  char last_error[256];
};

static int driver_fail(tls13_client_driver *driver, const char *fmt, ...) {
  if (driver != NULL && fmt != NULL) {
    va_list ap;
    va_start(ap, fmt);
    (void)vsnprintf(driver->last_error, sizeof driver->last_error, fmt, ap);
    va_end(ap);
  }
  return 1;
}

static void clear_work_buffers(tls13_client_driver *driver) {
  memset(driver->network_out, 0, sizeof driver->network_out);
  memset(driver->app_out, 0, sizeof driver->app_out);
  memset(driver->auth_leaf_der, 0, sizeof driver->auth_leaf_der);
  memset(driver->auth_payload, 0, sizeof driver->auth_payload);
  memset(driver->auth_cv_input, 0, sizeof driver->auth_cv_input);
  memset(driver->auth_signature, 0, sizeof driver->auth_signature);
}

static int check_local_write_result(
    tls13_client_driver *driver,
    local_write_result result,
    const char *label) {
  TLS13_Impl_Client_Types_client_response response = result.local_write_resp;
  if (response.status != TLS13_Impl_Client_Types_StepOk) {
    return driver_fail(driver, "%s returned status %u", label, (unsigned)response.status);
  }
  if (response.network_out_len > sizeof driver->network_out ||
      response.app_out_len > sizeof driver->app_out) {
    return driver_fail(driver, "%s returned out-of-range lengths", label);
  }
  if (result.local_write_written != response.network_out_len) {
    return driver_fail(
        driver,
        "%s wrote %zu of %zu network bytes",
        label,
        result.local_write_written,
        response.network_out_len);
  }
  return 0;
}

static int workflow_failed(
    tls13_client_driver *driver,
    const char *label,
    driver_workflow_result result) {
  TLS13_Impl_Client_Types_client_response local =
      result.driver_workflow_local.driver_drain_last.ready_local_resp;
  TLS13_Impl_Client_Types_client_buffer_response network =
      result.driver_workflow_network.buffered_network_io_buffered.buffered_network_read
          .network_read_buffer_resp;
  return driver_fail(
      driver,
      "%s returned workflow status %u local status %u network status %u buffered=%zu",
      label,
      (unsigned)result.driver_workflow_status,
      (unsigned)local.status,
      (unsigned)network.response.status,
      result.driver_workflow_rx_len);
}

static driver_workflow_result run_handshake_workflow(tls13_client_driver *driver, size_t fuel) {
  uint8_t empty_payload[1] = {0};
  clear_work_buffers(driver);
  return driver_handshake(
      driver->verified_driver,
      empty_payload,
      driver->rx,
      sizeof driver->rx,
      driver->rx_len,
      driver->network_out,
      sizeof driver->network_out,
      driver->auth_leaf_der,
      sizeof driver->auth_leaf_der,
      driver->auth_payload,
      driver->auth_cv_input,
      sizeof driver->auth_cv_input,
      driver->auth_signature,
      sizeof driver->auth_signature,
      TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP,
      TLS13_DRIVER_SERVER_FINISHED_PAYLOAD_LEN,
      driver->app_out,
      sizeof driver->app_out,
      TLS13_DRIVER_LOCAL_FUEL,
      fuel);
}

static driver_workflow_result run_receive_workflow(tls13_client_driver *driver, size_t fuel) {
  uint8_t empty_payload[1] = {0};
  clear_work_buffers(driver);
  return driver_receive_application_data(
      driver->verified_driver,
      empty_payload,
      driver->rx,
      sizeof driver->rx,
      driver->rx_len,
      driver->network_out,
      sizeof driver->network_out,
      driver->auth_leaf_der,
      sizeof driver->auth_leaf_der,
      driver->auth_payload,
      driver->auth_cv_input,
      sizeof driver->auth_cv_input,
      driver->auth_signature,
      sizeof driver->auth_signature,
      TLS13_DRIVER_PUBLIC_KEY_PAYLOAD_CAP,
      TLS13_DRIVER_SERVER_FINISHED_PAYLOAD_LEN,
      driver->app_out,
      sizeof driver->app_out,
      TLS13_DRIVER_LOCAL_FUEL,
      fuel);
}

int tls13_client_driver_connect(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds) {
  if (out == NULL || connect_host == NULL || server_name == NULL ||
      (trust_anchor_pem == NULL && trust_anchor_pem_len != 0u)) {
    return 1;
  }
  *out = NULL;
  tls13_client_driver *driver = calloc(1, sizeof *driver);
  if (driver == NULL) {
    return 1;
  }

  size_t connect_host_len = strlen(connect_host);
  size_t server_name_len = strlen(server_name);
  if (connect_host_len == 0u || server_name_len == 0u) {
    free(driver);
    return 1;
  }

  FStar_Pervasives_Native_option__TLS13_Impl_Client_Driver_top_driver opened =
      driver_open(
          (uint8_t *)connect_host,
          connect_host_len,
          port,
          (uint8_t *)server_name,
          server_name_len,
          (uint8_t *)trust_anchor_pem,
          trust_anchor_pem_len,
          validation_time_seconds);
  if (opened.tag != FStar_Pervasives_Native_Some) {
    driver_fail(
        driver,
        "verified driver open to %s:%u failed",
        connect_host,
        (unsigned)port);
    free(driver);
    return 1;
  }

  driver->verified_driver = opened.v;
  driver->channel_open = true;
  *out = driver;
  return 0;
}

int tls13_client_driver_handshake(tls13_client_driver *driver) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->channel_open) {
    return driver_fail(driver, "TLS channel is closed");
  }

  driver_workflow_result result = run_handshake_workflow(driver, TLS13_DRIVER_HANDSHAKE_FUEL);
  driver->rx_len = result.driver_workflow_rx_len;
  if (result.driver_workflow_status != DriverWorkflowOk) {
    return workflow_failed(driver, "verified handshake workflow", result);
  }
  return 0;
}

int tls13_client_driver_send_application_data(
    tls13_client_driver *driver,
    const uint8_t *payload,
    size_t payload_len) {
  if (driver == NULL || (payload == NULL && payload_len != 0u)) {
    return 1;
  }
  if (!driver->channel_open) {
    return driver_fail(driver, "TLS channel is closed");
  }

  clear_work_buffers(driver);
  local_write_result result =
      top_driver_send_application_data(
          driver->verified_driver,
          (uint8_t *)payload,
          payload_len,
          driver->network_out,
          sizeof driver->network_out,
          driver->app_out,
          sizeof driver->app_out);
  return check_local_write_result(driver, result, "LocalSendApplicationData");
}

int tls13_client_driver_receive_application_data(
    tls13_client_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len) {
  if (driver == NULL || out == NULL || out_len == NULL) {
    return 1;
  }
  if (!driver->channel_open) {
    return driver_fail(driver, "TLS channel is closed");
  }
  *out_len = 0u;

  driver_workflow_result result = run_receive_workflow(driver, TLS13_DRIVER_HANDSHAKE_FUEL);
  driver->rx_len = result.driver_workflow_rx_len;
  if (result.driver_workflow_status != DriverWorkflowOk) {
    return workflow_failed(driver, "verified receive workflow", result);
  }

  TLS13_Impl_Client_Types_client_response response =
      result.driver_workflow_network.buffered_network_io_buffered.buffered_network_read
          .network_read_buffer_resp.response;
  if (response.app_out_len > out_cap) {
    return driver_fail(
        driver,
        "application output buffer too small: need %zu bytes",
        response.app_out_len);
  }
  memcpy(out, driver->app_out, response.app_out_len);
  *out_len = response.app_out_len;
  return 0;
}

int tls13_client_driver_close(tls13_client_driver *driver, bool wait_for_peer) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->channel_open) {
    return 0;
  }

  uint8_t empty_payload[1] = {0};
  clear_work_buffers(driver);
  driver_workflow_result result =
      driver_close_workflow(
          driver->verified_driver,
          wait_for_peer,
          empty_payload,
          driver->rx,
          sizeof driver->rx,
          driver->rx_len,
          driver->network_out,
          sizeof driver->network_out,
          driver->app_out,
          sizeof driver->app_out,
          TLS13_DRIVER_HANDSHAKE_FUEL);
  driver->rx_len = result.driver_workflow_rx_len;
  driver->channel_open = false;
  if (result.driver_workflow_status != DriverWorkflowClosed) {
    return workflow_failed(driver, "verified close workflow", result);
  }
  return 0;
}

const char *tls13_client_driver_last_error(const tls13_client_driver *driver) {
  if (driver == NULL || driver->last_error[0] == '\0') {
    return "no driver error";
  }
  return driver->last_error;
}

void tls13_client_driver_free(tls13_client_driver *driver) {
  if (driver == NULL) {
    return;
  }
  if (driver->channel_open) {
    (void)tls13_client_driver_close(driver, false);
  }
  free(driver);
}

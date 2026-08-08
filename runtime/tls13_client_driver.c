#include "tls13_client_driver.h"

#include "TLS13_Impl_Client_Driver.h"
#include "atlas_trace.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLS13_DRIVER_WORKFLOW_FUEL ((size_t)1000u)
#define TLS13_DRIVER_LOCAL_FUEL ((size_t)100u)

#define TLS13_CLIENT_MAX_SERVER_NAME_LEN ((size_t)255u)
#define TLS13_CLIENT_MAX_TRUST_ANCHORS_LEN ((size_t)65535u)

struct tls13_client_driver_s {
  TLS13_Impl_Client_Driver_client_driver verified_driver;
  bool connected;
#if ATLAS_ENABLE_LOGGING
  uint64_t trace_connection;
#endif
  char last_error[256];
};

struct tls13_client_config_s {
  TLS13_Impl_Client_Driver_client_auth_config verified_config;
  uint8_t *server_name;
  size_t server_name_len;
  uint8_t *trust_anchor_pem;
  size_t trust_anchor_pem_len;
  size_t validation_time_seconds;
};

static int driver_fail(tls13_client_driver *driver, const char *message) {
  if (driver != NULL && message != NULL) {
    (void)snprintf(driver->last_error, sizeof driver->last_error, "%s", message);
  }
  return 1;
}

static const char *driver_status_message(
    TLS13_Impl_Client_Driver_driver_workflow_status status) {
  switch (status) {
    case TLS13_Impl_Client_Driver_State_DriverWorkflowOk:
      return "ok";
    case TLS13_Impl_Client_Driver_State_DriverWorkflowNeedMoreInput:
      return "needs more input";
    case TLS13_Impl_Client_Driver_State_DriverWorkflowStepFailed:
      return "verified protocol step failed";
    case TLS13_Impl_Client_Driver_State_DriverWorkflowExhausted:
      return "workflow exhausted fuel";
    case TLS13_Impl_Client_Driver_State_DriverWorkflowClosed:
      return "TLS channel closed";
    case TLS13_Impl_Client_Driver_State_DriverWorkflowPayloadTooLarge:
      return "payload exceeds the single-record limit (16384 bytes)";
    case TLS13_Impl_Client_Driver_State_DriverWorkflowOutputBufferTooSmall:
      return "output buffer is smaller than the maximum TLS record plaintext";
    default:
      return "unknown verified driver status";
  }
}

static int driver_fail_status(
    tls13_client_driver *driver,
    const char *operation,
    TLS13_Impl_Client_Driver_driver_workflow_status status) {
  if (driver != NULL) {
    (void)snprintf(
        driver->last_error,
        sizeof driver->last_error,
        "%s: %s",
        operation,
        driver_status_message(status));
  }
  return 1;
}

static void abort_connected_driver(tls13_client_driver *driver) {
  if (driver != NULL && driver->connected) {
    atlas_trace_set_connection(driver->trace_connection);
    TLS13_Impl_Client_Driver_abort(driver->verified_driver);
    driver->connected = false;
  }
}

int tls13_client_config_new(
    tls13_client_config **out,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds) {
  if (out == NULL) {
    return 1;
  }
  *out = NULL;
  if (server_name == NULL ||
      (trust_anchor_pem == NULL && trust_anchor_pem_len != 0u)) {
    return 1;
  }

  size_t server_name_len = strlen(server_name);
  if (server_name_len == 0u ||
      server_name_len > TLS13_CLIENT_MAX_SERVER_NAME_LEN ||
      trust_anchor_pem_len > TLS13_CLIENT_MAX_TRUST_ANCHORS_LEN) {
    return 1;
  }

  tls13_client_config *config = calloc(1u, sizeof *config);
  uint8_t *server_name_copy = malloc(server_name_len);
  uint8_t *trust_anchor_copy =
      malloc(trust_anchor_pem_len == 0u ? 1u : trust_anchor_pem_len);
  if (config == NULL || server_name_copy == NULL ||
      trust_anchor_copy == NULL) {
    free(trust_anchor_copy);
    free(server_name_copy);
    free(config);
    return 1;
  }
  memcpy(server_name_copy, server_name, server_name_len);
  if (trust_anchor_pem_len != 0u) {
    memcpy(trust_anchor_copy, trust_anchor_pem, trust_anchor_pem_len);
  }

  config->verified_config = TLS13_Impl_Client_Driver_new_auth_config(
      server_name_copy,
      server_name_len,
      trust_anchor_copy,
      trust_anchor_pem_len,
      validation_time_seconds);
  config->server_name = server_name_copy;
  config->server_name_len = server_name_len;
  config->trust_anchor_pem = trust_anchor_copy;
  config->trust_anchor_pem_len = trust_anchor_pem_len;
  config->validation_time_seconds = validation_time_seconds;
  *out = config;
  return 0;
}

void tls13_client_config_free(tls13_client_config *config) {
  if (config == NULL) {
    return;
  }
  TLS13_Impl_Client_Driver_free_auth_config(config->verified_config);
  free(config->trust_anchor_pem);
  free(config->server_name);
  free(config);
}

static int connect_with_config_reporting(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const tls13_client_config *config,
    char *error_out,
    size_t error_cap) {
  if (error_out != NULL && error_cap != 0u) {
    error_out[0] = '\0';
  }
  if (out == NULL) {
    return 1;
  }
  *out = NULL;
  if (connect_host == NULL || config == NULL) {
    return 1;
  }

  size_t connect_host_len = strlen(connect_host);
  if (connect_host_len == 0u) {
    return 1;
  }

  tls13_client_driver *driver = calloc(1u, sizeof *driver);
  if (driver == NULL) {
    return 1;
  }
#if ATLAS_ENABLE_LOGGING
  driver->trace_connection = atlas_trace_new_connection();
  atlas_trace_set_connection(driver->trace_connection);
#endif

  driver->verified_driver =
      TLS13_Impl_Client_Driver_new_client_with_auth_config(
          config->verified_config,
          config->server_name,
          config->server_name_len,
          config->trust_anchor_pem,
          config->trust_anchor_pem_len,
          config->validation_time_seconds);

  TLS13_Impl_Client_Driver_driver_workflow_status status =
      TLS13_Impl_Client_Driver_connect(
          driver->verified_driver,
          (uint8_t *)(void *)connect_host,
          connect_host_len,
          port,
          TLS13_DRIVER_LOCAL_FUEL,
          TLS13_DRIVER_WORKFLOW_FUEL);
  if (status != TLS13_Impl_Client_Driver_State_DriverWorkflowOk) {
    (void)driver_fail_status(driver, "connect", status);
    if (error_out != NULL && error_cap != 0u) {
      (void)snprintf(error_out, error_cap, "%s", driver->last_error);
    }
    TLS13_Impl_Client_Driver_free(driver->verified_driver);
    free(driver);
    return 1;
  }

  driver->connected = true;
  *out = driver;
  return 0;
}

int tls13_client_driver_connect_with_config(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const tls13_client_config *config) {
  return connect_with_config_reporting(out, connect_host, port, config, NULL, 0u);
}

int tls13_client_driver_connect_reporting(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds,
    char *error_out,
    size_t error_cap) {
  if (error_out != NULL && error_cap != 0u) {
    error_out[0] = '\0';
  }
  tls13_client_config *config = NULL;
  if (tls13_client_config_new(
          &config,
          server_name,
          trust_anchor_pem,
          trust_anchor_pem_len,
          validation_time_seconds) != 0) {
    if (out != NULL) {
      *out = NULL;
    }
    if (error_out != NULL && error_cap != 0u) {
      (void)snprintf(error_out, error_cap, "%s",
                     "client config rejected (hostname or trust store too large)");
    }
    return 1;
  }
  int result = connect_with_config_reporting(
      out, connect_host, port, config, error_out, error_cap);
  tls13_client_config_free(config);
  return result;
}

int tls13_client_driver_connect(
    tls13_client_driver **out,
    const char *connect_host,
    uint16_t port,
    const char *server_name,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    size_t validation_time_seconds) {
  return tls13_client_driver_connect_reporting(
      out, connect_host, port, server_name, trust_anchor_pem,
      trust_anchor_pem_len, validation_time_seconds, NULL, 0u);
}

int tls13_client_driver_send_application_data(
    tls13_client_driver *driver,
    const uint8_t *payload,
    size_t payload_len) {
  if (driver == NULL) {
    return 1;
  }
  if (payload == NULL && payload_len != 0u) {
    return driver_fail(driver, "send: payload is null");
  }
  if (!driver->connected) {
    return driver_fail(driver, "send: TLS channel is closed");
  }

  /* The verified [send] entry point is total for any [payload_len]: it
   * performs the authoritative single-record (<=16384 byte) length test
   * itself and reports [DriverWorkflowPayloadTooLarge] rather than sending
   * an oversized payload, so this wrapper submits the caller's buffer
   * directly with no C-side fragmentation or length pre-check. */
  uint8_t empty_payload = 0u;
  uint8_t *payload_input =
      payload_len == 0u ? &empty_payload : (uint8_t *)(void *)payload;
  atlas_trace_set_connection(driver->trace_connection);
  TLS13_Impl_Client_Driver_driver_workflow_status status =
      TLS13_Impl_Client_Driver_send(
          driver->verified_driver, payload_input, payload_len);
  if (status == TLS13_Impl_Client_Driver_State_DriverWorkflowOk) {
    return 0;
  }
  (void)driver_fail_status(driver, "send", status);
  if (status == TLS13_Impl_Client_Driver_State_DriverWorkflowPayloadTooLarge) {
    /* The verified contract preserves the connected, application-ready state
     * and the exact sent/received logs for this outcome, so the connection
     * remains usable: the caller may retry with a payload split into
     * single-record (<=16384 byte) chunks. */
    return 1;
  }
  driver->connected = false;
  return 1;
}

int tls13_client_driver_send_key_update(
    tls13_client_driver *driver,
    bool request_peer_update) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return driver_fail(driver, "key_update: TLS channel is closed");
  }

  atlas_trace_set_connection(driver->trace_connection);
  TLS13_Impl_Client_Driver_driver_workflow_status status =
      TLS13_Impl_Client_Driver_send_key_update(
          driver->verified_driver, request_peer_update);
  if (status == TLS13_Impl_Client_Driver_State_DriverWorkflowOk) {
    return 0;
  }
  (void)driver_fail_status(driver, "key_update", status);
  driver->connected = false;
  return 1;
}

static bool receive_status_is_retryable(
    TLS13_Impl_Client_Driver_driver_workflow_status status) {
  return status == TLS13_Impl_Client_Driver_State_DriverWorkflowNeedMoreInput ||
         status == TLS13_Impl_Client_Driver_State_DriverWorkflowExhausted ||
         status ==
             TLS13_Impl_Client_Driver_State_DriverWorkflowOutputBufferTooSmall;
}

int tls13_client_driver_receive_application_data(
    tls13_client_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len) {
  if (driver == NULL) {
    return 1;
  }
  if (out == NULL || out_len == NULL) {
    return driver_fail(driver, "receive: invalid output buffer");
  }
  if (!driver->connected) {
    return driver_fail(driver, "receive: TLS channel is closed");
  }
  *out_len = 0u;

  atlas_trace_set_connection(driver->trace_connection);
  TLS13_Impl_Client_Driver_client_receive_result result =
      TLS13_Impl_Client_Driver_receive(
          driver->verified_driver,
          out,
          out_cap,
          TLS13_DRIVER_LOCAL_FUEL,
          TLS13_DRIVER_WORKFLOW_FUEL);
  *out_len = result.client_receive_len;
  if (result.client_receive_status ==
      TLS13_Impl_Client_Driver_State_DriverWorkflowOk) {
    return 0;
  }
  (void)driver_fail_status(driver, "receive", result.client_receive_status);
  if (receive_status_is_retryable(result.client_receive_status)) {
    /* The verified receive contract preserves application readiness for these
     * bounded-progress outcomes, so callers may retry. */
    return 1;
  }
  driver->connected = false;
  return 1;
}

int tls13_client_driver_close(
    tls13_client_driver *driver,
    bool wait_for_peer_close_notify) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return 0;
  }

  atlas_trace_set_connection(driver->trace_connection);
  TLS13_Impl_Client_Driver_driver_workflow_status status =
      TLS13_Impl_Client_Driver_close(
          driver->verified_driver,
          wait_for_peer_close_notify,
          TLS13_DRIVER_WORKFLOW_FUEL);
  driver->connected = false;
  if (status != TLS13_Impl_Client_Driver_State_DriverWorkflowClosed) {
    return driver_fail_status(driver, "close", status);
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
  if (driver->connected) {
    abort_connected_driver(driver);
  }
  atlas_trace_set_connection(driver->trace_connection);
  TLS13_Impl_Client_Driver_free(driver->verified_driver);
  free(driver);
}

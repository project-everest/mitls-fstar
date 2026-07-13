#include "tls13_client_driver.h"

#include "Common_TCP.h"
#include "TLS13_Impl_Client_Driver.h"
#include "TLS13_Impl_Client_Endpoint.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__GNUC__)
extern void krmlinit_globals(void) __attribute__((weak));
#else
extern void krmlinit_globals(void);
#endif

#define TLS13_DRIVER_WORKFLOW_FUEL 1000u
#define TLS13_DRIVER_LOCAL_FUEL 100u

#define TLS13_CLIENT_NETWORK_OUT_CAP 20000u
#define TLS13_CLIENT_APP_OUT_CAP 16640u
#define TLS13_CLIENT_RX_CAP 65535u
#define TLS13_CLIENT_PUBLIC_KEY_PAYLOAD_CAP 4096u
#define TLS13_CLIENT_AUTH_LEAF_DER_CAP 32768u
#define TLS13_CLIENT_CERT_VERIFY_INPUT_CAP 256u
#define TLS13_CLIENT_SIGNATURE_CAP 4096u
#define TLS13_CLIENT_SERVER_FINISHED_PAYLOAD_LEN 36u

struct tls13_client_driver_s {
  TLS13_Impl_Client_Driver_client_driver verified_driver;
  Common_TCP_channel channel;
  bool connected;
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

static void ensure_krml_globals_initialized(void) {
  static bool initialized = false;
  if (!initialized) {
    initialized = true;
#if defined(__GNUC__)
    if (krmlinit_globals != NULL) {
      krmlinit_globals();
    }
#else
    krmlinit_globals();
#endif
  }
}

static TLS13_Impl_Client_CanonicalQueries_client_next_local_action_config
client_endpoint_config(void) {
  return (TLS13_Impl_Client_CanonicalQueries_client_next_local_action_config){
      .client_query_network_out_len = TLS13_CLIENT_NETWORK_OUT_CAP,
      .client_query_certificate_public_key_len =
          TLS13_CLIENT_PUBLIC_KEY_PAYLOAD_CAP,
      .client_query_server_finished_payload_len =
          TLS13_CLIENT_SERVER_FINISHED_PAYLOAD_LEN,
  };
}

static TLS13_Impl_Client_Endpoint_client_endpoint_frame client_endpoint_frame(
    TLS13_Impl_Client_Driver_client_driver d,
    uint8_t *app_out,
    size_t app_out_len,
    uint8_t *local_payload,
    size_t local_payload_len,
    uint8_t *local_app_out,
    size_t local_app_out_len) {
  return (TLS13_Impl_Client_Endpoint_client_endpoint_frame){
      .client_ep_query =
          {
              .client_query_network_app_out = app_out,
              .client_query_network_app_out_len = app_out_len,
              .client_query_local_payload = local_payload,
              .client_query_local_payload_len = local_payload_len,
              .client_query_local_app_out = local_app_out,
              .client_query_local_app_out_len = local_app_out_len,
          },
      .client_ep_raw_len = TLS13_CLIENT_RX_CAP,
      .client_ep_raw = d.client_driver_raw,
      .client_ep_network_out_len = TLS13_CLIENT_NETWORK_OUT_CAP,
      .client_ep_network_out = d.client_driver_network_out,
      .client_ep_auth = d.client_driver_auth,
      .client_ep_auth_leaf_der_len = TLS13_CLIENT_AUTH_LEAF_DER_CAP,
      .client_ep_auth_leaf_der = d.client_driver_auth_leaf_der,
      .client_ep_auth_payload_len = TLS13_CLIENT_PUBLIC_KEY_PAYLOAD_CAP,
      .client_ep_auth_payload = d.client_driver_auth_payload,
      .client_ep_auth_cv_input_len = TLS13_CLIENT_CERT_VERIFY_INPUT_CAP,
      .client_ep_auth_cv_input = d.client_driver_auth_cv_input,
      .client_ep_auth_signature_len = TLS13_CLIENT_SIGNATURE_CAP,
      .client_ep_auth_signature = d.client_driver_auth_signature,
  };
}

static void client_set_channel(
    TLS13_Impl_Client_Driver_client_driver *d,
    Common_TCP_channel ch) {
  if (d != NULL && d->client_driver_channel != NULL) {
    *d->client_driver_channel =
        (FStar_Pervasives_Native_option__Common_TCP_channel){
            .tag = FStar_Pervasives_Native_Some,
            .v = ch,
        };
  }
}

static void client_clear_channel(TLS13_Impl_Client_Driver_client_driver *d) {
  if (d != NULL && d->client_driver_channel != NULL) {
    *d->client_driver_channel =
        (FStar_Pervasives_Native_option__Common_TCP_channel){
            .tag = FStar_Pervasives_Native_None,
            .v = NULL,
        };
  }
}

static int client_endpoint_do_local(
    tls13_client_driver *driver,
    TLS13_Impl_CanonicalTypes_client_local_event ev,
    TLS13_Impl_Client_CanonicalProtocol_tls_client_local_frame local_frame,
    uint8_t *app_out,
    size_t app_out_len,
    bool scheduled) {
  TLS13_Impl_Client_CanonicalQueries_client_next_local_action_config cfg =
      client_endpoint_config();
  TLS13_Impl_Client_Endpoint_client_endpoint_frame frame =
      client_endpoint_frame(
          driver->verified_driver,
          app_out,
          app_out_len,
          local_frame.tls_client_local_payload,
      local_frame.tls_client_local_payload_len,
      driver->verified_driver.client_driver_local_app_out,
      TLS13_CLIENT_APP_OUT_CAP);
  Common_ProtocolImplementation_process_result result;
  if (scheduled) {
    result =
        TLS13_Impl_Client_Endpoint_client_run_scheduled_local_action(
            driver->verified_driver.client_driver_client,
            cfg,
            frame,
            driver->channel,
            ev,
            local_frame);
  } else {
    result =
        TLS13_Impl_Client_Endpoint_client_run_api_local_action(
            driver->verified_driver.client_driver_client,
            frame,
            driver->channel,
            ev,
            local_frame);
  }
  if (result.process_status != Common_ProtocolImplementation_StepOk) {
    return driver_fail(
        driver,
        "endpoint local action %u returned process status %u",
        (unsigned)TLS13_Impl_CanonicalTypes_client_local_event_kind(ev),
        (unsigned)result.process_status);
  }
  return 0;
}

static int client_endpoint_run(
    tls13_client_driver *driver,
    uint8_t *app_out,
    size_t app_out_len,
    size_t *produced_app_len,
    bool stop_on_application_data,
    bool stop_on_application_ready,
    bool stop_on_closed,
    size_t fuel) {
  if (produced_app_len != NULL) {
    *produced_app_len = 0u;
  }
  if (driver->verified_driver.client_driver_buffered_len == NULL) {
    return driver_fail(driver, "endpoint buffered-length cell is missing");
  }
  TLS13_Impl_Client_CanonicalQueries_client_next_local_action_config cfg =
      client_endpoint_config();
  TLS13_Impl_Client_Endpoint_client_endpoint_frame frame =
      client_endpoint_frame(
          driver->verified_driver,
          app_out,
          app_out_len,
          driver->verified_driver.client_driver_empty_payload,
      0u,
      driver->verified_driver.client_driver_local_app_out,
      TLS13_CLIENT_APP_OUT_CAP);
  TLS13_Impl_Client_Endpoint_client_endpoint_run_result result =
      TLS13_Impl_Client_Endpoint_client_endpoint_run_workflow(
          driver->verified_driver.client_driver_client,
          cfg,
          frame,
          driver->channel,
          driver->verified_driver.client_driver_buffered_len,
          stop_on_application_data,
          stop_on_application_ready,
          stop_on_closed,
          fuel);
  if (produced_app_len != NULL) {
    *produced_app_len = result.client_endpoint_run_app_len;
  }
  switch (result.client_endpoint_run_status) {
    case TLS13_Impl_Client_Endpoint_ClientEndpointRunOk:
      return 0;
    case TLS13_Impl_Client_Endpoint_ClientEndpointRunFuelExhausted:
      return driver_fail(driver, "endpoint workflow exhausted fuel");
    case TLS13_Impl_Client_Endpoint_ClientEndpointRunFailed:
    default:
      return driver_fail(
          driver,
          "endpoint workflow failed with process status %u",
          (unsigned)result.client_endpoint_run_last_status);
  }
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
  ensure_krml_globals_initialized();
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

  uint8_t empty_trust_anchor = 0;
  uint8_t *trust_anchor_input =
      trust_anchor_pem_len == 0u ? &empty_trust_anchor : (uint8_t *)trust_anchor_pem;

  TLS13_Impl_Client_Driver_client_driver verified_driver =
      TLS13_Impl_Client_Driver_new_client(
          (uint8_t *)server_name,
          server_name_len,
          trust_anchor_input,
          trust_anchor_pem_len,
          validation_time_seconds);

  FStar_Pervasives_Native_option__Common_TCP_channel ch_opt =
      Common_TCP_connect_tcp((uint8_t *)connect_host, connect_host_len, port);
  if (ch_opt.tag != FStar_Pervasives_Native_Some) {
    driver_fail(
        driver,
        "TCP connect to %s:%u failed",
        connect_host,
        (unsigned)port);
    free(driver);
    return 1;
  }

  driver->verified_driver = verified_driver;
  driver->channel = ch_opt.v;
  client_set_channel(&driver->verified_driver, ch_opt.v);
  if (client_endpoint_run(
          driver,
          driver->verified_driver.client_driver_app_out,
          TLS13_CLIENT_APP_OUT_CAP,
          NULL,
          false,
          true,
          false,
          TLS13_DRIVER_WORKFLOW_FUEL) != 0) {
    Common_TCP_close(ch_opt.v);
    client_clear_channel(&driver->verified_driver);
    free(driver);
    return 1;
  }

  driver->connected = true;
  *out = driver;
  return 0;
}

int tls13_client_driver_send_application_data(
    tls13_client_driver *driver,
    const uint8_t *payload,
    size_t payload_len) {
  if (driver == NULL || (payload == NULL && payload_len != 0u)) {
    return 1;
  }
  if (!driver->connected) {
    return driver_fail(driver, "TLS channel is closed");
  }

  uint8_t empty_payload = 0;
  uint8_t *payload_input =
      payload_len == 0u ? &empty_payload : (uint8_t *)payload;
  TLS13_Impl_CanonicalTypes_client_local_event ev =
      TLS13_Impl_Client_CanonicalQueries_client_local_event_of_kind(
          TLS13_Impl_Client_Types_LocalSendApplicationData);
  TLS13_Impl_Client_CanonicalProtocol_tls_client_local_frame local_frame = {
      .tls_client_local_payload = payload_input,
      .tls_client_local_payload_len = payload_len,
      .tls_client_local_app_out = driver->verified_driver.client_driver_app_out,
      .tls_client_local_app_out_len = TLS13_CLIENT_APP_OUT_CAP,
  };
  return client_endpoint_do_local(
      driver,
      ev,
      local_frame,
      driver->verified_driver.client_driver_app_out,
      TLS13_CLIENT_APP_OUT_CAP,
      false);
}

int tls13_client_driver_receive_application_data(
    tls13_client_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len) {
  if (driver == NULL || out == NULL || out_len == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return driver_fail(driver, "TLS channel is closed");
  }
  *out_len = 0u;

  if (client_endpoint_run(
          driver,
          out,
          out_cap,
          out_len,
          true,
          false,
          false,
          TLS13_DRIVER_WORKFLOW_FUEL) != 0) {
    return 1;
  }
  return 0;
}

int tls13_client_driver_close(tls13_client_driver *driver, bool wait_for_peer) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return 0;
  }

  TLS13_Impl_CanonicalTypes_client_local_event ev =
      TLS13_Impl_Client_CanonicalQueries_client_local_event_of_kind(
          TLS13_Impl_Client_Types_LocalSendCloseNotify);
  TLS13_Impl_Client_CanonicalProtocol_tls_client_local_frame local_frame = {
      .tls_client_local_payload =
          driver->verified_driver.client_driver_empty_payload,
      .tls_client_local_payload_len = 0u,
      .tls_client_local_app_out = driver->verified_driver.client_driver_app_out,
      .tls_client_local_app_out_len = TLS13_CLIENT_APP_OUT_CAP,
  };
  int rc = client_endpoint_do_local(
      driver,
      ev,
      local_frame,
      driver->verified_driver.client_driver_app_out,
      TLS13_CLIENT_APP_OUT_CAP,
      false);
  if (rc == 0 && wait_for_peer) {
    rc = client_endpoint_run(
        driver,
        driver->verified_driver.client_driver_app_out,
        TLS13_CLIENT_APP_OUT_CAP,
        NULL,
        false,
        false,
        true,
        TLS13_DRIVER_WORKFLOW_FUEL);
  }
  if (driver->channel != NULL) {
    Common_TCP_close(driver->channel);
    driver->channel = NULL;
  }
  client_clear_channel(&driver->verified_driver);
  driver->connected = false;
  return rc;
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
    (void)tls13_client_driver_close(driver, false);
  }
  free(driver);
}

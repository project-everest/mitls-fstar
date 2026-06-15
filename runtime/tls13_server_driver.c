#include "tls13_server_driver.h"

#include "TLS13_Impl_Server_Driver.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLS13_SERVER_DRIVER_NETWORK_FUEL 1000u
#define TLS13_SERVER_DRIVER_LOCAL_FUEL 100u

struct tls13_server_driver_s {
  TLS13_Impl_Server_Driver_server_driver verified_driver;
  bool connected;
  char last_error[256];
};

static int driver_fail(tls13_server_driver *driver, const char *fmt, ...) {
  if (driver != NULL && fmt != NULL) {
    va_list ap;
    va_start(ap, fmt);
    (void)vsnprintf(driver->last_error, sizeof driver->last_error, fmt, ap);
    va_end(ap);
  }
  return 1;
}

int tls13_server_driver_accept(
    tls13_server_driver **out,
    const char *bind_host,
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key_pem,
    size_t private_key_pem_len) {
  if (out == NULL || bind_host == NULL ||
      (certificate_chain == NULL && certificate_chain_len != 0u) ||
      private_key_pem == NULL || private_key_pem_len == 0u) {
    return 1;
  }
  *out = NULL;

  tls13_server_driver *driver = calloc(1, sizeof *driver);
  if (driver == NULL) {
    return 1;
  }

  uint8_t empty_certificate = 0;
  uint8_t *certificate_input =
      certificate_chain_len == 0u ? &empty_certificate : (uint8_t *)certificate_chain;
  FStar_Pervasives_Native_option__TLS13_Impl_Server_Driver_State_server_driver created =
      TLS13_Impl_Server_Driver_new_server(
          certificate_input,
          certificate_chain_len,
          (uint8_t *)private_key_pem,
          private_key_pem_len);
  if (created.tag != FStar_Pervasives_Native_Some) {
    driver_fail(driver, "verified server driver allocation failed");
    free(driver);
    return 1;
  }

  size_t bind_host_len = strlen(bind_host);
  TLS13_Impl_Server_Driver_server_driver verified_driver = created.v;
  TLS13_Impl_Server_Driver_server_workflow_status status =
      TLS13_Impl_Server_Driver_accept(
          verified_driver,
          (uint8_t *)bind_host,
          bind_host_len,
          port,
          TLS13_SERVER_DRIVER_LOCAL_FUEL,
          TLS13_SERVER_DRIVER_NETWORK_FUEL);
  if (status != TLS13_Impl_Server_Driver_ServerWorkflowOk) {
    if (status != TLS13_Impl_Server_Driver_ServerWorkflowClosed) {
      (void)TLS13_Impl_Server_Driver_close(
          verified_driver,
          false,
          TLS13_SERVER_DRIVER_NETWORK_FUEL);
    }
    driver->verified_driver = verified_driver;
    driver->connected = false;
    driver_fail(
        driver,
        "verified accept workflow on %s:%u returned status %u "
        "(control=%u stage=%u failure=%u/%u/%u keys=%u%u%u%u records=%u%u)",
        bind_host,
        (unsigned)port,
        (unsigned)status,
        (unsigned)(verified_driver.server_driver_server.control.control_tag != NULL
                       ? *verified_driver.server_driver_server.control.control_tag
                       : 255u),
        (unsigned)(verified_driver.server_driver_server.control.handshake_stage_tag != NULL
                       ? *verified_driver.server_driver_server.control.handshake_stage_tag
                       : 255u),
        (unsigned)(verified_driver.server_driver_server.control.failure_present != NULL
                       ? *verified_driver.server_driver_server.control.failure_present
                       : 0u),
        (unsigned)(verified_driver.server_driver_server.control.failure_code != NULL
                       ? *verified_driver.server_driver_server.control.failure_code
                       : 255u),
        (unsigned)(verified_driver.server_driver_server.control.failure_alert != NULL
                       ? *verified_driver.server_driver_server.control.failure_alert
                       : 255u),
        (unsigned)(verified_driver.server_driver_server.handshake.keys.handshake_secret.present3 != NULL
                       ? *verified_driver.server_driver_server.handshake.keys.handshake_secret.present3
                       : 0u),
        (unsigned)(verified_driver.server_driver_server.handshake.keys.server_handshake_traffic.present2 != NULL
                       ? *verified_driver.server_driver_server.handshake.keys.server_handshake_traffic.present2
                       : 0u),
        (unsigned)(verified_driver.server_driver_server.handshake.keys.client_handshake_traffic.present2 != NULL
                       ? *verified_driver.server_driver_server.handshake.keys.client_handshake_traffic.present2
                       : 0u),
        (unsigned)(verified_driver.server_driver_server.handshake.keys.master_secret.present3 != NULL
                       ? *verified_driver.server_driver_server.handshake.keys.master_secret.present3
                       : 0u),
        (unsigned)(verified_driver.server_driver_server.records.read.installed != NULL
                       ? *verified_driver.server_driver_server.records.read.installed
                       : 0u),
        (unsigned)(verified_driver.server_driver_server.records.write.installed != NULL
                       ? *verified_driver.server_driver_server.records.write.installed
                       : 0u));
    *out = driver;
    return 1;
  }

  driver->verified_driver = verified_driver;
  driver->connected = true;
  *out = driver;
  return 0;
}

int tls13_server_driver_send_application_data(
    tls13_server_driver *driver,
    const uint8_t *payload,
    size_t payload_len) {
  if (driver == NULL || (payload == NULL && payload_len != 0u)) {
    return 1;
  }
  if (!driver->connected) {
    return driver_fail(driver, "TLS server channel is closed");
  }

  uint8_t empty_payload = 0;
  uint8_t *payload_input = payload_len == 0u ? &empty_payload : (uint8_t *)payload;
  TLS13_Impl_Server_Driver_server_workflow_status status =
      TLS13_Impl_Server_Driver_send(driver->verified_driver, payload_input, payload_len);
  if (status != TLS13_Impl_Server_Driver_ServerWorkflowOk) {
    return driver_fail(driver, "verified server send returned status %u", (unsigned)status);
  }
  return 0;
}

int tls13_server_driver_receive_application_data(
    tls13_server_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len) {
  if (driver == NULL || out == NULL || out_len == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return driver_fail(driver, "TLS server channel is closed");
  }
  *out_len = 0u;

  TLS13_Impl_Server_Driver_server_receive_result result =
      TLS13_Impl_Server_Driver_receive(
          driver->verified_driver,
          out,
          out_cap,
          TLS13_SERVER_DRIVER_LOCAL_FUEL,
          TLS13_SERVER_DRIVER_NETWORK_FUEL);
  if (result.server_receive_status != TLS13_Impl_Server_Driver_ServerWorkflowOk) {
    return driver_fail(
        driver,
        "verified server receive returned status %u",
        (unsigned)result.server_receive_status);
  }

  *out_len = result.server_receive_len;
  return 0;
}

int tls13_server_driver_close(tls13_server_driver *driver, bool wait_for_peer) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return 0;
  }

  TLS13_Impl_Server_Driver_server_workflow_status status =
      TLS13_Impl_Server_Driver_close(
          driver->verified_driver,
          wait_for_peer,
          TLS13_SERVER_DRIVER_NETWORK_FUEL);
  driver->connected = false;
  if (status != TLS13_Impl_Server_Driver_ServerWorkflowClosed) {
    return driver_fail(driver, "verified server close returned status %u", (unsigned)status);
  }
  return 0;
}

const char *tls13_server_driver_last_error(const tls13_server_driver *driver) {
  if (driver == NULL || driver->last_error[0] == '\0') {
    return "no server driver error";
  }
  return driver->last_error;
}

void tls13_server_driver_free(tls13_server_driver *driver) {
  if (driver == NULL) {
    return;
  }
  if (driver->connected) {
    (void)tls13_server_driver_close(driver, false);
  }
  free(driver);
}

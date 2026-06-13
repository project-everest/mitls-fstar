#include "tls13_client_driver.h"

#include "TLS13_Impl_Client_Driver.h"
#include "TLS13_Impl_Serializer.h"

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

void TLS13_Impl_Serializer_build_server_certificate_verify_input(
    uint8_t *transcript_hash,
    uint8_t *out,
    size_t out_len) {
  TLS13_Connection_Backend_build_server_certificate_verify_input(
      transcript_hash, out, out_len);
}

size_t TLS13_Impl_Serializer_serialize_raw_application_data_record(
    uint8_t *fragment,
    size_t fragment_len,
    uint8_t *out,
    size_t out_len) {
  return TLS13_Connection_Backend_serialize_raw_application_data_record(
      fragment, fragment_len, out, out_len);
}

size_t TLS13_Impl_Serializer_serialize_client_finished_outputs(
    TLS13_Record_record_state write_state,
    uint8_t *lfin,
    uint8_t *handshake_out,
    uint8_t *network_out,
    size_t network_out_len) {
  return TLS13_Connection_Backend_serialize_client_finished_outputs(
      write_state.key,
      write_state.iv,
      *write_state.seq,
      *write_state.installed,
      lfin,
      handshake_out,
      network_out,
      network_out_len);
}

size_t TLS13_Impl_Serializer_serialize_finished_handshake(
    uint8_t *lfin,
    uint8_t *handshake_out,
    size_t handshake_out_len) {
  return TLS13_Connection_Backend_serialize_finished_handshake(
      lfin, handshake_out, handshake_out_len);
}

struct tls13_client_driver_s {
  TLS13_Impl_Client_Driver_client_driver verified_driver;
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

  FStar_Pervasives_Native_option__TLS13_Impl_Client_Driver_client_driver created =
      TLS13_Impl_Client_Driver_new_client(
          (uint8_t *)server_name,
          server_name_len,
          trust_anchor_input,
          trust_anchor_pem_len,
          validation_time_seconds);
  if (created.tag != FStar_Pervasives_Native_Some) {
    driver_fail(
        driver,
        "verified driver allocation for %s failed",
        server_name);
    free(driver);
    return 1;
  }

  TLS13_Impl_Client_Driver_client_driver verified_driver = created.v;
  TLS13_Impl_Client_Driver_driver_workflow_status status =
      TLS13_Impl_Client_Driver_connect(
          verified_driver,
          (uint8_t *)connect_host,
          connect_host_len,
          port,
          TLS13_DRIVER_LOCAL_FUEL,
          TLS13_DRIVER_WORKFLOW_FUEL);
  if (status != TLS13_Impl_Client_Driver_DriverWorkflowOk) {
    driver_fail(
        driver,
        "verified connect workflow to %s:%u returned status %u",
        connect_host,
        (unsigned)port,
        (unsigned)status);
    free(driver);
    return 1;
  }

  driver->verified_driver = verified_driver;
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
  uint8_t *payload_input = payload_len == 0u ? &empty_payload : (uint8_t *)payload;
  TLS13_Impl_Client_Driver_driver_workflow_status status =
      TLS13_Impl_Client_Driver_send(driver->verified_driver, payload_input, payload_len);
  if (status != TLS13_Impl_Client_Driver_DriverWorkflowOk) {
    return driver_fail(driver, "verified send returned status %u", (unsigned)status);
  }
  return 0;
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

  TLS13_Impl_Client_Driver_client_receive_result result =
      TLS13_Impl_Client_Driver_receive(
          driver->verified_driver,
          out,
          out_cap,
          TLS13_DRIVER_LOCAL_FUEL,
          TLS13_DRIVER_WORKFLOW_FUEL);
  if (result.client_receive_status != TLS13_Impl_Client_Driver_DriverWorkflowOk) {
    return driver_fail(
        driver,
        "verified receive returned status %u",
        (unsigned)result.client_receive_status);
  }

  *out_len = result.client_receive_len;
  return 0;
}

int tls13_client_driver_close(tls13_client_driver *driver, bool wait_for_peer) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return 0;
  }

  TLS13_Impl_Client_Driver_driver_workflow_status status =
      TLS13_Impl_Client_Driver_close(
          driver->verified_driver,
          wait_for_peer,
          TLS13_DRIVER_WORKFLOW_FUEL);
  driver->connected = false;
  if (status != TLS13_Impl_Client_Driver_DriverWorkflowClosed) {
    return driver_fail(driver, "verified close returned status %u", (unsigned)status);
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
    (void)tls13_client_driver_close(driver, false);
  }
  free(driver);
}

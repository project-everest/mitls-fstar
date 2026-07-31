#include "tls13_server_driver.h"

#include "TLS13_Impl_ConnectionState_Bounds.h"
#include "TLS13_Impl_Server_Driver.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLS13_SERVER_DRIVER_NETWORK_FUEL ((size_t)1000u)
#define TLS13_SERVER_DRIVER_LOCAL_FUEL ((size_t)100u)

enum tls13_server_driver_state {
  TLS13_SERVER_DRIVER_READY,
  TLS13_SERVER_DRIVER_CLOSED,
};

struct tls13_server_driver_s {
  TLS13_Impl_Server_Driver_server_driver verified_driver;
  enum tls13_server_driver_state state;
  char last_error[256];
};

struct tls13_server_config_s {
  TLS13_Impl_Server_Driver_server_credentials verified_credentials;
  TLS13_Impl_Server_Driver_server_listener verified_listener;
  uint8_t *bind_host;
  size_t bind_host_len;
  uint16_t port;
  uint8_t *certificate_chain;
  size_t certificate_chain_len;
  uint8_t *private_key_pem;
  size_t private_key_pem_len;
};

static int driver_fail(tls13_server_driver *driver, const char *message) {
  if (driver != NULL && message != NULL) {
    (void)snprintf(driver->last_error, sizeof driver->last_error, "%s", message);
  }
  return 1;
}

static const char *driver_status_message(
    TLS13_Impl_Server_Driver_server_workflow_status status) {
  switch (status) {
    case TLS13_Impl_Server_Driver_ServerWorkflowOk:
      return "ok";
    case TLS13_Impl_Server_Driver_ServerWorkflowNeedMoreInput:
      return "needs more input";
    case TLS13_Impl_Server_Driver_ServerWorkflowStepFailed:
      return "verified protocol step failed";
    case TLS13_Impl_Server_Driver_ServerWorkflowExhausted:
      return "workflow exhausted fuel";
    case TLS13_Impl_Server_Driver_ServerWorkflowClosed:
      return "TLS channel closed";
    case TLS13_Impl_Server_Driver_ServerWorkflowPayloadTooLarge:
      return "payload exceeds the single-record limit (16384 bytes)";
    case TLS13_Impl_Server_Driver_ServerWorkflowOutputBufferTooSmall:
      return "output buffer is smaller than the maximum TLS record plaintext";
    default:
      return "unknown verified server driver status";
  }
}

static int driver_fail_status(
    tls13_server_driver *driver,
    const char *operation,
    TLS13_Impl_Server_Driver_server_workflow_status status) {
  if (driver != NULL) {
    (void)snprintf(
        driver->last_error,
        sizeof driver->last_error,
        "%s: %s",
        operation,
        driver_status_message(status));
    /* Failures on the accept path free the driver before the caller can read
       last_error, so make the reason observable for debugging. */
    if (getenv("TLS13_SERVER_DRIVER_DEBUG") != NULL) {
      fprintf(stderr, "tls13_server_driver: %s\n", driver->last_error);
    }
  }
  return 1;
}

int tls13_server_config_new(
    tls13_server_config **out,
    const char *bind_host,
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key_pem,
    size_t private_key_pem_len) {
  if (out == NULL) {
    return 1;
  }
  *out = NULL;
  if (bind_host == NULL || bind_host[0] == '\0' ||
      (certificate_chain == NULL && certificate_chain_len != 0u) ||
      private_key_pem == NULL || private_key_pem_len == 0u ||
      certificate_chain_len >
          TLS13_Impl_ConnectionState_Bounds_max_server_certificate_chain_len_sz) {
    return 1;
  }

  size_t bind_host_len = strlen(bind_host);
  tls13_server_config *config = calloc(1u, sizeof *config);
  uint8_t *bind_host_copy = malloc(bind_host_len);
  uint8_t *certificate_copy =
      malloc(certificate_chain_len == 0u ? 1u : certificate_chain_len);
  uint8_t *private_key_copy = malloc(private_key_pem_len);
  if (config == NULL || bind_host_copy == NULL || certificate_copy == NULL ||
      private_key_copy == NULL) {
    free(private_key_copy);
    free(certificate_copy);
    free(bind_host_copy);
    free(config);
    return 1;
  }
  memcpy(bind_host_copy, bind_host, bind_host_len);
  if (certificate_chain_len != 0u) {
    memcpy(certificate_copy, certificate_chain, certificate_chain_len);
  }
  memcpy(private_key_copy, private_key_pem, private_key_pem_len);

  FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials credentials =
      TLS13_Impl_Server_Driver_new_server_credentials(
          certificate_copy,
          certificate_chain_len,
          private_key_copy,
          private_key_pem_len);
  if (credentials.tag != FStar_Pervasives_Native_Some) {
    free(private_key_copy);
    free(certificate_copy);
    free(bind_host_copy);
    free(config);
    return 1;
  }

  FStar_Pervasives_Native_option__Common_TCP_listener listener =
      TLS13_Impl_Server_Driver_new_server_listener(
          bind_host_copy, bind_host_len, port);
  if (listener.tag != FStar_Pervasives_Native_Some) {
    TLS13_Impl_Server_Driver_free_server_credentials(credentials.v);
    free(private_key_copy);
    free(certificate_copy);
    free(bind_host_copy);
    free(config);
    return 1;
  }

  config->verified_credentials = credentials.v;
  config->verified_listener = listener.v;
  config->bind_host = bind_host_copy;
  config->bind_host_len = bind_host_len;
  config->port = port;
  config->certificate_chain = certificate_copy;
  config->certificate_chain_len = certificate_chain_len;
  config->private_key_pem = private_key_copy;
  config->private_key_pem_len = private_key_pem_len;
  *out = config;
  return 0;
}

void tls13_server_config_free(tls13_server_config *config) {
  if (config == NULL) {
    return;
  }
  TLS13_Impl_Server_Driver_free_server_listener(config->verified_listener);
  TLS13_Impl_Server_Driver_free_server_credentials(
      config->verified_credentials);
  free(config->private_key_pem);
  free(config->certificate_chain);
  free(config->bind_host);
  free(config);
}

int tls13_server_driver_accept_with_config(
    tls13_server_driver **out,
    const tls13_server_config *config) {
  if (out == NULL) {
    return 1;
  }
  *out = NULL;
  if (config == NULL) {
    return 1;
  }

  tls13_server_driver *driver = calloc(1u, sizeof *driver);
  if (driver == NULL) {
    return 1;
  }

  FStar_Pervasives_Native_option__TLS13_Impl_Server_Driver_State_top_server_driver created =
      TLS13_Impl_Server_Driver_new_server_with_credentials(
          config->verified_credentials,
          config->certificate_chain,
          config->certificate_chain_len,
          config->private_key_pem,
          config->private_key_pem_len);
  if (created.tag != FStar_Pervasives_Native_Some) {
    (void)driver_fail(driver, "verified server driver allocation failed");
    free(driver);
    return 1;
  }

  driver->verified_driver = created.v;
  TLS13_Impl_Server_Driver_server_workflow_status status =
      TLS13_Impl_Server_Driver_accept_with_listener(
          driver->verified_driver,
          config->verified_listener,
          config->bind_host,
          config->bind_host_len,
          config->port,
          TLS13_SERVER_DRIVER_LOCAL_FUEL,
          TLS13_SERVER_DRIVER_NETWORK_FUEL);
  if (status != TLS13_Impl_Server_Driver_ServerWorkflowOk) {
    (void)driver_fail_status(driver, "accept", status);
    driver->state = TLS13_SERVER_DRIVER_CLOSED;
    TLS13_Impl_Server_Driver_free(driver->verified_driver);
    free(driver);
    return 1;
  }

  driver->state = TLS13_SERVER_DRIVER_READY;
  *out = driver;
  return 0;
}

int tls13_server_driver_accept(
    tls13_server_driver **out,
    const char *bind_host,
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key_pem,
    size_t private_key_pem_len) {
  tls13_server_config *config = NULL;
  if (tls13_server_config_new(
          &config,
          bind_host,
          port,
          certificate_chain,
          certificate_chain_len,
          private_key_pem,
          private_key_pem_len) != 0) {
    if (out != NULL) {
      *out = NULL;
    }
    return 1;
  }
  int result = tls13_server_driver_accept_with_config(out, config);
  tls13_server_config_free(config);
  return result;
}

int tls13_server_driver_send_application_data(
    tls13_server_driver *driver,
    const uint8_t *payload,
    size_t payload_len) {
  if (driver == NULL) {
    return 1;
  }
  if (payload == NULL && payload_len != 0u) {
    return driver_fail(driver, "send: payload is null");
  }
  if (driver->state != TLS13_SERVER_DRIVER_READY) {
    return driver_fail(driver, "send: TLS channel is closed");
  }

  uint8_t empty_payload = 0u;
  uint8_t *payload_input =
      payload_len == 0u ? &empty_payload : (uint8_t *)(void *)payload;
  TLS13_Impl_Server_Driver_server_workflow_status status =
      TLS13_Impl_Server_Driver_send(
          driver->verified_driver, payload_input, payload_len);
  if (status == TLS13_Impl_Server_Driver_ServerWorkflowOk) {
    return 0;
  }
  (void)driver_fail_status(driver, "send", status);
  if (status ==
      TLS13_Impl_Server_Driver_ServerWorkflowPayloadTooLarge) {
    return 1;
  }
  driver->state = TLS13_SERVER_DRIVER_CLOSED;
  return 1;
}

int tls13_server_driver_receive_application_data(
    tls13_server_driver *driver,
    uint8_t *out,
    size_t out_cap,
    size_t *out_len) {
  if (driver == NULL) {
    return 1;
  }
  if (out == NULL || out_len == NULL) {
    return driver_fail(driver, "receive: invalid output buffer");
  }
  if (driver->state != TLS13_SERVER_DRIVER_READY) {
    return driver_fail(driver, "receive: TLS channel is closed");
  }
  *out_len = 0u;

  TLS13_Impl_Server_Driver_server_receive_result result =
      TLS13_Impl_Server_Driver_receive(
          driver->verified_driver,
          out,
          out_cap,
          TLS13_SERVER_DRIVER_LOCAL_FUEL,
          TLS13_SERVER_DRIVER_NETWORK_FUEL);
  *out_len = result.server_receive_len;
  if (result.server_receive_status ==
      TLS13_Impl_Server_Driver_ServerWorkflowOk) {
    return 0;
  }
  (void)driver_fail_status(driver, "receive", result.server_receive_status);
  if (result.server_receive_status ==
          TLS13_Impl_Server_Driver_ServerWorkflowExhausted ||
      result.server_receive_status ==
          TLS13_Impl_Server_Driver_ServerWorkflowNeedMoreInput ||
      result.server_receive_status ==
          TLS13_Impl_Server_Driver_ServerWorkflowOutputBufferTooSmall) {
    /* Verified: application_ready is preserved on exhausted/need-more-input,
       so the connection remains usable for retry. */
    return 1;
  }
  driver->state = TLS13_SERVER_DRIVER_CLOSED;
  return 1;
}

int tls13_server_driver_close(tls13_server_driver *driver, bool wait_for_peer) {
  if (driver == NULL) {
    return 1;
  }
  if (driver->state == TLS13_SERVER_DRIVER_CLOSED) {
    return 0;
  }

  TLS13_Impl_Server_Driver_server_workflow_status status =
      TLS13_Impl_Server_Driver_close(
          driver->verified_driver,
          wait_for_peer,
          TLS13_SERVER_DRIVER_NETWORK_FUEL);
  driver->state = TLS13_SERVER_DRIVER_CLOSED;
  if (status != TLS13_Impl_Server_Driver_ServerWorkflowClosed) {
    return driver_fail_status(driver, "close", status);
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
  if (driver->state == TLS13_SERVER_DRIVER_READY) {
    (void)tls13_server_driver_close(driver, false);
  }
  TLS13_Impl_Server_Driver_free(driver->verified_driver);
  free(driver);
}

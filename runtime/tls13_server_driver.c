#include "tls13_server_driver.h"

#include "Common_TCP.h"
#include "TLS13_Crypto.h"
#include "TLS13_Impl_ConnectionState_Queries.h"
#include "TLS13_Impl_Server_Driver.h"
#include "TLS13_Impl_Server_Endpoint.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLS13_SERVER_DRIVER_NETWORK_FUEL 1000u
#define TLS13_SERVER_DRIVER_LOCAL_FUEL 100u

#define TLS13_SERVER_NETWORK_OUT_CAP 20000u
#define TLS13_SERVER_APP_OUT_CAP 16640u
#define TLS13_SERVER_RX_CAP 65535u
#define TLS13_SERVER_MATERIAL_CAP 64u
#define TLS13_SERVER_PRIVATE_KEY_CAP 32u

#define TLS13_CONTROL_HANDSHAKING 1u
#define TLS13_CONTROL_APPLICATION_DATA 2u
#define TLS13_CONTROL_CLOSED 4u
#define TLS13_CONTROL_FAILED 5u
#define TLS13_HANDSHAKE_CLIENT_HELLO_RECEIVED 13u

typedef Common_ProtocolEndpoint_endpoint_action__TLS13_Impl_Server_CanonicalProtocol_tls_server_network_bridge_frame_TLS13_Impl_CanonicalTypes_server_local_event_TLS13_Impl_Server_CanonicalProtocol_tls_server_local_bridge_frame
    server_endpoint_action;

struct tls13_server_driver_s {
  TLS13_Impl_Server_Driver_server_driver verified_driver;
  Common_TCP_channel channel;
  size_t certificate_chain_len;
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

static void server_trace(const char *fmt, ...) {
  if (getenv("TLS13_SERVER_DRIVER_TRACE") == NULL) {
    return;
  }
  va_list ap;
  va_start(ap, fmt);
  (void)vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
}

#if defined(__GNUC__)
extern void krmlinit_globals(void) __attribute__((weak));
#else
extern void krmlinit_globals(void);
#endif

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

static TLS13_Impl_Server_CanonicalProtocol_canonical_server server_endpoint_state(
    TLS13_Impl_Server_Driver_server_driver d) {
  return (TLS13_Impl_Server_CanonicalProtocol_canonical_server){
      .canonical_server_state = d.server_driver_server,
      .canonical_server_credentials = d.server_driver_credentials,
  };
}

static TLS13_Impl_Server_Endpoint_server_endpoint_frame server_endpoint_frame(
    TLS13_Impl_Server_Driver_server_driver d,
    uint8_t *app_out,
    size_t app_out_len,
    uint8_t *local_payload,
    size_t local_payload_len) {
  return (TLS13_Impl_Server_Endpoint_server_endpoint_frame){
      .server_ep_query =
          {
              .server_query_network_app_out = app_out,
              .server_query_network_app_out_len = app_out_len,
              .server_query_local_payload = local_payload,
              .server_query_local_payload_len = local_payload_len,
              .server_query_local_app_out = app_out,
              .server_query_local_app_out_len = app_out_len,
          },
      .server_ep_raw_len = TLS13_SERVER_RX_CAP,
      .server_ep_raw = d.server_driver_raw,
      .server_ep_network_out_len = TLS13_SERVER_NETWORK_OUT_CAP,
      .server_ep_network_out = d.server_driver_network_out,
      .server_ep_material_len = TLS13_SERVER_MATERIAL_CAP,
      .server_ep_material = d.server_driver_material_payload,
      .server_ep_private_len = TLS13_SERVER_PRIVATE_KEY_CAP,
      .server_ep_private = d.server_driver_material_payload + TLS13_SERVER_PRIVATE_KEY_CAP,
  };
}

static bool server_control_is(
    const TLS13_Impl_Server_Driver_server_driver *d,
    uint8_t tag) {
  return d != NULL && d->server_driver_server.control.control_tag != NULL &&
         *d->server_driver_server.control.control_tag == tag;
}

static bool server_failed(const TLS13_Impl_Server_Driver_server_driver *d) {
  return server_control_is(d, TLS13_CONTROL_FAILED);
}

static bool server_needs_handshake_material(
    const TLS13_Impl_Server_Driver_server_driver *d) {
  return d != NULL &&
         d->server_driver_server.control.control_tag != NULL &&
         *d->server_driver_server.control.control_tag ==
             TLS13_CONTROL_HANDSHAKING &&
         d->server_driver_server.control.handshake_stage_tag != NULL &&
         *d->server_driver_server.control.handshake_stage_tag ==
             TLS13_HANDSHAKE_CLIENT_HELLO_RECEIVED &&
         d->server_driver_server.handshake.server_selection_present != NULL &&
         !*d->server_driver_server.handshake.server_selection_present;
}

static int server_prepare_endpoint_material(tls13_server_driver *driver) {
  if (!server_needs_handshake_material(&driver->verified_driver)) {
    return 0;
  }
  if (driver->verified_driver.server_driver_material_payload == NULL ||
      !TLS13_Crypto_random_bytes(
          driver->verified_driver.server_driver_material_payload,
          TLS13_SERVER_MATERIAL_CAP)) {
    return driver_fail(driver, "server endpoint failed to generate handshake material");
  }
  return 0;
}

static void server_set_channel(
    TLS13_Impl_Server_Driver_server_driver *d,
    Common_TCP_channel ch) {
  if (d != NULL && d->server_driver_channel != NULL) {
    *d->server_driver_channel =
        (FStar_Pervasives_Native_option__Common_TCP_channel){
            .tag = FStar_Pervasives_Native_Some,
            .v = ch,
        };
  }
}

static void server_clear_channel(TLS13_Impl_Server_Driver_server_driver *d) {
  if (d != NULL && d->server_driver_channel != NULL) {
    *d->server_driver_channel =
        (FStar_Pervasives_Native_option__Common_TCP_channel){
            .tag = FStar_Pervasives_Native_None,
            .v = NULL,
        };
  }
}

static int server_compact_input(
    tls13_server_driver *driver,
    Common_ProtocolImplementation_process_result result,
    size_t total_len) {
  if (result.process_consumed_len > total_len) {
    return driver_fail(
        driver,
        "endpoint consumed %zu bytes from %zu buffered bytes",
        result.process_consumed_len,
        total_len);
  }
  size_t remaining = total_len - result.process_consumed_len;
  if (remaining != 0u && result.process_consumed_len != 0u) {
    memmove(
        driver->verified_driver.server_driver_raw,
        driver->verified_driver.server_driver_raw + result.process_consumed_len,
        remaining);
  }
  if (driver->verified_driver.server_driver_buffered_len != NULL) {
    *driver->verified_driver.server_driver_buffered_len = remaining;
  }
  return 0;
}

static int server_endpoint_do_local(
    tls13_server_driver *driver,
    TLS13_Impl_CanonicalTypes_server_local_event ev,
    TLS13_Impl_Server_CanonicalProtocol_tls_server_local_frame local_frame,
    uint8_t *app_out,
    size_t app_out_len,
    bool scheduled) {
  TLS13_Impl_Server_Types_local_event_kind kind =
      TLS13_Impl_CanonicalTypes_server_local_event_kind(ev);
  size_t local_output_len = TLS13_SERVER_NETWORK_OUT_CAP;
  switch (kind) {
    case TLS13_Impl_Server_Types_LocalSendServerHello:
      local_output_len = 95u;
      break;
    case TLS13_Impl_Server_Types_LocalSendEncryptedExtensions:
      local_output_len = 28u;
      break;
    case TLS13_Impl_Server_Types_LocalSendCertificate:
      local_output_len = driver->certificate_chain_len + 35u;
      break;
    case TLS13_Impl_Server_Types_LocalSendCertificateVerify: {
      TLS13_Impl_ConnectionState_Repr_certificate_verify_signature_snapshot snap =
          TLS13_Impl_ConnectionState_Queries_get_certificate_verify_signature_snapshot(
              driver->verified_driver.server_driver_server);
      local_output_len = snap.cv_signature_len + 30u;
      break;
    }
    case TLS13_Impl_Server_Types_LocalSendServerFinished:
      local_output_len = 58u;
      break;
    default:
      break;
  }
  if (local_output_len > TLS13_SERVER_NETWORK_OUT_CAP) {
    return driver_fail(
        driver,
        "endpoint local action %u needs %zu bytes of network output",
        (unsigned)kind,
        local_output_len);
  }
  TLS13_Impl_Server_CanonicalProtocol_canonical_server srv =
      server_endpoint_state(driver->verified_driver);
  if (server_prepare_endpoint_material(driver) != 0) {
    return 1;
  }
  TLS13_Impl_Server_Endpoint_server_endpoint_frame frame =
      server_endpoint_frame(
          driver->verified_driver,
          app_out,
          app_out_len,
          local_frame.tls_server_local_payload,
          local_frame.tls_server_local_payload_len);
  frame.server_ep_network_out_len = local_output_len;
  Common_ProtocolImplementation_process_result result;
  if (scheduled) {
    result =
        TLS13_Impl_Server_Endpoint_server_run_scheduled_local_action(
           srv,
           frame,
           driver->channel,
           ev,
           local_frame);
  } else {
    result =
        TLS13_Impl_Server_Endpoint_server_run_api_local_action(
           srv,
           frame,
           driver->channel,
           ev,
           local_frame);
  }
  server_trace(
      "server local kind=%u status=%u consumed=%zu app=%zu net=%zu control=%u stage=%u",
      (unsigned)TLS13_Impl_CanonicalTypes_server_local_event_kind(ev),
      (unsigned)result.process_status,
      result.process_consumed_len,
      result.process_app_len,
      result.process_produced_len,
      (unsigned)(driver->verified_driver.server_driver_server.control.control_tag != NULL
                     ? *driver->verified_driver.server_driver_server.control.control_tag
                     : 255u),
      (unsigned)(driver->verified_driver.server_driver_server.control.handshake_stage_tag != NULL
                     ? *driver->verified_driver.server_driver_server.control.handshake_stage_tag
                     : 255u));
  if (result.process_status != Common_ProtocolImplementation_StepOk) {
    return driver_fail(
        driver,
        "endpoint local action %u returned process status %u",
        (unsigned)TLS13_Impl_CanonicalTypes_server_local_event_kind(ev),
        (unsigned)result.process_status);
  }
  return 0;
}

static int server_endpoint_run(
    tls13_server_driver *driver,
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
  while (fuel-- != 0u) {
    if (server_failed(&driver->verified_driver)) {
      return driver_fail(driver, "endpoint entered failed control state");
    }
    if (stop_on_application_ready &&
        server_control_is(&driver->verified_driver, TLS13_CONTROL_APPLICATION_DATA)) {
      return 0;
    }
    if (stop_on_closed &&
        server_control_is(&driver->verified_driver, TLS13_CONTROL_CLOSED)) {
      return 0;
    }

    TLS13_Impl_Server_CanonicalProtocol_canonical_server srv =
        server_endpoint_state(driver->verified_driver);
    TLS13_Impl_Server_Endpoint_server_endpoint_frame frame =
        server_endpoint_frame(
            driver->verified_driver,
            app_out,
            app_out_len,
            driver->verified_driver.server_driver_empty_payload,
            0u);
    server_endpoint_action action =
        TLS13_Impl_Server_Endpoint_server_endpoint_next_action(srv, frame);
    server_trace(
        "server action tag=%u control=%u stage=%u buffered=%zu",
        (unsigned)action.tag,
        (unsigned)(driver->verified_driver.server_driver_server.control.control_tag != NULL
                       ? *driver->verified_driver.server_driver_server.control.control_tag
                       : 255u),
        (unsigned)(driver->verified_driver.server_driver_server.control.handshake_stage_tag != NULL
                       ? *driver->verified_driver.server_driver_server.control.handshake_stage_tag
                       : 255u),
        driver->verified_driver.server_driver_buffered_len == NULL
            ? 0u
            : *driver->verified_driver.server_driver_buffered_len);

    switch (action.tag) {
      case Common_ProtocolEndpoint_EndpointLocal: {
        if (server_endpoint_do_local(
                driver,
                action.case_EndpointLocal.ev,
                action.case_EndpointLocal.frame,
                app_out,
                app_out_len,
                true) != 0) {
          return 1;
        }
        break;
      }
      case Common_ProtocolEndpoint_EndpointNeedInput: {
        size_t buffered_len =
            driver->verified_driver.server_driver_buffered_len == NULL
                ? 0u
                : *driver->verified_driver.server_driver_buffered_len;
        if (buffered_len >= TLS13_SERVER_RX_CAP) {
          return driver_fail(driver, "endpoint receive buffer is full");
        }
        size_t read_len = 0u;
        if (buffered_len == 0u) {
          read_len = Common_TCP_read(
              driver->channel,
              driver->verified_driver.server_driver_raw,
              TLS13_SERVER_RX_CAP);
          server_trace("server read fresh=%zu", read_len);
        }
        size_t total_len = buffered_len + read_len;
        if (total_len == 0u) {
          return driver_fail(driver, "endpoint TCP read returned no data");
        }

        srv = server_endpoint_state(driver->verified_driver);
        Common_ProtocolImplementation_process_result result =
            TLS13_Impl_Server_Endpoint_server_run_buffered_network_action(
                srv,
                frame,
                driver->channel,
                action.case_EndpointNeedInput,
                total_len);
        server_trace(
            "server network status=%u consumed=%zu app=%zu net=%zu total=%zu control=%u stage=%u",
            (unsigned)result.process_status,
            result.process_consumed_len,
            result.process_app_len,
            result.process_produced_len,
            total_len,
            (unsigned)(driver->verified_driver.server_driver_server.control.control_tag != NULL
                           ? *driver->verified_driver.server_driver_server.control.control_tag
                           : 255u),
            (unsigned)(driver->verified_driver.server_driver_server.control.handshake_stage_tag != NULL
                           ? *driver->verified_driver.server_driver_server.control.handshake_stage_tag
                           : 255u));
        if (result.process_status ==
                Common_ProtocolImplementation_NeedMoreInput &&
            read_len == 0u && total_len < TLS13_SERVER_RX_CAP) {
          read_len = Common_TCP_read(
              driver->channel,
              driver->verified_driver.server_driver_raw + total_len,
              TLS13_SERVER_RX_CAP - total_len);
          total_len += read_len;
          server_trace("server read appended=%zu total=%zu", read_len, total_len);
          if (read_len == 0u) {
            return driver_fail(driver, "endpoint TCP read returned no data");
          }
          server_endpoint_action retry_action =
              TLS13_Impl_Server_Endpoint_server_endpoint_next_action(srv, frame);
          if (retry_action.tag != Common_ProtocolEndpoint_EndpointNeedInput) {
            TLS13_Impl_Server_Endpoint_server_endpoint_cancel_action(
                srv,
                frame,
                retry_action);
            return driver_fail(driver, "endpoint no longer needs input after read retry");
          }
          result = TLS13_Impl_Server_Endpoint_server_run_buffered_network_action(
              srv,
              frame,
              driver->channel,
              retry_action.case_EndpointNeedInput,
              total_len);
          server_trace(
              "server network retry status=%u consumed=%zu app=%zu net=%zu total=%zu control=%u stage=%u",
              (unsigned)result.process_status,
              result.process_consumed_len,
              result.process_app_len,
              result.process_produced_len,
              total_len,
              (unsigned)(driver->verified_driver.server_driver_server.control.control_tag != NULL
                             ? *driver->verified_driver.server_driver_server.control.control_tag
                             : 255u),
              (unsigned)(driver->verified_driver.server_driver_server.control.handshake_stage_tag != NULL
                             ? *driver->verified_driver.server_driver_server.control.handshake_stage_tag
                             : 255u));
        }
        if (server_compact_input(driver, result, total_len) != 0) {
          return 1;
        }
        if (result.process_status == Common_ProtocolImplementation_StepOk) {
          if (result.process_app_len != 0u) {
            if (produced_app_len != NULL) {
              *produced_app_len = result.process_app_len;
            }
            if (stop_on_application_data) {
              return 0;
            }
          }
        } else if (result.process_status !=
                   Common_ProtocolImplementation_NeedMoreInput) {
          return driver_fail(
              driver,
              "endpoint network action returned process status %u",
              (unsigned)result.process_status);
        } else if (read_len == 0u) {
          return driver_fail(driver, "endpoint needs more input after empty read");
        }
        break;
      }
      case Common_ProtocolEndpoint_EndpointDone:
        TLS13_Impl_Server_Endpoint_server_endpoint_cancel_action(
            srv,
            frame,
            action);
        return 0;
      case Common_ProtocolEndpoint_EndpointFailed:
      default:
        TLS13_Impl_Server_Endpoint_server_endpoint_cancel_action(
            srv,
            frame,
            action);
        return driver_fail(driver, "endpoint next action failed");
    }
  }
  return driver_fail(driver, "endpoint workflow exhausted fuel");
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
  ensure_krml_globals_initialized();
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
  FStar_Pervasives_Native_option__Common_TCP_listener listener_opt =
      Common_TCP_listen_tcp((uint8_t *)bind_host, bind_host_len, port);
  if (listener_opt.tag != FStar_Pervasives_Native_Some) {
    driver->verified_driver = verified_driver;
    driver->connected = false;
    driver_fail(driver, "TCP listen on %s:%u failed", bind_host, (unsigned)port);
    *out = driver;
    return 1;
  }
  FStar_Pervasives_Native_option__Common_TCP_channel ch_opt =
      Common_TCP_accept_tcp(listener_opt.v);
  Common_TCP_close_listener(listener_opt.v);
  if (ch_opt.tag != FStar_Pervasives_Native_Some) {
    driver->verified_driver = verified_driver;
    driver->connected = false;
    driver_fail(driver, "TCP accept on %s:%u failed", bind_host, (unsigned)port);
    *out = driver;
    return 1;
  }

  driver->verified_driver = verified_driver;
  driver->channel = ch_opt.v;
  driver->certificate_chain_len = certificate_chain_len;
  server_set_channel(&driver->verified_driver, ch_opt.v);
  if (server_endpoint_run(
          driver,
          driver->verified_driver.server_driver_app_out,
          TLS13_SERVER_APP_OUT_CAP,
          NULL,
          false,
          true,
          false,
          TLS13_SERVER_DRIVER_NETWORK_FUEL) != 0) {
    Common_TCP_close(ch_opt.v);
    server_clear_channel(&driver->verified_driver);
    *out = driver;
    return 1;
  }

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
  uint8_t *payload_input =
      payload_len == 0u ? &empty_payload : (uint8_t *)payload;
  TLS13_Impl_CanonicalTypes_server_local_event ev =
      TLS13_Impl_Server_CanonicalQueries_server_local_event_of_kind(
          TLS13_Impl_Server_Types_LocalSendApplicationData);
  TLS13_Impl_Server_CanonicalProtocol_tls_server_local_frame local_frame = {
      .tls_server_local_payload = payload_input,
      .tls_server_local_payload_len = payload_len,
      .tls_server_local_app_out = driver->verified_driver.server_driver_app_out,
      .tls_server_local_app_out_len = TLS13_SERVER_APP_OUT_CAP,
  };
  return server_endpoint_do_local(
      driver,
      ev,
      local_frame,
      driver->verified_driver.server_driver_app_out,
      TLS13_SERVER_APP_OUT_CAP,
      false);
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

  if (server_endpoint_run(
          driver,
          out,
          out_cap,
          out_len,
          true,
          false,
          false,
          TLS13_SERVER_DRIVER_NETWORK_FUEL) != 0) {
    return 1;
  }
  return 0;
}

int tls13_server_driver_close(tls13_server_driver *driver, bool wait_for_peer) {
  if (driver == NULL) {
    return 1;
  }
  if (!driver->connected) {
    return 0;
  }

  TLS13_Impl_CanonicalTypes_server_local_event ev =
      TLS13_Impl_Server_CanonicalQueries_server_local_event_of_kind(
          TLS13_Impl_Server_Types_LocalSendCloseNotify);
  TLS13_Impl_Server_CanonicalProtocol_tls_server_local_frame local_frame = {
      .tls_server_local_payload =
          driver->verified_driver.server_driver_empty_payload,
      .tls_server_local_payload_len = 0u,
      .tls_server_local_app_out = driver->verified_driver.server_driver_app_out,
      .tls_server_local_app_out_len = TLS13_SERVER_APP_OUT_CAP,
  };
  int rc = server_endpoint_do_local(
      driver,
      ev,
      local_frame,
      driver->verified_driver.server_driver_app_out,
      TLS13_SERVER_APP_OUT_CAP,
      false);
  if (rc == 0 && wait_for_peer) {
    rc = server_endpoint_run(
        driver,
        driver->verified_driver.server_driver_app_out,
        TLS13_SERVER_APP_OUT_CAP,
        NULL,
        false,
        false,
        true,
        TLS13_SERVER_DRIVER_NETWORK_FUEL);
  }
  if (driver->channel != NULL) {
    Common_TCP_close(driver->channel);
    driver->channel = NULL;
  }
  server_clear_channel(&driver->verified_driver);
  driver->connected = false;
  return rc;
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

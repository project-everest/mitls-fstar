#include "tls13_client_engine.h"

#include "TLS13_Impl_Client_Engine.h"

#include <stdbool.h>
#include <stdlib.h>

struct tls13_client_engine_s {
  TLS13_Impl_Client_Engine_client_engine verified_engine;
  tls13_client_engine_action last_action;
};

static bool capacities_match(void) {
  return
      TLS13_Impl_Client_Engine_engine_network_out_capacity ==
          TLS13_CLIENT_ENGINE_NETWORK_OUT_CAPACITY &&
      TLS13_Impl_Client_Engine_engine_app_out_capacity ==
          TLS13_CLIENT_ENGINE_APPLICATION_OUT_CAPACITY &&
      TLS13_Impl_Client_Engine_engine_certificate_chain_capacity ==
          TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_CAPACITY &&
      TLS13_Impl_Client_Engine_engine_certificate_chain_entries ==
          TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES &&
      TLS13_Impl_Client_Engine_engine_certificate_verify_input_capacity ==
          TLS13_CLIENT_ENGINE_CERTIFICATE_VERIFY_INPUT_CAPACITY &&
      TLS13_Impl_Client_Engine_engine_signature_capacity ==
          TLS13_CLIENT_ENGINE_SIGNATURE_CAPACITY &&
      TLS13_Impl_Client_Engine_engine_public_key_capacity ==
          TLS13_CLIENT_ENGINE_PUBLIC_KEY_CAPACITY;
}

static bool output_buffers_valid(
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity) {
  return network_out != NULL &&
      network_out_capacity >= TLS13_CLIENT_ENGINE_NETWORK_OUT_CAPACITY &&
      application_out != NULL &&
      application_out_capacity >= TLS13_CLIENT_ENGINE_APPLICATION_OUT_CAPACITY;
}

static tls13_client_engine_action map_action(
    TLS13_Impl_Client_Engine_engine_action action) {
  switch (action) {
    case TLS13_Impl_Client_Engine_EngineProgress:
      return TLS13_CLIENT_ENGINE_PROGRESS;
    case TLS13_Impl_Client_Engine_EngineNeedNetworkInput:
      return TLS13_CLIENT_ENGINE_NEED_NETWORK_INPUT;
    case TLS13_Impl_Client_Engine_EngineNeedCertificateVerification:
      return TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_VERIFICATION;
    case TLS13_Impl_Client_Engine_EngineNeedCertificateSignatureVerification:
      return TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_SIGNATURE_VERIFICATION;
    case TLS13_Impl_Client_Engine_EngineNetworkOutput:
      return TLS13_CLIENT_ENGINE_NETWORK_OUTPUT;
    case TLS13_Impl_Client_Engine_EngineApplicationData:
      return TLS13_CLIENT_ENGINE_APPLICATION_DATA;
    case TLS13_Impl_Client_Engine_EngineReady:
      return TLS13_CLIENT_ENGINE_READY;
    case TLS13_Impl_Client_Engine_EngineClosing:
      return TLS13_CLIENT_ENGINE_CLOSING;
    case TLS13_Impl_Client_Engine_EngineClosed:
      return TLS13_CLIENT_ENGINE_CLOSED;
    case TLS13_Impl_Client_Engine_EngineFailed:
    default:
      return TLS13_CLIENT_ENGINE_FAILED;
  }
}

static tls13_client_engine_status map_status(
    TLS13_Impl_Endpoint_Types_endpoint_status status) {
  switch (status) {
    case TLS13_Impl_Endpoint_Types_StepOk:
      return TLS13_CLIENT_ENGINE_STATUS_OK;
    case TLS13_Impl_Endpoint_Types_NeedMoreInput:
      return TLS13_CLIENT_ENGINE_STATUS_NEED_MORE_INPUT;
    case TLS13_Impl_Endpoint_Types_DecodeError:
      return TLS13_CLIENT_ENGINE_STATUS_DECODE_ERROR;
    case TLS13_Impl_Endpoint_Types_IllegalTransition:
      return TLS13_CLIENT_ENGINE_STATUS_ILLEGAL_TRANSITION;
    case TLS13_Impl_Endpoint_Types_OutputBufferTooSmall:
      return TLS13_CLIENT_ENGINE_STATUS_OUTPUT_BUFFER_TOO_SMALL;
    case TLS13_Impl_Endpoint_Types_ConnectionFailed:
    default:
      return TLS13_CLIENT_ENGINE_STATUS_CONNECTION_FAILED;
  }
}

static void store_result(
    tls13_client_engine *engine,
    TLS13_Impl_Client_Engine_engine_step_result verified_result,
    tls13_client_engine_result *result) {
  result->action = map_action(verified_result.engine_step_action);
  result->status = map_status(verified_result.engine_step_status);
  result->consumed_len = verified_result.engine_step_consumed_len;
  result->network_out_len = verified_result.engine_step_network_out_len;
  result->application_out_len = verified_result.engine_step_app_out_len;
  engine->last_action = result->action;
}

int tls13_client_engine_new(
    tls13_client_engine **out,
    const uint8_t *server_name,
    size_t server_name_len,
    const uint8_t *trust_context,
    size_t trust_context_len,
    size_t validation_time_seconds) {
  static uint8_t empty;
  if (out == NULL) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  *out = NULL;
  if ((server_name == NULL && server_name_len != 0u) ||
      (trust_context == NULL && trust_context_len != 0u) ||
      server_name_len > TLS13_CLIENT_ENGINE_MAX_SERVER_NAME_LEN ||
      trust_context_len > TLS13_CLIENT_ENGINE_MAX_TRUST_CONTEXT_LEN) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (!capacities_match()) {
    return TLS13_CLIENT_ENGINE_ERROR_INTERNAL;
  }

  tls13_client_engine *engine = malloc(sizeof *engine);
  if (engine == NULL) {
    return TLS13_CLIENT_ENGINE_ERROR_ALLOCATION;
  }
  engine->verified_engine = TLS13_Impl_Client_Engine_new_engine(
      (uint8_t *)(uintptr_t)(server_name_len == 0u ? &empty : server_name),
      server_name_len,
      (uint8_t *)(uintptr_t)(trust_context_len == 0u ? &empty : trust_context),
      trust_context_len,
      validation_time_seconds);
  engine->last_action = TLS13_CLIENT_ENGINE_PROGRESS;
  *out = engine;
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_poll(
    tls13_client_engine *engine,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result) {
  if (engine == NULL || result == NULL ||
      !output_buffers_valid(
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity)) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  store_result(
      engine,
      TLS13_Impl_Client_Engine_poll(
          engine->verified_engine,
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity),
      result);
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_feed_network(
    tls13_client_engine *engine,
    const uint8_t *network_input,
    size_t network_input_len,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result) {
  static uint8_t empty;
  if (engine == NULL || result == NULL ||
      (network_input == NULL && network_input_len != 0u) ||
      !output_buffers_valid(
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity)) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (engine->last_action != TLS13_CLIENT_ENGINE_NEED_NETWORK_INPUT) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE;
  }
  store_result(
      engine,
      TLS13_Impl_Client_Engine_feed_network(
          engine->verified_engine,
          (uint8_t *)(uintptr_t)(
              network_input_len == 0u ? &empty : network_input),
          network_input_len,
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity),
      result);
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_copy_certificate_chain(
    tls13_client_engine *engine,
    uint8_t *chain_out,
    size_t chain_out_capacity,
    size_t *offsets_out,
    size_t offsets_out_capacity,
    size_t *lengths_out,
    size_t lengths_out_capacity,
    tls13_client_engine_certificate_chain *chain) {
  if (engine == NULL || chain_out == NULL || offsets_out == NULL ||
      lengths_out == NULL || chain == NULL ||
      chain_out_capacity < TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_CAPACITY ||
      offsets_out_capacity < TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES ||
      lengths_out_capacity < TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (engine->last_action !=
      TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_VERIFICATION) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE;
  }
  TLS13_Impl_ConnectionState_Repr_certificate_chain_snapshot snapshot =
      TLS13_Impl_Client_Engine_copy_certificate_chain(
          engine->verified_engine,
          chain_out,
          TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_CAPACITY,
          offsets_out,
          TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES,
          lengths_out,
          TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES);
  chain->bytes_len = snapshot.certificate_chain_bytes_len;
  chain->certificate_count = snapshot.certificate_chain_cert_count;
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_copy_certificate_verify_request(
    tls13_client_engine *engine,
    uint8_t *input_out,
    size_t input_out_capacity,
    uint8_t *signature_out,
    size_t signature_out_capacity,
    tls13_client_engine_certificate_verify_request *request) {
  if (engine == NULL || input_out == NULL || signature_out == NULL ||
      request == NULL ||
      input_out_capacity <
          TLS13_CLIENT_ENGINE_CERTIFICATE_VERIFY_INPUT_CAPACITY ||
      signature_out_capacity < TLS13_CLIENT_ENGINE_SIGNATURE_CAPACITY) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (engine->last_action !=
      TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_SIGNATURE_VERIFICATION) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE;
  }
  TLS13_Impl_Client_Engine_certificate_verify_request verified_request =
      TLS13_Impl_Client_Engine_copy_certificate_verify_request(
          engine->verified_engine,
          input_out,
          TLS13_CLIENT_ENGINE_CERTIFICATE_VERIFY_INPUT_CAPACITY,
          signature_out,
          TLS13_CLIENT_ENGINE_SIGNATURE_CAPACITY);
  request->input_len = verified_request.certificate_verify_input_len;
  request->signature_scheme =
      verified_request.certificate_verify_signature_scheme;
  request->signature_len =
      verified_request.certificate_verify_signature_len;
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_complete_certificate_verification(
    tls13_client_engine *engine,
    const uint8_t *authenticated_public_key,
    size_t authenticated_public_key_len,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result) {
  static uint8_t empty;
  if (engine == NULL || result == NULL ||
      (authenticated_public_key == NULL &&
       authenticated_public_key_len != 0u) ||
      authenticated_public_key_len >
          TLS13_CLIENT_ENGINE_PUBLIC_KEY_CAPACITY ||
      !output_buffers_valid(
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity)) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (engine->last_action !=
      TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_VERIFICATION) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE;
  }
  store_result(
      engine,
      TLS13_Impl_Client_Engine_complete_certificate_verification(
          engine->verified_engine,
          (uint8_t *)(uintptr_t)(
              authenticated_public_key_len == 0u
                  ? &empty
                  : authenticated_public_key),
          authenticated_public_key_len,
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity),
      result);
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_complete_certificate_signature_verification(
    tls13_client_engine *engine,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result) {
  if (engine == NULL || result == NULL ||
      !output_buffers_valid(
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity)) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (engine->last_action !=
      TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_SIGNATURE_VERIFICATION) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE;
  }
  store_result(
      engine,
      TLS13_Impl_Client_Engine_complete_certificate_signature_verification(
          engine->verified_engine,
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity),
      result);
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_send_application_data(
    tls13_client_engine *engine,
    const uint8_t *payload,
    size_t payload_len,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result) {
  static uint8_t empty;
  if (engine == NULL || result == NULL ||
      (payload == NULL && payload_len != 0u) ||
      payload_len > TLS13_CLIENT_ENGINE_MAX_APPLICATION_DATA_LEN ||
      !output_buffers_valid(
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity)) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (engine->last_action != TLS13_CLIENT_ENGINE_READY) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE;
  }
  store_result(
      engine,
      TLS13_Impl_Client_Engine_send_application_data(
          engine->verified_engine,
          (uint8_t *)(uintptr_t)(payload_len == 0u ? &empty : payload),
          payload_len,
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity),
      result);
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

int tls13_client_engine_send_close_notify(
    tls13_client_engine *engine,
    uint8_t *network_out,
    size_t network_out_capacity,
    uint8_t *application_out,
    size_t application_out_capacity,
    tls13_client_engine_result *result) {
  if (engine == NULL || result == NULL ||
      !output_buffers_valid(
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity)) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT;
  }
  if (engine->last_action != TLS13_CLIENT_ENGINE_READY) {
    return TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE;
  }
  store_result(
      engine,
      TLS13_Impl_Client_Engine_send_close_notify(
          engine->verified_engine,
          network_out,
          network_out_capacity,
          application_out,
          application_out_capacity),
      result);
  return TLS13_CLIENT_ENGINE_SUCCESS;
}

void tls13_client_engine_free(tls13_client_engine *engine) {
  if (engine == NULL) {
    return;
  }
  TLS13_Impl_Client_Engine_free_engine(engine->verified_engine);
  free(engine);
}

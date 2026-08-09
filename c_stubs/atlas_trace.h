#ifndef ATLAS_TRACE_H
#define ATLAS_TRACE_H

#include <stdbool.h>
#include <stdint.h>

/*
 * KaRaMeL emits the external declaration in a generated header. When that
 * header is available, include it before defining the call-site macro below.
 */
#if defined(__has_include)
#if __has_include("internal/TLS13_Trace.h")
#include "internal/TLS13_Trace.h"
#elif __has_include("TLS13_Trace.h")
#include "TLS13_Trace.h"
#endif
#endif

#ifndef ATLAS_ENABLE_LOGGING
#define ATLAS_ENABLE_LOGGING 0
#endif

#define TLS13_TRACE_RECORD_STATE_NEW ((uint32_t)1000U)
#define TLS13_TRACE_RECORD_STATE_FREE ((uint32_t)1001U)
#define TLS13_TRACE_RECORD_SEQUENCE_ADVANCE ((uint32_t)1010U)
#define TLS13_TRACE_RECORD_SEQUENCE_RESTORE ((uint32_t)1011U)
#define TLS13_TRACE_RECORD_INSTALL_HANDSHAKE_KEYS ((uint32_t)1020U)
#define TLS13_TRACE_RECORD_INSTALL_APPLICATION_KEYS ((uint32_t)1021U)
#define TLS13_TRACE_RECORD_SEAL_BEGIN ((uint32_t)1030U)
#define TLS13_TRACE_RECORD_SEAL_SUCCESS ((uint32_t)1031U)
#define TLS13_TRACE_RECORD_SEAL_FAILURE ((uint32_t)1032U)
#define TLS13_TRACE_RECORD_OPEN_BEGIN ((uint32_t)1040U)
#define TLS13_TRACE_RECORD_OPEN_SUCCESS ((uint32_t)1041U)
#define TLS13_TRACE_RECORD_OPEN_FAILURE ((uint32_t)1042U)

#define TLS13_TRACE_CLIENT_NEW ((uint32_t)2000U)
#define TLS13_TRACE_CLIENT_FREE ((uint32_t)2001U)
#define TLS13_TRACE_CLIENT_LOCAL_EVENT_BEGIN ((uint32_t)2010U)
#define TLS13_TRACE_CLIENT_LOCAL_EVENT_END ((uint32_t)2011U)
#define TLS13_TRACE_CLIENT_NETWORK_BEGIN ((uint32_t)2020U)
#define TLS13_TRACE_CLIENT_NETWORK_NEED_MORE ((uint32_t)2021U)
#define TLS13_TRACE_CLIENT_NETWORK_DECODE_ERROR ((uint32_t)2022U)
#define TLS13_TRACE_CLIENT_NETWORK_RECORD ((uint32_t)2023U)
#define TLS13_TRACE_CLIENT_NETWORK_END ((uint32_t)2024U)
#define TLS13_TRACE_CLIENT_PROTECTED_HEAD ((uint32_t)2030U)
#define TLS13_TRACE_CLIENT_PROTECTED_DRAIN ((uint32_t)2031U)
#define TLS13_TRACE_CLIENT_PROTECTED_EMPTY ((uint32_t)2032U)
#define TLS13_TRACE_CLIENT_PROTECTED_ERROR ((uint32_t)2033U)
#define TLS13_TRACE_CLIENT_PROTECTED_BUFFER ((uint32_t)2034U)
#define TLS13_TRACE_CLIENT_HANDSHAKE_MESSAGE ((uint32_t)2040U)

#define TLS13_TRACE_ENGINE_NEW ((uint32_t)2100U)
#define TLS13_TRACE_ENGINE_POLL_BEGIN ((uint32_t)2110U)
#define TLS13_TRACE_ENGINE_POLL_END ((uint32_t)2111U)
#define TLS13_TRACE_ENGINE_FEED_BEGIN ((uint32_t)2120U)
#define TLS13_TRACE_ENGINE_FEED_END ((uint32_t)2121U)
#define TLS13_TRACE_ENGINE_CERTIFICATE_CHAIN ((uint32_t)2130U)
#define TLS13_TRACE_ENGINE_CERTIFICATE_VERIFIED ((uint32_t)2131U)
#define TLS13_TRACE_ENGINE_CERTIFICATE_SIGNATURE_VERIFIED ((uint32_t)2132U)
#define TLS13_TRACE_ENGINE_SEND_APPLICATION ((uint32_t)2140U)
#define TLS13_TRACE_ENGINE_SEND_CLOSE ((uint32_t)2141U)
#define TLS13_TRACE_ENGINE_FREE ((uint32_t)2150U)

#define TLS13_TRACE_SERVER_NEW ((uint32_t)3000U)
#define TLS13_TRACE_SERVER_FREE ((uint32_t)3001U)
#define TLS13_TRACE_SERVER_LOCAL_EVENT_BEGIN ((uint32_t)3010U)
#define TLS13_TRACE_SERVER_LOCAL_EVENT_END ((uint32_t)3011U)
#define TLS13_TRACE_SERVER_NETWORK_BEGIN ((uint32_t)3020U)
#define TLS13_TRACE_SERVER_NETWORK_NEED_MORE ((uint32_t)3021U)
#define TLS13_TRACE_SERVER_NETWORK_DECODE_ERROR ((uint32_t)3022U)
#define TLS13_TRACE_SERVER_NETWORK_RECORD ((uint32_t)3023U)
#define TLS13_TRACE_SERVER_NETWORK_END ((uint32_t)3024U)
#define TLS13_TRACE_SERVER_HANDSHAKE_MESSAGE ((uint32_t)3040U)

uint64_t atlas_trace_new_connection(void);
void atlas_trace_set_connection(uint64_t connection);

#if ATLAS_ENABLE_LOGGING
void atlas_trace_emit(
    uint32_t event,
    uint64_t arg0,
    uint64_t arg1,
    uint64_t arg2);
#define TLS13_Trace_emit(event, arg0, arg1, arg2) \
  atlas_trace_emit((event), (arg0), (arg1), (arg2))
#else
#define atlas_trace_new_connection() ((uint64_t)0U)
#define atlas_trace_set_connection(connection) ((void)0)
#define TLS13_Trace_emit(event, arg0, arg1, arg2) \
  ((void)0)
#endif

#endif

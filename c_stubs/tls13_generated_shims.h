#ifndef TLS13_GENERATED_SHIMS_H
#define TLS13_GENERATED_SHIMS_H

/*
 * This header is force-included only while compiling KaRaMeL-generated C.
 * It preloads generated declarations first, then exposes the explicit C
 * parser/backend boundary used for modules that are not currently extracted
 * to C, plus generic C primitives needed by generated Pulse code.
 */

#include <stddef.h>
#include <stdint.h>
#include <string.h>

static inline void TLS13_Generated_copy_array_slice_to_array(
    const uint8_t *src,
    size_t src_total_len,
    size_t src_offset,
    size_t copy_len,
    uint8_t *dst,
    size_t dst_len,
    size_t dst_offset) {
  (void)src_total_len;
  (void)dst_len;
  if (copy_len != 0u) {
    memcpy(dst + dst_offset, src + src_offset, copy_len);
  }
}

#define TLS13_Impl_Serializer_Common_copy_array_slice_to_array( \
    src, src_total_len, src_offset, copy_len, dst, dst_len, dst_offset, ...) \
  TLS13_Generated_copy_array_slice_to_array( \
      (src), (src_total_len), (src_offset), (copy_len), (dst), (dst_len), (dst_offset))

#define TLS13_Impl_Serializer_copy_array_slice_to_array( \
    src, src_total_len, src_offset, copy_len, dst, dst_len, dst_offset, ...) \
  TLS13_Generated_copy_array_slice_to_array( \
      (src), (src_total_len), (src_offset), (copy_len), (dst), (dst_len), (dst_offset))

#if defined(__has_include)
#if __has_include("TLS13_Crypto.h")
#include "TLS13_Crypto.h"
#endif
#if __has_include("TLS13_Record.h")
#include "TLS13_Record.h"
#endif
#if __has_include("TLS13_Impl_Messages.h")
#include "TLS13_Impl_Messages.h"
#endif
#if __has_include("TLS13_Impl_ConnectionState_Bounds.h")
#include "TLS13_Impl_ConnectionState_Bounds.h"
#endif
#if __has_include("TLS13_Impl_ConnectionState_Repr.h")
#include "TLS13_Impl_ConnectionState_Repr.h"
#endif
#if __has_include("TLS13_Impl_ConnectionState_Queries.h")
#include "TLS13_Impl_ConnectionState_Queries.h"
#endif
#if __has_include("TLS13_Impl_Serializer.h")
#include "TLS13_Impl_Serializer.h"
#endif
#if __has_include("TLS13_Impl_Serializer_Common.h")
#include "TLS13_Impl_Serializer_Common.h"
#endif
#if __has_include("TLS13_Impl_Serializer_Finished.h")
#include "TLS13_Impl_Serializer_Finished.h"
#endif
#if __has_include("TLS13_Impl_Serializer_EncryptedExtensions.h")
#include "TLS13_Impl_Serializer_EncryptedExtensions.h"
#endif
#if __has_include("TLS13_Impl_Serializer_CertificateVerify.h")
#include "TLS13_Impl_Serializer_CertificateVerify.h"
#endif
#if __has_include("TLS13_Impl_Serializer_ServerHello.h")
#include "TLS13_Impl_Serializer_ServerHello.h"
#endif
#if __has_include("TLS13_Impl_Serializer_Certificate.h")
#include "TLS13_Impl_Serializer_Certificate.h"
#endif
#if __has_include("TLS13_Impl_Serializer_ProtectedRecord.h")
#include "TLS13_Impl_Serializer_ProtectedRecord.h"
#endif
#if __has_include("TLS13_Impl_Server_Types.h")
#include "TLS13_Impl_Server_Types.h"
#endif
#if __has_include("TLS13_Impl_Server_Material.h")
#include "TLS13_Impl_Server_Material.h"
#endif
#endif

#define TLS13_Impl_ConnectionState_Bounds_max_hostname_len \
  TLS13_Impl_ConnectionState_Bounds_max_hostname_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_public_key_len \
  TLS13_Impl_ConnectionState_Bounds_max_public_key_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_cipher_suites \
  TLS13_Impl_ConnectionState_Bounds_max_cipher_suites_sz
#define TLS13_Impl_ConnectionState_Bounds_max_signature_schemes \
  TLS13_Impl_ConnectionState_Bounds_max_signature_schemes_sz
#define TLS13_Impl_ConnectionState_Bounds_max_client_hello_len \
  TLS13_Impl_ConnectionState_Bounds_max_client_hello_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_server_hello_len \
  TLS13_Impl_ConnectionState_Bounds_max_server_hello_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_handshake_flight_len \
  TLS13_Impl_ConnectionState_Bounds_max_handshake_flight_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_transcript_len \
  TLS13_Impl_ConnectionState_Bounds_max_transcript_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_certificate_verify_input_len \
  TLS13_Impl_ConnectionState_Bounds_max_certificate_verify_input_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_trust_anchors_len \
  TLS13_Impl_ConnectionState_Bounds_max_trust_anchors_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_pending_plaintext_len \
  TLS13_Impl_ConnectionState_Bounds_max_pending_plaintext_len_sz
#define TLS13_Impl_ConnectionState_Bounds_max_pending_raw_len \
  TLS13_Impl_ConnectionState_Bounds_max_pending_raw_len_sz

#include "tls13_server_extraction_shims.h"
#include "tls13_connection_backend.h"

#endif

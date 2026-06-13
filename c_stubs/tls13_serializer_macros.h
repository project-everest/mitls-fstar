#ifndef TLS13_SERIALIZER_MACROS_H
#define TLS13_SERIALIZER_MACROS_H

#include "tls13_connection_backend.h"

#define TLS13_Impl_Serializer_encode_inner_plaintext_no_padding_slice( \
    plain, plain_total_len, plain_offset, plain_len, content_type, out, out_len, ...) \
  do { \
    size_t _tls13_plain_total_len = (plain_total_len); \
    size_t _tls13_plain_offset = (plain_offset); \
    size_t _tls13_plain_len = (plain_len); \
    size_t _tls13_out_len = (out_len); \
    if (_tls13_plain_offset <= _tls13_plain_total_len && \
        _tls13_plain_len <= _tls13_plain_total_len - _tls13_plain_offset && \
        _tls13_out_len == _tls13_plain_len + 1u) { \
      memcpy((out), (plain) + _tls13_plain_offset, _tls13_plain_len); \
      (out)[_tls13_plain_len] = (content_type); \
    } \
  } while (0)

#define TLS13_Impl_Serializer_serialize_application_data_header( \
    fragment_len, out, out_len, ...) \
  do { \
    size_t _tls13_fragment_len = (fragment_len); \
    if ((out_len) >= 5u && _tls13_fragment_len <= 0xffffu) { \
      (out)[0] = 23u; \
      (out)[1] = 0x03u; \
      (out)[2] = 0x03u; \
      (out)[3] = (uint8_t)((_tls13_fragment_len >> 8) & 0xffu); \
      (out)[4] = (uint8_t)(_tls13_fragment_len & 0xffu); \
    } \
  } while (0)

#define TLS13_Impl_Serializer_serialize_client_hello_from_start( \
    start_random, start_server_name, start_server_name_len, \
    start_key_share, start_cipher_suites, start_cipher_suites_len, \
    start_signature_schemes, start_signature_schemes_len, client_hello_present, l, \
    client_hello_bytes, client_hello_bytes_len, network_out, network_out_len, ...) \
  ((l).client_hello_server_name_len = *(start_server_name_len), \
   (l).client_hello_has_server_name = true, \
   (l).client_hello_cipher_suites_len = *(start_cipher_suites_len), \
   (l).client_hello_signature_schemes_len = *(start_signature_schemes_len), \
   TLS13_Connection_Backend_serialize_client_hello_from_start_impl( \
       (start_random), (start_server_name), (start_server_name_len), (start_key_share), \
       (start_cipher_suites), (start_cipher_suites_len), \
       (start_signature_schemes), (start_signature_schemes_len), \
       (client_hello_present), (l).client_hello_random, (l).client_hello_server_name, \
       (l).client_hello_key_share, (l).client_hello_cipher_suites, \
       (l).client_hello_signature_schemes, (client_hello_bytes), \
       (client_hello_bytes_len), (network_out), (network_out_len)))

#endif

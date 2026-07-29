// Copyright 2026 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#ifndef NET_SOCKET_VERIFIED_MITLS_CLIENT_SOCKET_H_
#define NET_SOCKET_VERIFIED_MITLS_CLIENT_SOCKET_H_

#include <memory>
#include <optional>
#include <string_view>
#include <vector>

#include "base/memory/raw_ptr.h"
#include "base/memory/scoped_refptr.h"
#include "net/base/completion_once_callback.h"
#include "net/base/net_export.h"
#include "net/socket/ssl_client_socket.h"

namespace mitls::chromium {
class Tls13ClientSocket;
}

namespace net {

class CertVerifyResult;
class HostPortPair;
class IOBuffer;
class SSLClientContext;
struct SSLConfig;

// Chromium's SSLClientSocket facade over the transport-neutral verified miTLS
// TLS 1.3 client engine. This initial integration profile is deliberately
// limited to X25519, ChaCha20-Poly1305, RSA-PSS-SHA256, and HTTP/1.1.
class NET_EXPORT_PRIVATE VerifiedMiTlsClientSocket final
    : public SSLClientSocket {
 public:
  VerifiedMiTlsClientSocket(SSLClientContext* context,
                            std::unique_ptr<StreamSocket> stream_socket,
                            const HostPortPair& host_and_port,
                            const SSLConfig& ssl_config);
  ~VerifiedMiTlsClientSocket() override;

  VerifiedMiTlsClientSocket(const VerifiedMiTlsClientSocket&) = delete;
  VerifiedMiTlsClientSocket& operator=(const VerifiedMiTlsClientSocket&) =
      delete;

  std::vector<uint8_t> GetECHRetryConfigs() override;
  std::vector<std::vector<uint8_t>> GetServerTrustAnchorIDs() override;

  int ExportKeyingMaterial(
      std::string_view label,
      std::optional<base::span<const uint8_t>> context,
      base::span<uint8_t> out) override;

  int Connect(CompletionOnceCallback callback) override;
  void Disconnect() override;
  int ConfirmHandshake(CompletionOnceCallback callback) override;
  bool IsConnected() const override;
  bool IsConnectedAndIdle() const override;
  int GetPeerAddress(IPEndPoint* address) const override;
  int GetLocalAddress(IPEndPoint* address) const override;
  const NetLogWithSource& NetLog() const override;
  bool WasEverUsed() const override;
  NextProto GetNegotiatedProtocol() const override;
  std::optional<std::string_view> GetPeerApplicationSettings() const override;
  bool GetSSLInfo(SSLInfo* ssl_info) override;
  int64_t GetTotalReceivedBytes() const override;
  void ApplySocketTag(const SocketTag& tag) override;

  int Read(IOBuffer* buf,
           int buf_len,
           CompletionOnceCallback callback) override;
  int Write(IOBuffer* buf,
            int buf_len,
            CompletionOnceCallback callback,
            const NetworkTrafficAnnotationTag& traffic_annotation) override;
  int SetReceiveBufferSize(int32_t size) override;
  int SetSendBufferSize(int32_t size) override;

 private:
  class TransportAdapter;
  class Authenticator;

  int MapCoreResult(int result) const;
  void OnConnectComplete(int result);
  void OnReadComplete(int result);
  void OnWriteComplete(int result);

  std::unique_ptr<mitls::chromium::Tls13ClientSocket> core_;
  raw_ptr<TransportAdapter> transport_adapter_;
  raw_ptr<Authenticator> authenticator_;

  CompletionOnceCallback connect_callback_;
  CompletionOnceCallback read_callback_;
  CompletionOnceCallback write_callback_;
  scoped_refptr<IOBuffer> read_buffer_;
  scoped_refptr<IOBuffer> write_buffer_;

  bool disconnected_ = false;
  bool was_ever_used_ = false;
  int initialization_error_ = 0;
};

}  // namespace net

#endif  // NET_SOCKET_VERIFIED_MITLS_CLIENT_SOCKET_H_

// Copyright 2026 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "net/socket/atlas_client_socket.h"

#include <ctime>
#include <string>
#include <utility>

#include "base/containers/span.h"
#include "base/functional/bind.h"
#include "base/memory/weak_ptr.h"
#include "crypto/signature_verifier.h"
#include "net/base/io_buffer.h"
#include "net/base/net_errors.h"
#include "net/cert/cert_verify_result.h"
#include "net/cert/cert_verifier.h"
#include "net/cert/x509_certificate.h"
#include "net/cert/x509_util.h"
#include "net/log/net_log_with_source.h"
#include "net/ssl/ssl_config.h"
#include "net/ssl/ssl_connection_status_flags.h"
#include "net/ssl/ssl_info.h"
#include "net/socket/socket_tag.h"
#include "net/traffic_annotation/network_traffic_annotation.h"
#include "third_party/boringssl/src/pki/parse_certificate.h"
#include "third_party/atlas/tls13_client_socket.h"

namespace net {
namespace {

constexpr uint16_t kTls13ChaCha20Poly1305Sha256 = 0x1303;
constexpr uint16_t kX25519 = 29;
constexpr uint16_t kRsaPssRsaeSha256 = 0x0804;

constexpr auto kAtlasTrafficAnnotation =
    DefineNetworkTrafficAnnotation("atlas_socket", R"(
      semantics {
        sender: "ATLAS TLS 1.3 client"
        description:
          "Carries HTTPS requests made by Chromium through the ATLAS "
          "TLS provider."
        trigger:
          "A Chromium HTTPS request while --use-atlas is enabled."
        data:
          "Encrypted HTTPS request and response data. The destination and "
          "content depend on the invoking Chromium feature."
        destination: WEBSITE
        internal {
          contacts {
            email: "security@chromium.org"
          }
        }
        user_data {
          type: WEB_CONTENT
        }
        last_reviewed: "2026-04-24"
      }
      policy {
        cookies_allowed: YES
        cookies_store: "user"
        setting:
          "This experimental provider is enabled only by the "
          "--use-atlas command-line switch."
        policy_exception_justification:
          "Experimental command-line-only TLS provider."
      })");

int ToPortableTransportResult(int result) {
  if (result > 0) {
    return result;
  }
  return atlas::chromium::kErrorConnectionClosed;
}

}  // namespace

class AtlasClientSocket::TransportAdapter final
    : public atlas::chromium::StreamSocket {
 public:
  explicit TransportAdapter(std::unique_ptr<net::StreamSocket> socket)
      : socket_(std::move(socket)) {}

  ~TransportAdapter() override { Disconnect(); }

  int Read(uint8_t* output,
           size_t output_capacity,
           atlas::chromium::CompletionCallback callback) override {
    CHECK(!read_buffer_);
    CHECK(output);
    CHECK_GT(output_capacity, 0u);
    read_output_ = output;
    read_buffer_ = base::MakeRefCounted<IOBufferWithSize>(output_capacity);
    int result = socket_->Read(
        read_buffer_.get(), static_cast<int>(output_capacity),
        base::BindOnce(&TransportAdapter::OnReadComplete,
                       weak_factory_.GetWeakPtr(), std::move(callback)));
    if (result == ERR_IO_PENDING) {
      return atlas::chromium::kIoPending;
    }
    return CompleteRead(result);
  }

  int Write(const uint8_t* input,
            size_t input_len,
            atlas::chromium::CompletionCallback callback) override {
    CHECK(!write_buffer_);
    CHECK(input);
    CHECK_GT(input_len, 0u);
    write_buffer_ = base::MakeRefCounted<IOBufferWithSize>(input_len);
    write_buffer_->span().copy_from(
        UNSAFE_BUFFERS(base::span(input, input_len)));
    int result = socket_->Write(
        write_buffer_.get(), static_cast<int>(input_len),
        base::BindOnce(&TransportAdapter::OnWriteComplete,
                       weak_factory_.GetWeakPtr(), std::move(callback)),
        kAtlasTrafficAnnotation);
    if (result == ERR_IO_PENDING) {
      return atlas::chromium::kIoPending;
    }
    return CompleteWrite(result);
  }

  void Disconnect() override {
    weak_factory_.InvalidateWeakPtrs();
    read_buffer_.reset();
    write_buffer_.reset();
    read_output_ = nullptr;
    if (socket_) {
      socket_->Disconnect();
    }
  }

  net::StreamSocket* socket() const { return socket_.get(); }
  int last_error() const { return last_error_; }

 private:
  int CompleteRead(int result) {
    if (result > 0) {
      UNSAFE_BUFFERS(base::span<uint8_t>(
          read_output_.get(), static_cast<size_t>(result)))
          .copy_from(read_buffer_->first(result));
    } else {
      last_error_ = result == 0 ? ERR_CONNECTION_CLOSED : result;
    }
    read_buffer_.reset();
    read_output_ = nullptr;
    return ToPortableTransportResult(result);
  }

  int CompleteWrite(int result) {
    if (result <= 0) {
      last_error_ = result == 0 ? ERR_CONNECTION_CLOSED : result;
    }
    write_buffer_.reset();
    return ToPortableTransportResult(result);
  }

  void OnReadComplete(atlas::chromium::CompletionCallback callback,
                      int result) {
    std::move(callback)(CompleteRead(result));
  }

  void OnWriteComplete(atlas::chromium::CompletionCallback callback,
                       int result) {
    std::move(callback)(CompleteWrite(result));
  }

  std::unique_ptr<net::StreamSocket> socket_;
  scoped_refptr<IOBufferWithSize> read_buffer_;
  scoped_refptr<IOBufferWithSize> write_buffer_;
  raw_ptr<uint8_t> read_output_ = nullptr;
  int last_error_ = OK;
  base::WeakPtrFactory<TransportAdapter> weak_factory_{this};
};

class AtlasClientSocket::Authenticator final
    : public atlas::chromium::ServerAuthenticator {
 public:
  Authenticator(SSLClientContext* context,
                const SSLConfig& ssl_config,
                const NetLogWithSource& net_log)
      : context_(context), ssl_config_(ssl_config), net_log_(net_log) {}

  ~Authenticator() override { Cancel(); }

  int VerifyCertificateChain(
      const std::string& hostname,
      const atlas::chromium::CertificateChain& chain,
      uint64_t validation_time_seconds,
      atlas::chromium::CompletionCallback callback) override {
    CHECK(!request_);
    std::vector<std::string_view> der_chain;
    der_chain.reserve(chain.der_certificates.size());
    for (const auto& certificate : chain.der_certificates) {
      der_chain.emplace_back(
          reinterpret_cast<const char*>(certificate.data()),
          certificate.size());
    }
    unverified_cert_ = X509Certificate::CreateFromDERCertChain(der_chain);
    if (!unverified_cert_ || !ExtractPublicKey()) {
      last_error_ = ERR_SSL_SERVER_CERT_BAD_FORMAT;
      return atlas::chromium::kErrorCertificate;
    }
    int result = context_->cert_verifier()->Verify(
        CertVerifier::RequestParams(unverified_cert_, hostname,
                                    ssl_config_.GetCertVerifyFlags(), {}, {}),
        &verify_result_,
        base::BindOnce(&Authenticator::OnVerifyComplete,
                       weak_factory_.GetWeakPtr(), std::move(callback)),
        &request_, net_log_);
    if (result == ERR_IO_PENDING) {
      return atlas::chromium::kIoPending;
    }
    return MapVerifyResult(result);
  }

  const std::vector<uint8_t>& authenticated_public_key_der() const override {
    return public_key_der_;
  }

  bool VerifyCertificateSignature(uint16_t signature_scheme,
                                  const uint8_t* input,
                                  size_t input_len,
                                  const uint8_t* signature,
                                  size_t signature_len) const override {
    if (signature_scheme != kRsaPssRsaeSha256 || !unverified_cert_) {
      return false;
    }
    crypto::SignatureVerifier verifier;
    if (!x509_util::SignatureVerifierInitWithCertificate(
            &verifier, crypto::SignatureVerifier::RSA_PSS_SHA256,
            UNSAFE_BUFFERS(base::span(signature, signature_len)),
            unverified_cert_->cert_buffer())) {
      return false;
    }
    verifier.VerifyUpdate(UNSAFE_BUFFERS(base::span(input, input_len)));
    return verifier.VerifyFinal();
  }

  void Cancel() override {
    request_.reset();
    weak_factory_.InvalidateWeakPtrs();
  }

  int last_error() const { return last_error_; }

  void PopulateSSLInfo(SSLInfo* ssl_info, uint16_t signature_scheme) const {
    *ssl_info = SSLInfo();
    ssl_info->cert =
        verify_result_.verified_cert ? verify_result_.verified_cert
                                     : unverified_cert_;
    ssl_info->unverified_cert = unverified_cert_;
    ssl_info->cert_status = verify_result_.cert_status;
    ssl_info->is_issued_by_known_root =
        verify_result_.is_issued_by_known_root;
    ssl_info->public_key_hashes = verify_result_.public_key_hashes;
    ssl_info->signed_certificate_timestamps = verify_result_.scts;
    ssl_info->ct_policy_compliance = verify_result_.policy_compliance;
#if BUILDFLAG(CHROME_ROOT_STORE_SUPPORTED)
    ssl_info->crs_root_id = verify_result_.crs_root_id;
#endif
    ssl_info->key_exchange_group = kX25519;
    ssl_info->peer_signature_algorithm = signature_scheme;
    SSLConnectionStatusSetCipherSuite(
        kTls13ChaCha20Poly1305Sha256, &ssl_info->connection_status);
    SSLConnectionStatusSetVersion(
        SSL_CONNECTION_VERSION_TLS1_3, &ssl_info->connection_status);
    ssl_info->handshake_type = SSLInfo::HANDSHAKE_FULL;
  }

  bool has_certificate() const { return unverified_cert_ != nullptr; }

 private:
  bool ExtractPublicKey() {
    bssl::der::Input tbs_certificate_tlv;
    bssl::der::Input signature_algorithm_tlv;
    bssl::der::BitString signature_value;
    bssl::ParsedTbsCertificate tbs;
    if (!bssl::ParseCertificate(
            bssl::der::Input(unverified_cert_->cert_span()),
            &tbs_certificate_tlv, &signature_algorithm_tlv, &signature_value,
            nullptr) ||
        !bssl::ParseTbsCertificate(
            tbs_certificate_tlv,
            x509_util::DefaultParseCertificateOptions(), &tbs, nullptr)) {
      return false;
    }
    UNSAFE_BUFFERS(public_key_der_.assign(
        tbs.spki_tlv.data(),
        tbs.spki_tlv.data() + tbs.spki_tlv.size()));
    return !public_key_der_.empty();
  }

  int MapVerifyResult(int result) {
    request_.reset();
    if (result == OK) {
      return atlas::chromium::kSuccess;
    }

    if (ssl_config_.ignore_certificate_errors) {
      if (!verify_result_.verified_cert) {
        verify_result_.verified_cert = unverified_cert_;
      }
      return atlas::chromium::kSuccess;
    }
    CertStatus allowed_status = 0;
    if (ssl_config_.IsAllowedBadCert(unverified_cert_.get(), &allowed_status)) {
      verify_result_.Reset();
      verify_result_.cert_status = allowed_status;
      verify_result_.verified_cert = unverified_cert_;
      return atlas::chromium::kSuccess;
    }
    last_error_ = result;
    return atlas::chromium::kErrorCertificate;
  }

  void OnVerifyComplete(atlas::chromium::CompletionCallback callback,
                        int result) {
    std::move(callback)(MapVerifyResult(result));
  }

  raw_ptr<SSLClientContext> context_;
  SSLConfig ssl_config_;
  NetLogWithSource net_log_;
  scoped_refptr<X509Certificate> unverified_cert_;
  CertVerifyResult verify_result_;
  std::vector<uint8_t> public_key_der_;
  std::unique_ptr<CertVerifier::Request> request_;
  int last_error_ = OK;
  base::WeakPtrFactory<Authenticator> weak_factory_{this};
};

AtlasClientSocket::AtlasClientSocket(
    SSLClientContext* context,
    std::unique_ptr<StreamSocket> stream_socket,
    const HostPortPair& host_and_port,
    const SSLConfig& ssl_config) {
  if ((ssl_config.version_min_override &&
       *ssl_config.version_min_override > SSL_PROTOCOL_VERSION_TLS1_3) ||
      (ssl_config.version_max_override &&
       *ssl_config.version_max_override < SSL_PROTOCOL_VERSION_TLS1_3)) {
    initialization_error_ = ERR_SSL_VERSION_OR_CIPHER_MISMATCH;
  } else if (!ssl_config.ech_config_list.empty() ||
             ssl_config.trust_anchor_ids.has_value() ||
             ssl_config.server_padding_to_request.has_value()) {
    initialization_error_ = ERR_NOT_IMPLEMENTED;
  }
  SetDnsAliases(stream_socket->GetDnsAliases());

  auto transport = std::make_unique<TransportAdapter>(std::move(stream_socket));
  transport_adapter_ = transport.get();
  auto authenticator = std::make_unique<Authenticator>(
      context, ssl_config, transport_adapter_->socket()->NetLog());
  authenticator_ = authenticator.get();
  std::unique_ptr<atlas::chromium::ServerAuthenticator> base_authenticator =
      std::move(authenticator);

  atlas::chromium::ClientSocketConfig config;
  config.hostname = host_and_port.host();
  config.validation_time_seconds = static_cast<uint64_t>(std::time(nullptr));
  core_ = std::make_unique<atlas::chromium::Tls13ClientSocket>(
      std::move(transport), std::move(base_authenticator), std::move(config));
}

AtlasClientSocket::~AtlasClientSocket() {
  Disconnect();
}

std::vector<uint8_t> AtlasClientSocket::GetECHRetryConfigs() {
  return {};
}

std::vector<std::vector<uint8_t>>
AtlasClientSocket::GetServerTrustAnchorIDs() {
  return {};
}

int AtlasClientSocket::ExportKeyingMaterial(
    std::string_view label,
    std::optional<base::span<const uint8_t>> context,
    base::span<uint8_t> out) {
  return ERR_NOT_IMPLEMENTED;
}

int AtlasClientSocket::Connect(CompletionOnceCallback callback) {
  if (initialization_error_ != OK) {
    LOG(ERROR) << "ATLAS socket initialization failed: "
               << initialization_error_;
    return initialization_error_;
  }
  if (disconnected_) {
    return ERR_SOCKET_NOT_CONNECTED;
  }
  int result = core_->Connect(
      [this](int completion_result) {
        OnConnectComplete(completion_result);
      });
  int mapped = MapCoreResult(result);
  if (mapped != OK && mapped != ERR_IO_PENDING) {
    LOG(ERROR) << "ATLAS synchronous connect failed: " << mapped;
  }
  if (mapped == ERR_IO_PENDING) {
    connect_callback_ = std::move(callback);
  }
  return mapped;
}

void AtlasClientSocket::Disconnect() {
  if (disconnected_) {
    return;
  }
  disconnected_ = true;
  connect_callback_.Reset();
  read_callback_.Reset();
  write_callback_.Reset();
  read_buffer_.reset();
  write_buffer_.reset();
  if (core_) {
    core_->Disconnect();
  }
}

int AtlasClientSocket::ConfirmHandshake(
    CompletionOnceCallback callback) {
  return IsConnected() ? OK : ERR_SOCKET_NOT_CONNECTED;
}

bool AtlasClientSocket::IsConnected() const {
  return !disconnected_ && core_->IsConnected() &&
         transport_adapter_->socket()->IsConnected();
}

bool AtlasClientSocket::IsConnectedAndIdle() const {
  return IsConnected() && core_->IsIdle() &&
         transport_adapter_->socket()->IsConnectedAndIdle();
}

int AtlasClientSocket::GetPeerAddress(IPEndPoint* address) const {
  return transport_adapter_->socket()->GetPeerAddress(address);
}

int AtlasClientSocket::GetLocalAddress(IPEndPoint* address) const {
  return transport_adapter_->socket()->GetLocalAddress(address);
}

const NetLogWithSource& AtlasClientSocket::NetLog() const {
  return transport_adapter_->socket()->NetLog();
}

bool AtlasClientSocket::WasEverUsed() const {
  return was_ever_used_;
}

NextProto AtlasClientSocket::GetNegotiatedProtocol() const {
  return NextProto::kProtoUnknown;
}

std::optional<std::string_view>
AtlasClientSocket::GetPeerApplicationSettings() const {
  return std::nullopt;
}

bool AtlasClientSocket::GetSSLInfo(SSLInfo* ssl_info) {
  if (!authenticator_->has_certificate()) {
    return false;
  }
  authenticator_->PopulateSSLInfo(ssl_info, core_->peer_signature_scheme());
  return true;
}

int64_t AtlasClientSocket::GetTotalReceivedBytes() const {
  return transport_adapter_->socket()->GetTotalReceivedBytes();
}

void AtlasClientSocket::ApplySocketTag(const SocketTag& tag) {
  transport_adapter_->socket()->ApplySocketTag(tag);
}

int AtlasClientSocket::Read(IOBuffer* buf,
                                    int buf_len,
                                    CompletionOnceCallback callback) {
  if (buf_len <= 0) {
    return ERR_INVALID_ARGUMENT;
  }
  if (!IsConnected()) {
    return ERR_SOCKET_NOT_CONNECTED;
  }
  if (read_buffer_) {
    return ERR_IO_PENDING;
  }
  read_buffer_ = buf;
  int result = core_->Read(
      buf->bytes(), buf_len,
      [this](int completion_result) {
        OnReadComplete(completion_result);
      });
  int mapped = MapCoreResult(result);
  if (mapped == ERR_IO_PENDING) {
    read_callback_ = std::move(callback);
  } else {
    read_buffer_.reset();
    if (mapped > 0) {
      was_ever_used_ = true;
    }
  }
  return mapped;
}

int AtlasClientSocket::Write(
    IOBuffer* buf,
    int buf_len,
    CompletionOnceCallback callback,
    const NetworkTrafficAnnotationTag& traffic_annotation) {
  if (buf_len <= 0) {
    return ERR_INVALID_ARGUMENT;
  }
  if (!IsConnected()) {
    return ERR_SOCKET_NOT_CONNECTED;
  }
  if (write_buffer_) {
    return ERR_IO_PENDING;
  }
  write_buffer_ = buf;
  int result = core_->Write(
      buf->bytes(), buf_len,
      [this](int completion_result) {
        OnWriteComplete(completion_result);
      });
  int mapped = MapCoreResult(result);
  if (mapped == ERR_IO_PENDING) {
    write_callback_ = std::move(callback);
  } else {
    write_buffer_.reset();
    if (mapped > 0) {
      was_ever_used_ = true;
    }
  }
  return mapped;
}

int AtlasClientSocket::SetReceiveBufferSize(int32_t size) {
  return transport_adapter_->socket()->SetReceiveBufferSize(size);
}

int AtlasClientSocket::SetSendBufferSize(int32_t size) {
  return transport_adapter_->socket()->SetSendBufferSize(size);
}

int AtlasClientSocket::MapCoreResult(int result) const {
  if (result >= 0) {
    return result;
  }
  switch (result) {
    case atlas::chromium::kIoPending:
      return ERR_IO_PENDING;
    case atlas::chromium::kErrorInvalidArgument:
      return ERR_INVALID_ARGUMENT;
    case atlas::chromium::kErrorInvalidState:
    case atlas::chromium::kErrorOperationPending:
      return ERR_UNEXPECTED;
    case atlas::chromium::kErrorCertificate:
      return authenticator_->last_error() == OK
                 ? ERR_CERT_INVALID
                 : authenticator_->last_error();
    case atlas::chromium::kErrorConnectionClosed:
      return transport_adapter_->last_error() == OK
                 ? ERR_CONNECTION_CLOSED
                 : transport_adapter_->last_error();
    case atlas::chromium::kErrorProtocol:
    case atlas::chromium::kErrorFailed:
    default:
      return ERR_SSL_PROTOCOL_ERROR;
  }
}

void AtlasClientSocket::OnConnectComplete(int result) {
  if (!connect_callback_) {
    return;
  }
  int mapped = MapCoreResult(result);
  if (mapped != OK) {
    LOG(ERROR) << "ATLAS asynchronous connect failed: " << mapped
               << " (core result " << result << ")";
  }
  std::move(connect_callback_).Run(mapped);
}

void AtlasClientSocket::OnReadComplete(int result) {
  if (!read_callback_) {
    return;
  }
  int mapped = MapCoreResult(result);
  read_buffer_.reset();
  if (mapped > 0) {
    was_ever_used_ = true;
  }
  std::move(read_callback_).Run(mapped);
}

void AtlasClientSocket::OnWriteComplete(int result) {
  if (!write_callback_) {
    return;
  }
  int mapped = MapCoreResult(result);
  write_buffer_.reset();
  if (mapped > 0) {
    was_ever_used_ = true;
  }
  std::move(write_callback_).Run(mapped);
}

}  // namespace net

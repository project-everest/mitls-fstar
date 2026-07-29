#ifndef TLS13_CHROMIUM_CLIENT_SOCKET_H
#define TLS13_CHROMIUM_CLIENT_SOCKET_H

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <vector>

namespace mitls::chromium {

constexpr int kSuccess = 0;
constexpr int kIoPending = -1;
constexpr int kErrorFailed = -2;
constexpr int kErrorInvalidArgument = -3;
constexpr int kErrorInvalidState = -4;
constexpr int kErrorConnectionClosed = -5;
constexpr int kErrorCertificate = -6;
constexpr int kErrorProtocol = -7;
constexpr int kErrorOperationPending = -8;

using CompletionCallback = std::function<void(int)>;

class StreamSocket {
 public:
  virtual ~StreamSocket() = default;

  // Positive results are byte counts. A pending operation returns kIoPending
  // and invokes its callback exactly once; synchronous results do not.
  virtual int Read(
      uint8_t* output,
      size_t output_capacity,
      CompletionCallback callback) = 0;
  virtual int Write(
      const uint8_t* input,
      size_t input_len,
      CompletionCallback callback) = 0;
  virtual void Disconnect() = 0;
};

struct CertificateChain {
  std::vector<std::vector<uint8_t>> der_certificates;
};

class ServerAuthenticator {
 public:
  virtual ~ServerAuthenticator() = default;

  // On success, authenticated_public_key_der() returns the leaf SubjectPublicKeyInfo.
  virtual int VerifyCertificateChain(
      const std::string& hostname,
      const CertificateChain& chain,
      uint64_t validation_time_seconds,
      CompletionCallback callback) = 0;
  virtual const std::vector<uint8_t>& authenticated_public_key_der() const = 0;
  virtual bool VerifyCertificateSignature(
      uint16_t signature_scheme,
      const uint8_t* input,
      size_t input_len,
      const uint8_t* signature,
      size_t signature_len) const = 0;
  virtual void Cancel() = 0;
};

struct ClientSocketConfig {
  std::string hostname;
  std::vector<uint8_t> trust_context;
  uint64_t validation_time_seconds = 0;
};

// Portable core for a Chromium SSLClientSocket implementation. It follows the
// Chromium synchronous-or-ERR_IO_PENDING convention and supports one pending
// read and one pending write concurrently on a single sequence.
class Tls13ClientSocket {
 public:
  Tls13ClientSocket(
      std::unique_ptr<StreamSocket> transport,
      std::unique_ptr<ServerAuthenticator> authenticator,
      ClientSocketConfig config);
  ~Tls13ClientSocket();

  Tls13ClientSocket(const Tls13ClientSocket&) = delete;
  Tls13ClientSocket& operator=(const Tls13ClientSocket&) = delete;

  int Connect(CompletionCallback callback);
  int Read(
      uint8_t* output,
      size_t output_capacity,
      CompletionCallback callback);
  int Write(
      const uint8_t* input,
      size_t input_len,
      CompletionCallback callback);
  int Shutdown(CompletionCallback callback);

  void Disconnect();
  bool IsConnected() const;
  const CertificateChain& peer_certificate_chain() const;
  uint16_t peer_signature_scheme() const;

 private:
  class Impl;
  std::unique_ptr<Impl> impl_;
};

}  // namespace mitls::chromium

#endif

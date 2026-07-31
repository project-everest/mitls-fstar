#include "chromium/tls13_client_socket.h"
#include "tls13_client_engine.h"
#include "tls13_openssl_stubs.h"

#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace {

using atlas::chromium::CertificateChain;
using atlas::chromium::ClientSocketConfig;
using atlas::chromium::CompletionCallback;
using atlas::chromium::ServerAuthenticator;
using atlas::chromium::StreamSocket;
using atlas::chromium::Tls13ClientSocket;
using atlas::chromium::kErrorCertificate;
using atlas::chromium::kErrorConnectionClosed;
using atlas::chromium::kErrorInvalidArgument;
using atlas::chromium::kErrorOperationPending;
using atlas::chromium::kIoPending;
using atlas::chromium::kSuccess;

constexpr size_t kTransportFragment = 7u;

class EventLoopStreamSocket final : public StreamSocket {
 public:
  explicit EventLoopStreamSocket(int socket_fd) : socket_fd_(socket_fd) {}

  ~EventLoopStreamSocket() override {
    Disconnect();
  }

  int Read(
      uint8_t* output,
      size_t output_capacity,
      CompletionCallback callback) override {
    if (socket_fd_ < 0) {
      return kErrorConnectionClosed;
    }
    if (read_callback_) {
      return kErrorOperationPending;
    }
    if (output == nullptr || output_capacity == 0u || !callback) {
      return kErrorInvalidArgument;
    }
    read_output_ = output;
    read_capacity_ = output_capacity;
    read_callback_ = std::move(callback);
    return kIoPending;
  }

  int Write(
      const uint8_t* input,
      size_t input_len,
      CompletionCallback callback) override {
    if (socket_fd_ < 0) {
      return kErrorConnectionClosed;
    }
    if (write_callback_) {
      return kErrorOperationPending;
    }
    if (input == nullptr || input_len == 0u || !callback) {
      return kErrorInvalidArgument;
    }
    size_t write_len = std::min(input_len, kTransportFragment);
    ssize_t written = send(socket_fd_, input, write_len, MSG_NOSIGNAL);
    if (written > 0) {
      return static_cast<int>(written);
    }
    if (written < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      write_input_ = input;
      write_len_ = input_len;
      write_callback_ = std::move(callback);
      return kIoPending;
    }
    return kErrorConnectionClosed;
  }

  void Disconnect() override {
    read_callback_ = {};
    write_callback_ = {};
    if (socket_fd_ >= 0) {
      close(socket_fd_);
      socket_fd_ = -1;
    }
  }

  bool HasPendingOperation() const {
    return static_cast<bool>(read_callback_) ||
        static_cast<bool>(write_callback_);
  }

  bool RunOnce() {
    if (socket_fd_ < 0 || !HasPendingOperation()) {
      return false;
    }
    short events = 0;
    if (read_callback_) {
      events |= POLLIN;
    }
    if (write_callback_) {
      events |= POLLOUT;
    }
    struct pollfd descriptor {};
    descriptor.fd = socket_fd_;
    descriptor.events = events;
    int poll_result;
    do {
      poll_result = poll(&descriptor, 1, 10000);
    } while (poll_result < 0 && errno == EINTR);
    if (poll_result <= 0) {
      perror(poll_result == 0 ? "poll timeout" : "poll");
      return false;
    }

    if (write_callback_ &&
        (descriptor.revents & (POLLOUT | POLLERR | POLLHUP)) != 0) {
      size_t write_len = std::min(write_len_, kTransportFragment);
      ssize_t written =
          send(socket_fd_, write_input_, write_len, MSG_NOSIGNAL);
      if (written < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        return true;
      }
      CompletionCallback callback = std::move(write_callback_);
      write_input_ = nullptr;
      write_len_ = 0u;
      callback(written > 0 ? static_cast<int>(written)
                           : kErrorConnectionClosed);
      return true;
    }

    if (read_callback_ &&
        (descriptor.revents & (POLLIN | POLLERR | POLLHUP)) != 0) {
      size_t read_len = std::min(read_capacity_, kTransportFragment);
      ssize_t received = recv(socket_fd_, read_output_, read_len, 0);
      if (received < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        return true;
      }
      CompletionCallback callback = std::move(read_callback_);
      read_output_ = nullptr;
      read_capacity_ = 0u;
      callback(received > 0 ? static_cast<int>(received)
                            : kErrorConnectionClosed);
      return true;
    }
    return false;
  }

 private:
  int socket_fd_;
  uint8_t* read_output_ = nullptr;
  size_t read_capacity_ = 0u;
  CompletionCallback read_callback_;
  const uint8_t* write_input_ = nullptr;
  size_t write_len_ = 0u;
  CompletionCallback write_callback_;
};

class OpenSslAuthenticator final : public ServerAuthenticator {
 public:
  explicit OpenSslAuthenticator(tls13_trust_store* trust_store)
      : trust_store_(trust_store) {}

  ~OpenSslAuthenticator() override {
    Cancel();
    tls13_openssl_peer_identity_free(peer_);
    tls13_openssl_trust_store_free(trust_store_);
  }

  int VerifyCertificateChain(
      const std::string& hostname,
      const CertificateChain& chain,
      uint64_t validation_time_seconds,
      CompletionCallback callback) override {
    if (pending_callback_) {
      return kErrorOperationPending;
    }
    tls13_openssl_peer_identity_free(peer_);
    peer_ = nullptr;
    public_key_.clear();
    bool valid =
        !chain.der_certificates.empty() &&
        tls13_openssl_validate_leaf_der_with_store(
            hostname.c_str(),
            trust_store_,
            static_cast<size_t>(validation_time_seconds),
            chain.der_certificates.front().data(),
            chain.der_certificates.front().size(),
            &peer_);
    if (valid) {
      public_key_.resize(TLS13_CLIENT_ENGINE_PUBLIC_KEY_CAPACITY);
      size_t public_key_len = 0u;
      valid = tls13_openssl_peer_copy_public_key_der(
          peer_,
          public_key_.data(),
          public_key_.size(),
          &public_key_len);
      public_key_.resize(valid ? public_key_len : 0u);
    }
    pending_result_ = valid ? kSuccess : kErrorCertificate;
    pending_callback_ = std::move(callback);
    return kIoPending;
  }

  const std::vector<uint8_t>& authenticated_public_key_der()
      const override {
    return public_key_;
  }

  bool VerifyCertificateSignature(
      uint16_t signature_scheme,
      const uint8_t* input,
      size_t input_len,
      const uint8_t* signature,
      size_t signature_len) const override {
    return tls13_openssl_peer_verify_signature(
        peer_,
        signature_scheme,
        input,
        input_len,
        signature,
        signature_len);
  }

  void Cancel() override {
    pending_callback_ = {};
  }

  bool HasPendingOperation() const {
    return static_cast<bool>(pending_callback_);
  }

  void RunPending() {
    CompletionCallback callback = std::move(pending_callback_);
    if (callback) {
      callback(pending_result_);
    }
  }

 private:
  tls13_trust_store* trust_store_;
  tls13_peer_identity* peer_ = nullptr;
  std::vector<uint8_t> public_key_;
  int pending_result_ = kErrorCertificate;
  CompletionCallback pending_callback_;
};

int ReadFile(const char* path, std::vector<uint8_t>& output) {
  FILE* file = fopen(path, "rb");
  if (file == nullptr) {
    perror(path);
    return 1;
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    fclose(file);
    return 1;
  }
  long length = ftell(file);
  if (length < 0) {
    fclose(file);
    return 1;
  }
  rewind(file);
  output.resize(static_cast<size_t>(length));
  bool ok =
      fread(output.data(), 1u, output.size(), file) == output.size();
  fclose(file);
  return ok ? 0 : 1;
}

int ConnectTcp(const char* host, uint16_t port) {
  int socket_fd = socket(AF_INET, SOCK_STREAM, 0);
  if (socket_fd < 0) {
    return -1;
  }
  struct sockaddr_in address {};
  address.sin_family = AF_INET;
  address.sin_port = htons(port);
  if (inet_pton(AF_INET, host, &address.sin_addr) != 1 ||
      connect(
          socket_fd,
          reinterpret_cast<struct sockaddr*>(&address),
          sizeof address) != 0) {
    close(socket_fd);
    return -1;
  }
  int flags = fcntl(socket_fd, F_GETFL, 0);
  if (flags < 0 || fcntl(socket_fd, F_SETFL, flags | O_NONBLOCK) != 0) {
    close(socket_fd);
    return -1;
  }
  return socket_fd;
}

int Await(
    int initial_result,
    bool& completed,
    int& completion_result,
    EventLoopStreamSocket& transport,
    OpenSslAuthenticator& authenticator) {
  if (initial_result != kIoPending) {
    return initial_result;
  }
  while (!completed) {
    if (authenticator.HasPendingOperation()) {
      authenticator.RunPending();
    } else if (!transport.RunOnce()) {
      return kErrorConnectionClosed;
    }
  }
  return completion_result;
}

int RunDemo(
    const char* host,
    uint16_t port,
    const std::vector<uint8_t>& trust_anchor) {
  int socket_fd = ConnectTcp(host, port);
  tls13_trust_store* trust_store = tls13_openssl_trust_store_new(
      trust_anchor.data(),
      trust_anchor.size());
  if (socket_fd < 0 || trust_store == nullptr) {
    if (socket_fd >= 0) {
      close(socket_fd);
    }
    tls13_openssl_trust_store_free(trust_store);
    return 1;
  }

  auto transport = std::make_unique<EventLoopStreamSocket>(socket_fd);
  auto authenticator =
      std::make_unique<OpenSslAuthenticator>(trust_store);
  EventLoopStreamSocket* transport_ptr = transport.get();
  OpenSslAuthenticator* authenticator_ptr = authenticator.get();
  ClientSocketConfig config;
  config.hostname = "localhost";
  config.trust_context = trust_anchor;
  Tls13ClientSocket client(
      std::move(transport),
      std::move(authenticator),
      std::move(config));

  bool completed = false;
  int completion_result = kErrorConnectionClosed;
  int result = client.Connect([&](int value) {
    completion_result = value;
    completed = true;
  });
  result = Await(
      result,
      completed,
      completion_result,
      *transport_ptr,
      *authenticator_ptr);
  if (result != kSuccess || !client.IsConnected() ||
      client.peer_certificate_chain().der_certificates.empty()) {
    fprintf(stderr, "Chromium-style TLS Connect failed: %d\n", result);
    return 1;
  }

  static const char request[] =
      "GET / HTTP/1.1\r\n"
      "Host: localhost\r\n"
      "Connection: close\r\n"
      "\r\n";
  uint8_t first_read_buffer[17];
  bool read_completed = false;
  int read_completion_result = kErrorConnectionClosed;
  int first_read_result = client.Read(
      first_read_buffer,
      sizeof first_read_buffer,
      [&](int value) {
        read_completion_result = value;
        read_completed = true;
      });
  if (first_read_result != kIoPending) {
    fprintf(stderr, "initial concurrent Read did not pend: %d\n",
            first_read_result);
    return 1;
  }

  completed = false;
  result = client.Write(
      reinterpret_cast<const uint8_t*>(request),
      sizeof request - 1u,
      [&](int value) {
        completion_result = value;
        completed = true;
      });
  result = Await(
      result,
      completed,
      completion_result,
      *transport_ptr,
      *authenticator_ptr);
  if (result != static_cast<int>(sizeof request - 1u)) {
    fprintf(stderr, "Chromium-style TLS Write failed: %d\n", result);
    return 1;
  }

  std::string response;
  result = Await(
      first_read_result,
      read_completed,
      read_completion_result,
      *transport_ptr,
      *authenticator_ptr);
  if (result <= 0) {
    fprintf(stderr, "initial concurrent TLS Read failed: %d\n", result);
    return 1;
  }
  response.append(
      reinterpret_cast<const char*>(first_read_buffer),
      static_cast<size_t>(result));
  for (;;) {
    uint8_t read_buffer[17];
    completed = false;
    result = client.Read(read_buffer, sizeof read_buffer, [&](int value) {
      completion_result = value;
      completed = true;
    });
    result = Await(
        result,
        completed,
        completion_result,
        *transport_ptr,
        *authenticator_ptr);
    if (result < 0) {
      fprintf(stderr, "Chromium-style TLS Read failed: %d\n", result);
      return 1;
    }
    if (result == 0) {
      break;
    }
    response.append(
        reinterpret_cast<const char*>(read_buffer),
        static_cast<size_t>(result));
  }

  if (response.find("HTTP/1.1 200 OK\r\n") != 0u ||
      response.find("\r\n\r\nverified chromium demo\n") ==
          std::string::npos) {
    fprintf(stderr, "unexpected HTTP response:\n%s\n", response.c_str());
    return 1;
  }
  printf(
      "Chromium-style async HTTPS demo passed (%zu certificate, scheme 0x%04x)\n",
      client.peer_certificate_chain().der_certificates.size(),
      client.peer_signature_scheme());
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s HOST PORT CA_PEM\n", argv[0]);
    return 1;
  }
  char* end = nullptr;
  long port = strtol(argv[2], &end, 10);
  if (end == argv[2] || *end != '\0' || port <= 0 || port > 65535) {
    return 1;
  }
  std::vector<uint8_t> trust_anchor;
  if (ReadFile(argv[3], trust_anchor) != 0) {
    return 1;
  }
  return RunDemo(argv[1], static_cast<uint16_t>(port), trust_anchor);
}

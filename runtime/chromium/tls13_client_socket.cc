#include "tls13_client_socket.h"

#include "tls13_client_engine.h"

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstring>
#include <limits>
#include <utility>

namespace atlas::chromium {
namespace {

constexpr size_t kNetworkInputCapacity = 65535u;
int MapEngineError(int error) {
  switch (error) {
    case TLS13_CLIENT_ENGINE_SUCCESS:
      return kSuccess;
    case TLS13_CLIENT_ENGINE_ERROR_INVALID_ARGUMENT:
      return kErrorInvalidArgument;
    case TLS13_CLIENT_ENGINE_ERROR_INVALID_STATE:
      return kErrorInvalidState;
    case TLS13_CLIENT_ENGINE_ERROR_ALLOCATION:
    case TLS13_CLIENT_ENGINE_ERROR_INTERNAL:
    default:
      return kErrorFailed;
  }
}

}  // namespace

class Tls13ClientSocket::Impl {
 public:
  Impl(
      std::unique_ptr<StreamSocket> transport,
      std::unique_ptr<ServerAuthenticator> authenticator,
      ClientSocketConfig config)
      : transport_(std::move(transport)),
        authenticator_(std::move(authenticator)),
        config_(std::move(config)) {
    network_input_.reserve(kNetworkInputCapacity);
  }

  ~Impl() {
    Disconnect();
  }

  int Connect(CompletionCallback callback) {
    if (state_ != State::kNew) {
      return state_ == State::kConnected ? kSuccess : kErrorInvalidState;
    }
    if (transport_ == nullptr || authenticator_ == nullptr || !callback ||
        config_.hostname.empty() ||
        config_.hostname.size() > TLS13_CLIENT_ENGINE_MAX_SERVER_NAME_LEN ||
        config_.trust_context.size() >
            TLS13_CLIENT_ENGINE_MAX_TRUST_CONTEXT_LEN) {
      return kErrorInvalidArgument;
    }

    int error = tls13_client_engine_new(
        &engine_,
        reinterpret_cast<const uint8_t*>(config_.hostname.data()),
        config_.hostname.size(),
        config_.trust_context.data(),
        config_.trust_context.size(),
        static_cast<size_t>(config_.validation_time_seconds));
    if (error != TLS13_CLIENT_ENGINE_SUCCESS) {
      return MapEngineError(error);
    }

    state_ = State::kHandshaking;
    StartRequest(connect_request_, std::move(callback));
    if (!PollEngine()) {
      Fail(kErrorProtocol);
    } else {
      Pump();
    }
    return FinishStart(connect_request_);
  }

  int Read(
      uint8_t* output,
      size_t output_capacity,
      CompletionCallback callback) {
    if (output == nullptr || output_capacity == 0u || !callback) {
      return kErrorInvalidArgument;
    }
    if (state_ == State::kClosing || state_ == State::kClosed) {
      if (!HasPlaintext()) {
        return 0;
      }
      size_t available = plaintext_.size() - plaintext_offset_;
      size_t copied = std::min(available, output_capacity);
      std::memcpy(output, plaintext_.data() + plaintext_offset_, copied);
      plaintext_offset_ += copied;
      CompactPlaintext();
      return static_cast<int>(copied);
    }
    if (state_ != State::kConnected) {
      return kErrorInvalidState;
    }
    if (read_request_.active) {
      return kErrorOperationPending;
    }

    read_output_ = output;
    read_output_capacity_ = output_capacity;
    StartRequest(read_request_, std::move(callback));
    Pump();
    return FinishStart(read_request_);
  }

  int Write(
      const uint8_t* input,
      size_t input_len,
      CompletionCallback callback) {
    if (state_ != State::kConnected) {
      return kErrorInvalidState;
    }
    if ((input == nullptr && input_len != 0u) || !callback) {
      return kErrorInvalidArgument;
    }
    if (write_request_.active) {
      return kErrorOperationPending;
    }
    if (input_len == 0u) {
      return 0;
    }

    size_t accepted =
        std::min(input_len, TLS13_CLIENT_ENGINE_MAX_APPLICATION_DATA_LEN);
    pending_write_.assign(input, input + accepted);
    write_accepted_ = accepted;
    write_submitted_ = false;
    StartRequest(write_request_, std::move(callback));
    Pump();
    return FinishStart(write_request_);
  }

  int Shutdown(CompletionCallback callback) {
    if (state_ == State::kClosed) {
      return kSuccess;
    }
    if (state_ != State::kConnected || !callback) {
      return kErrorInvalidState;
    }
    if (shutdown_request_.active || write_request_.active ||
        read_request_.active) {
      return kErrorOperationPending;
    }

    StartRequest(shutdown_request_, std::move(callback));
    Pump();
    return FinishStart(shutdown_request_);
  }

  void Disconnect() {
    if (state_ == State::kClosed && engine_ == nullptr) {
      return;
    }
    state_ = State::kClosed;
    if (authenticator_ != nullptr) {
      authenticator_->Cancel();
    }
    if (transport_ != nullptr) {
      transport_->Disconnect();
    }
    if (engine_ != nullptr) {
      tls13_client_engine_free(engine_);
      engine_ = nullptr;
    }
    ResetRequest(connect_request_);
    ResetRequest(read_request_);
    ResetRequest(write_request_);
    ResetRequest(shutdown_request_);
    ready_callbacks_.clear();
    transport_read_pending_ = false;
    transport_write_pending_ = false;
    auth_pending_ = false;
  }

  bool IsConnected() const {
    return state_ == State::kConnected;
  }

  bool IsIdle() const {
    return state_ == State::kConnected && !HasPlaintext() &&
        network_input_.empty() && !HasNetworkOutput() &&
        !transport_read_pending_ && !transport_write_pending_ &&
        !auth_pending_ && !connect_request_.active &&
        !read_request_.active && !write_request_.active &&
        !shutdown_request_.active;
  }

  const CertificateChain& peer_certificate_chain() const {
    return peer_certificate_chain_;
  }

  uint16_t peer_signature_scheme() const {
    return peer_signature_scheme_;
  }

 private:
  enum class State {
    kNew,
    kHandshaking,
    kConnected,
    kClosing,
    kClosed,
    kFailed,
  };

  struct PendingRequest {
    bool active = false;
    bool asynchronous = false;
    bool completed = false;
    int result = kErrorFailed;
    CompletionCallback callback;
  };

  void StartRequest(
      PendingRequest& request,
      CompletionCallback callback) {
    request.active = true;
    request.asynchronous = false;
    request.completed = false;
    request.result = kErrorFailed;
    request.callback = std::move(callback);
  }

  void ResetRequest(PendingRequest& request) {
    request = PendingRequest{};
  }

  void CompleteRequest(PendingRequest& request, int result) {
    if (!request.active || request.completed) {
      return;
    }
    if (!request.asynchronous) {
      request.completed = true;
      request.result = result;
      return;
    }
    CompletionCallback callback = std::move(request.callback);
    ResetRequest(request);
    ready_callbacks_.emplace_back(std::move(callback), result);
  }

  int FinishStart(PendingRequest& request) {
    int result = kIoPending;
    if (request.completed) {
      result = request.result;
      ResetRequest(request);
    } else if (request.active) {
      request.asynchronous = true;
    }
    DispatchCallbacks();
    return result;
  }

  void DispatchCallbacks() {
    auto callbacks = std::move(ready_callbacks_);
    ready_callbacks_.clear();
    for (auto& entry : callbacks) {
      entry.first(entry.second);
    }
  }

  bool CaptureEngineResult(
      const char* operation,
      int error,
      const tls13_client_engine_result& result) {
    if (error != TLS13_CLIENT_ENGINE_SUCCESS) {
      fprintf(
          stderr,
          "ATLAS engine call failed: operation=%s error=%d\n",
          operation,
          error);
      return false;
    }
    if (result.network_out_len > network_out_buffer_.size() ||
        result.application_out_len > application_out_buffer_.size()) {
      fprintf(
          stderr,
          "ATLAS engine returned invalid lengths: "
          "operation=%s network=%zu application=%zu\n",
          operation,
          result.network_out_len,
          result.application_out_len);
      return false;
    }
    if (result.action == TLS13_CLIENT_ENGINE_FAILED) {
      fprintf(
          stderr,
          "ATLAS engine rejected input: operation=%s "
          "previous_action=%d status=%d consumed=%zu buffered=%zu\n",
          operation,
          have_engine_result_ ? static_cast<int>(engine_result_.action) : -1,
          static_cast<int>(result.status),
          result.consumed_len,
          network_input_.size());
    }
    if (result.network_out_len != 0u) {
      if (network_output_offset_ != network_output_.size()) {
        return false;
      }
      network_output_.assign(
          network_out_buffer_.begin(),
          network_out_buffer_.begin() + result.network_out_len);
      network_output_offset_ = 0u;
    }
    if (result.application_out_len != 0u) {
      plaintext_.insert(
          plaintext_.end(),
          application_out_buffer_.begin(),
          application_out_buffer_.begin() + result.application_out_len);
    }
    engine_result_ = result;
    have_engine_result_ = true;
    need_more_network_ =
        result.action == TLS13_CLIENT_ENGINE_NEED_NETWORK_INPUT &&
        result.status == TLS13_CLIENT_ENGINE_STATUS_NEED_MORE_INPUT;
    return true;
  }

  bool PollEngine() {
    tls13_client_engine_result result;
    int error = tls13_client_engine_poll(
        engine_,
        network_out_buffer_.data(),
        network_out_buffer_.size(),
        application_out_buffer_.data(),
        application_out_buffer_.size(),
        &result);
    return CaptureEngineResult("poll", error, result);
  }

  bool FeedNetwork() {
    tls13_client_engine_result result;
    int error = tls13_client_engine_feed_network(
        engine_,
        network_input_.data(),
        network_input_.size(),
        network_out_buffer_.data(),
        network_out_buffer_.size(),
        application_out_buffer_.data(),
        application_out_buffer_.size(),
        &result);
    if (error != TLS13_CLIENT_ENGINE_SUCCESS ||
        result.consumed_len > network_input_.size()) {
      return false;
    }
    network_input_.erase(
        network_input_.begin(),
        network_input_.begin() + result.consumed_len);
    return CaptureEngineResult("feed_network", error, result);
  }

  bool CompleteCertificateVerification() {
    const std::vector<uint8_t>& public_key =
        authenticator_->authenticated_public_key_der();
    if (public_key.empty() ||
        public_key.size() > TLS13_CLIENT_ENGINE_PUBLIC_KEY_CAPACITY) {
      return false;
    }
    tls13_client_engine_result result;
    int error = tls13_client_engine_complete_certificate_verification(
        engine_,
        public_key.data(),
        public_key.size(),
        network_out_buffer_.data(),
        network_out_buffer_.size(),
        application_out_buffer_.data(),
        application_out_buffer_.size(),
        &result);
    return CaptureEngineResult(
        "complete_certificate_verification", error, result);
  }

  bool CompleteCertificateSignatureVerification() {
    tls13_client_engine_result result;
    int error =
        tls13_client_engine_complete_certificate_signature_verification(
            engine_,
            network_out_buffer_.data(),
            network_out_buffer_.size(),
            application_out_buffer_.data(),
            application_out_buffer_.size(),
            &result);
    return CaptureEngineResult(
        "complete_certificate_signature_verification", error, result);
  }

  bool SubmitApplicationWrite() {
    tls13_client_engine_result result;
    int error = tls13_client_engine_send_application_data(
        engine_,
        pending_write_.data(),
        pending_write_.size(),
        network_out_buffer_.data(),
        network_out_buffer_.size(),
        application_out_buffer_.data(),
        application_out_buffer_.size(),
        &result);
    if (!CaptureEngineResult("send_application_data", error, result)) {
      return false;
    }
    write_submitted_ = true;
    return true;
  }

  bool SubmitCloseNotify() {
    tls13_client_engine_result result;
    int error = tls13_client_engine_send_close_notify(
        engine_,
        network_out_buffer_.data(),
        network_out_buffer_.size(),
        application_out_buffer_.data(),
        application_out_buffer_.size(),
        &result);
    if (!CaptureEngineResult("send_close_notify", error, result)) {
      return false;
    }
    state_ = State::kClosing;
    return true;
  }

  bool CopyCertificateChain(CertificateChain& chain) {
    std::array<uint8_t, TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_CAPACITY>
        chain_bytes{};
    std::array<size_t, TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES>
        offsets{};
    std::array<size_t, TLS13_CLIENT_ENGINE_CERTIFICATE_CHAIN_ENTRIES>
        lengths{};
    tls13_client_engine_certificate_chain snapshot;
    int error = tls13_client_engine_copy_certificate_chain(
        engine_,
        chain_bytes.data(),
        chain_bytes.size(),
        offsets.data(),
        offsets.size(),
        lengths.data(),
        lengths.size(),
        &snapshot);
    if (error != TLS13_CLIENT_ENGINE_SUCCESS ||
        snapshot.certificate_count == 0u ||
        snapshot.certificate_count > offsets.size() ||
        snapshot.bytes_len > chain_bytes.size()) {
      return false;
    }

    chain.der_certificates.clear();
    chain.der_certificates.reserve(snapshot.certificate_count);
    for (size_t i = 0u; i < snapshot.certificate_count; ++i) {
      if (lengths[i] == 0u || offsets[i] > snapshot.bytes_len ||
          lengths[i] > snapshot.bytes_len - offsets[i]) {
        return false;
      }
      chain.der_certificates.emplace_back(
          chain_bytes.begin() + offsets[i],
          chain_bytes.begin() + offsets[i] + lengths[i]);
    }
    return true;
  }

  bool VerifyCertificateSignature() {
    std::array<
        uint8_t,
        TLS13_CLIENT_ENGINE_CERTIFICATE_VERIFY_INPUT_CAPACITY>
        input{};
    std::array<uint8_t, TLS13_CLIENT_ENGINE_SIGNATURE_CAPACITY> signature{};
    tls13_client_engine_certificate_verify_request request;
    int error = tls13_client_engine_copy_certificate_verify_request(
        engine_,
        input.data(),
        input.size(),
        signature.data(),
        signature.size(),
        &request);
    if (error != TLS13_CLIENT_ENGINE_SUCCESS ||
        request.input_len > input.size() ||
        request.signature_len > signature.size()) {
      return false;
    }
    bool verified = authenticator_->VerifyCertificateSignature(
        request.signature_scheme,
        input.data(),
        request.input_len,
        signature.data(),
        request.signature_len);
    if (verified) {
      peer_signature_scheme_ = request.signature_scheme;
    }
    return verified;
  }

  bool HasNetworkOutput() const {
    return network_output_offset_ < network_output_.size();
  }

  bool HasPlaintext() const {
    return plaintext_offset_ < plaintext_.size();
  }

  void CompactPlaintext() {
    if (plaintext_offset_ == plaintext_.size()) {
      plaintext_.clear();
      plaintext_offset_ = 0u;
    } else if (plaintext_offset_ > 32768u) {
      plaintext_.erase(
          plaintext_.begin(),
          plaintext_.begin() + plaintext_offset_);
      plaintext_offset_ = 0u;
    }
  }

  void CompleteReadFromPlaintext() {
    size_t available = plaintext_.size() - plaintext_offset_;
    size_t copied = std::min(available, read_output_capacity_);
    std::memcpy(read_output_, plaintext_.data() + plaintext_offset_, copied);
    plaintext_offset_ += copied;
    read_output_ = nullptr;
    read_output_capacity_ = 0u;
    CompactPlaintext();
    CompleteRequest(read_request_, static_cast<int>(copied));
  }

  bool StartTransportRead() {
    if (transport_read_pending_) {
      return true;
    }
    if (network_input_.size() >= kNetworkInputCapacity) {
      return false;
    }
    size_t capacity =
        std::min(
            transport_read_buffer_.size(),
            kNetworkInputCapacity - network_input_.size());
    int result = transport_->Read(
        transport_read_buffer_.data(),
        capacity,
        [this](int completion_result) {
          OnTransportReadComplete(completion_result);
        });
    if (result == kIoPending) {
      transport_read_pending_ = true;
      return true;
    }
    return HandleTransportReadResult(result);
  }

  bool HandleTransportReadResult(int result) {
    if (result <= 0 ||
        static_cast<size_t>(result) > transport_read_buffer_.size() ||
        static_cast<size_t>(result) >
            kNetworkInputCapacity - network_input_.size()) {
      return false;
    }
    network_input_.insert(
        network_input_.end(),
        transport_read_buffer_.begin(),
        transport_read_buffer_.begin() + result);
    need_more_network_ = false;
    return true;
  }

  bool FlushNetworkOutput() {
    if (!HasNetworkOutput() || transport_write_pending_) {
      return true;
    }
    size_t remaining = network_output_.size() - network_output_offset_;
    int result = transport_->Write(
        network_output_.data() + network_output_offset_,
        remaining,
        [this](int completion_result) {
          OnTransportWriteComplete(completion_result);
        });
    if (result == kIoPending) {
      transport_write_pending_ = true;
      return true;
    }
    return HandleTransportWriteResult(result);
  }

  bool HandleTransportWriteResult(int result) {
    size_t remaining = network_output_.size() - network_output_offset_;
    if (result <= 0 || static_cast<size_t>(result) > remaining) {
      return false;
    }
    network_output_offset_ += static_cast<size_t>(result);
    if (!HasNetworkOutput()) {
      network_output_.clear();
      network_output_offset_ = 0u;
    }
    return true;
  }

  bool StartCertificateVerification() {
    if (!CopyCertificateChain(peer_certificate_chain_)) {
      return false;
    }
    int result = authenticator_->VerifyCertificateChain(
        config_.hostname,
        peer_certificate_chain_,
        config_.validation_time_seconds,
        [this](int completion_result) {
          OnCertificateVerificationComplete(completion_result);
        });
    if (result == kIoPending) {
      auth_pending_ = true;
      return true;
    }
    if (result != kSuccess) {
      Fail(kErrorCertificate);
      return false;
    }
    return CompleteCertificateVerification();
  }

  void Pump() {
    if (pumping_ || state_ == State::kClosed || state_ == State::kFailed) {
      return;
    }
    pumping_ = true;
    bool stop = false;
    while (!stop) {
      bool completed_request = false;
      if (HasPlaintext() && read_request_.active) {
        CompleteReadFromPlaintext();
        completed_request = true;
      }

      if (HasNetworkOutput()) {
        if (!FlushNetworkOutput()) {
          Fail(kErrorConnectionClosed);
          break;
        }
        if (transport_write_pending_) {
          break;
        }
        if (HasNetworkOutput()) {
          continue;
        }
      }

      if (write_request_.active && write_submitted_) {
        pending_write_.clear();
        write_submitted_ = false;
        CompleteRequest(
            write_request_,
            static_cast<int>(write_accepted_));
        write_accepted_ = 0u;
        completed_request = true;
      }

      if (completed_request) {
        break;
      }

      if (!have_engine_result_ || auth_pending_) {
        break;
      }

      switch (engine_result_.action) {
        case TLS13_CLIENT_ENGINE_PROGRESS:
        case TLS13_CLIENT_ENGINE_NETWORK_OUTPUT:
        case TLS13_CLIENT_ENGINE_APPLICATION_DATA:
          if (!PollEngine()) {
            Fail(kErrorProtocol);
          }
          break;

        case TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_VERIFICATION:
          if (!StartCertificateVerification() && state_ != State::kFailed) {
            Fail(kErrorCertificate);
          }
          if (auth_pending_ || state_ == State::kFailed) {
            stop = true;
          }
          break;

        case TLS13_CLIENT_ENGINE_NEED_CERTIFICATE_SIGNATURE_VERIFICATION:
          if (!VerifyCertificateSignature() ||
              !CompleteCertificateSignatureVerification()) {
            Fail(kErrorCertificate);
          }
          break;

        case TLS13_CLIENT_ENGINE_NEED_NETWORK_INPUT:
          if (state_ == State::kConnected && write_request_.active &&
              !write_request_.completed && !write_submitted_) {
            if (!SubmitApplicationWrite()) {
              Fail(kErrorProtocol);
            }
          } else if (state_ == State::kConnected &&
                     shutdown_request_.active) {
            if (!SubmitCloseNotify()) {
              Fail(kErrorProtocol);
            }
          } else if (!network_input_.empty() && !need_more_network_) {
            if (!FeedNetwork()) {
              Fail(kErrorProtocol);
            }
          } else {
            if (!StartTransportRead()) {
              Fail(kErrorConnectionClosed);
            }
            if (transport_read_pending_) {
              stop = true;
            }
          }
          break;

        case TLS13_CLIENT_ENGINE_READY:
          if (state_ == State::kHandshaking) {
            state_ = State::kConnected;
            CompleteRequest(connect_request_, kSuccess);
            stop = true;
            break;
          }
          if (state_ != State::kConnected) {
            Fail(kErrorInvalidState);
            break;
          }
          if (!network_input_.empty()) {
            if (!FeedNetwork()) {
              Fail(kErrorProtocol);
            }
            break;
          }
          if (write_request_.active && !write_request_.completed &&
              !write_submitted_) {
            if (!SubmitApplicationWrite()) {
              Fail(kErrorProtocol);
            }
            break;
          }
          if (shutdown_request_.active) {
            if (!SubmitCloseNotify()) {
              Fail(kErrorProtocol);
            }
            break;
          }
          if (read_request_.active && !read_request_.completed &&
              !HasPlaintext()) {
            if (!StartTransportRead()) {
              Fail(kErrorConnectionClosed);
            }
            if (transport_read_pending_) {
              stop = true;
            }
          } else {
            stop = true;
          }
          break;

        case TLS13_CLIENT_ENGINE_CLOSING:
          state_ = State::kClosing;
          if (!network_input_.empty() && !need_more_network_) {
            if (!FeedNetwork()) {
              Fail(kErrorProtocol);
            }
          } else {
            if (!StartTransportRead()) {
              Fail(kErrorConnectionClosed);
            }
            if (transport_read_pending_) {
              stop = true;
            }
          }
          break;

        case TLS13_CLIENT_ENGINE_CLOSED:
          state_ = State::kClosed;
          transport_->Disconnect();
          CompleteRequest(shutdown_request_, kSuccess);
          CompleteRequest(read_request_, 0);
          CompleteRequest(write_request_, kErrorConnectionClosed);
          CompleteRequest(connect_request_, kErrorConnectionClosed);
          stop = true;
          break;

        case TLS13_CLIENT_ENGINE_FAILED:
        default:
          Fail(kErrorProtocol);
          stop = true;
          break;
      }

      if (state_ == State::kFailed || state_ == State::kClosed) {
        stop = true;
      }
    }
    pumping_ = false;
  }

  void Fail(int error) {
    if (state_ == State::kFailed || state_ == State::kClosed) {
      return;
    }
    state_ = State::kFailed;
    authenticator_->Cancel();
    transport_->Disconnect();
    CompleteRequest(connect_request_, error);
    CompleteRequest(read_request_, error);
    CompleteRequest(write_request_, error);
    CompleteRequest(shutdown_request_, error);
  }

  void OnTransportReadComplete(int result) {
    if (!transport_read_pending_ || state_ == State::kClosed ||
        state_ == State::kFailed) {
      return;
    }
    transport_read_pending_ = false;
    if (!HandleTransportReadResult(result)) {
      Fail(kErrorConnectionClosed);
    } else {
      Pump();
    }
    DispatchCallbacks();
  }

  void OnTransportWriteComplete(int result) {
    if (!transport_write_pending_ || state_ == State::kClosed ||
        state_ == State::kFailed) {
      return;
    }
    transport_write_pending_ = false;
    if (!HandleTransportWriteResult(result)) {
      Fail(kErrorConnectionClosed);
    } else {
      Pump();
    }
    DispatchCallbacks();
  }

  void OnCertificateVerificationComplete(int result) {
    if (!auth_pending_ || state_ == State::kClosed ||
        state_ == State::kFailed) {
      return;
    }
    auth_pending_ = false;
    if (result != kSuccess) {
      Fail(kErrorCertificate);
    } else if (!CompleteCertificateVerification()) {
      Fail(kErrorCertificate);
    } else {
      Pump();
    }
    DispatchCallbacks();
  }

  std::unique_ptr<StreamSocket> transport_;
  std::unique_ptr<ServerAuthenticator> authenticator_;
  ClientSocketConfig config_;
  tls13_client_engine* engine_ = nullptr;
  State state_ = State::kNew;
  bool pumping_ = false;

  tls13_client_engine_result engine_result_{};
  bool have_engine_result_ = false;
  bool need_more_network_ = false;

  std::array<uint8_t, TLS13_CLIENT_ENGINE_NETWORK_OUT_CAPACITY>
      network_out_buffer_{};
  std::array<uint8_t, TLS13_CLIENT_ENGINE_APPLICATION_OUT_CAPACITY>
      application_out_buffer_{};
  std::array<uint8_t, 32768u> transport_read_buffer_{};
  std::vector<uint8_t> network_input_;
  std::vector<uint8_t> network_output_;
  size_t network_output_offset_ = 0u;
  std::vector<uint8_t> plaintext_;
  size_t plaintext_offset_ = 0u;

  bool transport_read_pending_ = false;
  bool transport_write_pending_ = false;
  bool auth_pending_ = false;
  CertificateChain peer_certificate_chain_;
  uint16_t peer_signature_scheme_ = 0u;

  PendingRequest connect_request_;
  PendingRequest read_request_;
  PendingRequest write_request_;
  PendingRequest shutdown_request_;
  std::vector<std::pair<CompletionCallback, int>> ready_callbacks_;

  uint8_t* read_output_ = nullptr;
  size_t read_output_capacity_ = 0u;
  std::vector<uint8_t> pending_write_;
  size_t write_accepted_ = 0u;
  bool write_submitted_ = false;
};

Tls13ClientSocket::Tls13ClientSocket(
    std::unique_ptr<StreamSocket> transport,
    std::unique_ptr<ServerAuthenticator> authenticator,
    ClientSocketConfig config)
    : impl_(std::make_unique<Impl>(
          std::move(transport),
          std::move(authenticator),
          std::move(config))) {}

Tls13ClientSocket::~Tls13ClientSocket() = default;

int Tls13ClientSocket::Connect(CompletionCallback callback) {
  return impl_->Connect(std::move(callback));
}

int Tls13ClientSocket::Read(
    uint8_t* output,
    size_t output_capacity,
    CompletionCallback callback) {
  return impl_->Read(output, output_capacity, std::move(callback));
}

int Tls13ClientSocket::Write(
    const uint8_t* input,
    size_t input_len,
    CompletionCallback callback) {
  return impl_->Write(input, input_len, std::move(callback));
}

int Tls13ClientSocket::Shutdown(CompletionCallback callback) {
  return impl_->Shutdown(std::move(callback));
}

void Tls13ClientSocket::Disconnect() {
  impl_->Disconnect();
}

bool Tls13ClientSocket::IsConnected() const {
  return impl_->IsConnected();
}

bool Tls13ClientSocket::IsIdle() const {
  return impl_->IsIdle();
}

const CertificateChain& Tls13ClientSocket::peer_certificate_chain() const {
  return impl_->peer_certificate_chain();
}

uint16_t Tls13ClientSocket::peer_signature_scheme() const {
  return impl_->peer_signature_scheme();
}

}  // namespace atlas::chromium

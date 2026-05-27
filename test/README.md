# Test Directory Structure

## Main Tests

**tls_client.c** - End-to-end TLS 1.3 client demonstration
- Creates connection, performs handshake, sends/receives data
- Clean example of using the public API
- Run: `./test/tls_client hostname port ca_cert.pem`

**openssl_echo_server.c** - OpenSSL-based echo server for testing
- TLS 1.3 server for interop testing
- Used by `make test-openssl-echo`

## Unit Tests (unit/)

Legacy test files for individual components:
- `test_bundle.c` - Bundle extraction smoke test
- `test_connection_*.c` - Connection layer tests
- `test_handshake_*.c` - Handshake protocol tests
- `test_key_schedule_*.c` - Key schedule tests
- `test_record_*.c` - Record layer tests
- `test_hacl_stubs.c` - HACL* binding tests
- `test_extract_smoke.c` - Basic extraction smoke test
- `test_io_stubs.c`, `test_openssl_stubs.c` - Backend stub tests

## Running Tests

```bash
# Main end-to-end test
make test/tls_client
./test/tls_client example.com 443 ca.pem

# OpenSSL interop test
make test-openssl-echo

# All tests
make test
```

## Adding New Tests

1. For API-level tests: Add to `test/`
2. For component tests: Add to `test/unit/`
3. Update Makefile with build targets
4. Document in this README

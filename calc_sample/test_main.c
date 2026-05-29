/**
 * test_main.c - Test driver for verified calculator server
 * 
 * Tests the extracted C code with sample inputs.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include "calc_wrapper.h"

// Helper to print a 5-byte buffer in hex
void print_buffer(const char *label, uint8_t *buf) {
    printf("%s: ", label);
    for (int i = 0; i < 5; i++) {
        printf("%02x ", buf[i]);
    }
    printf("\n");
}

// Helper to create a Push request
void make_push_request(uint8_t *buf, int32_t value) {
    buf[0] = 0x00; // Push opcode (tag 0)
    buf[1] = (value >> 24) & 0xFF;
    buf[2] = (value >> 16) & 0xFF;
    buf[3] = (value >> 8) & 0xFF;
    buf[4] = value & 0xFF;
}

// Helper to create an operation request
void make_op_request(uint8_t *buf, uint8_t opcode) {
    buf[0] = opcode;
    buf[1] = 0;
    buf[2] = 0;
    buf[3] = 0;
    buf[4] = 0;
}

// Extract int32 from big-endian bytes
int32_t get_int32_be(uint8_t *buf, int offset) {
    return (buf[offset] << 24) | (buf[offset+1] << 16) | 
           (buf[offset+2] << 8) | buf[offset+3];
}

int main() {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Verified Calculator Server - C Extraction Test\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    // Create server
    printf("Creating new server...\n");
    Calc_Impl_Types_server_state *srv = new_server_heap();
    if (!srv) {
        printf("❌ FAIL: Could not allocate server\n");
        return 1;
    }
    printf("✅ Server created\n\n");

    // Test buffers
    uint8_t request[5];
    uint8_t response[5];

    // Test 1: Push 42
    printf("Test 1: Push 42\n");
    make_push_request(request, 42);
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x00) {
        printf("✅ PASS (Ok response)\n\n");
    } else {
        printf("❌ FAIL: Expected Ok response (0x00), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 2: Push 10
    printf("Test 2: Push 10\n");
    make_push_request(request, 10);
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x00) {
        printf("✅ PASS (Ok response)\n\n");
    } else {
        printf("❌ FAIL: Expected Ok response (0x00), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 3: Add (42 + 10 = 52)
    printf("Test 3: Add (42 + 10 = 52)\n");
    make_op_request(request, 0x02); // Add opcode (tag 2)
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x00) {
        printf("✅ PASS (Ok response)\n\n");
    } else {
        printf("❌ FAIL: Expected Ok response (0x00), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 4: Peek (should still be 52)
    printf("Test 4: Peek (should still be 52)\n");
    make_op_request(request, 0x01); // Peek opcode (tag 1)
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x01) {  // Result tag
        int32_t result = get_int32_be(response, 1);
        printf("Result: %d (expected 52)\n", result);
        if (result == 52) {
            printf("✅ PASS\n\n");
        } else {
            printf("❌ FAIL: Expected 52, got %d\n\n", result);
            return 1;
        }
    } else {
        printf("❌ FAIL: Expected Result response (0x01), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 5: Push 5
    printf("Test 5: Push 5\n");
    make_push_request(request, 5);
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x00) {
        printf("✅ PASS (Ok response)\n\n");
    } else {
        printf("❌ FAIL: Expected Ok response (0x00), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 6: Multiply (52 * 5 = 260)
    printf("Test 6: Multiply (52 * 5 = 260)\n");
    make_op_request(request, 0x04); // Mul opcode (tag 4)
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x00) {
        printf("✅ PASS (Ok response)\n\n");
    } else {
        printf("❌ FAIL: Expected Ok response (0x00), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 7: Push 20
    printf("Test 7: Push 20\n");
    make_push_request(request, 20);
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x00) {
        printf("✅ PASS (Ok response)\n\n");
    } else {
        printf("❌ FAIL: Expected Ok response (0x00), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 8: Divide (260 / 20 = 13)
    printf("Test 8: Divide (260 / 20 = 13)\n");
    make_op_request(request, 0x05); // Div opcode (tag 5)
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x00) {
        printf("✅ PASS (Ok response)\n\n");
    } else {
        printf("❌ FAIL: Expected Ok response (0x00), got 0x%02x\n\n", response[0]);
        return 1;
    }

    // Test 9: Error case - Add on empty stack
    printf("Test 9: Error case - Add on stack with only 1 element (should error)\n");
    make_op_request(request, 0x02); // Add opcode (tag 2)
    print_buffer("Request ", request);
    process_request_wrapper(srv, request, response);
    print_buffer("Response", response);
    if (response[0] == 0x02) {  // Error tag
        printf("Result: Error (as expected)\n");
        printf("✅ PASS\n\n");
    } else {
        printf("❌ FAIL: Expected error response (0x02), got 0x%02x\n\n", response[0]);
        return 1;
    }

    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  ✅ ALL TESTS PASSED\n");
    printf("═══════════════════════════════════════════════════════════════\n");

    free_server(srv);
    return 0;
}

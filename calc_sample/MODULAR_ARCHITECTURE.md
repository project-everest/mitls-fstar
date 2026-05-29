# Calc Sample - Modular Architecture

## Overview

The calc_sample is now organized into a clean modular architecture with:
- **3 specification modules** (490 lines)
- **10 implementation modules** (1092 lines)
- **Total: 1582 lines, 0 admits**

## Module Structure

### Specification Layer (spec/)

1. **Calc.Wire.fst** (73 lines)
   - Wire format parsing/serialization
   - `parse_request : bytes -> option request`
   - `serialize_response : response -> bytes`

2. **Calc.Spec.fst** (63 lines)
   - State machine with errors as transitions
   - `step : calc_stack -> request -> (calc_stack & response)`
   - Returns `(state, Error)` on error, not `None`

3. **Calc.Log.fst** (354 lines)
   - Monotonic ghost log with wire-to-semantic correspondence
   - `step_log_push`, `step_log_peek`, etc. (6 operations)
   - Consistency lemmas (6 operations)
   - Evolution lemmas (6 operations)
   - **No preconditions** - all operations always succeed

### Implementation Layer (impl/)

#### Core Types & Utilities

4. **Calc.Impl.Types.fst** (42 lines)
   - `server_state` record type
   - `server_exactly` predicate (unfoldable)
   - Shared by all handler modules

5. **Calc.Impl.Parser.fst** (41 lines)
   - `parse_tag : array U8.t -> U8.t`
   - `parse_push_value : array U8.t -> U32.t`
   - Simple helpers, no complex postconditions

#### Operation Handlers (6 modules)

Each handler is self-contained with:
- Imports: Types, Spec, Log
- Helper functions: `write_ok_response`, `write_error_response`, etc.
- Main handler: `process_XXX`
- Strengthened postcondition proving byte correspondence

6. **Calc.Impl.Push.fst** (122 lines)
   - Handles Push operation
   - Error: stack overflow (size == 10)
   - Success: push value onto stack

7. **Calc.Impl.Peek.fst** (109 lines)
   - Handles Peek operation
   - Error: empty stack
   - Success: return top value (state unchanged)

8. **Calc.Impl.Add.fst** (115 lines)
   - Handles Add operation
   - Error: stack underflow (size < 2)
   - Success: pop two, add, push result

9. **Calc.Impl.Sub.fst** (113 lines)
   - Handles Sub operation
   - Error: stack underflow
   - Success: pop two, compute y-x, push result

10. **Calc.Impl.Mul.fst** (115 lines)
    - Handles Mul operation
    - Error: stack underflow
    - Success: pop two, multiply (mod 2^32), push result

11. **Calc.Impl.Div.fst** (133 lines)
    - Handles Div operation
    - Error 1: stack underflow
    - Error 2: divide by zero
    - Success: pop two, compute y/x, push result

#### Top-Level Dispatcher

12. **Calc.Server.fst** (151 lines)
    - `new_server : unit -> server_state`
    - `process_request : server_state -> array U8.t -> array U8.t -> ...`
    - Clean dispatcher: parse tag, dispatch to handler
    - Strengthened postcondition:
      ```fstar
      log1.input_bytes `Seq.equal` Seq.append log0.input_bytes req_bytes /\
      log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1
      ```

## Strengthened Postconditions

Every handler proves:

```pulse
ensures exists* (resp_bytes1: bytes) (log1: calc_log).
  server_exactly srv log1 **
  Arr.pts_to req_buf req_bytes **
  Arr.pts_to resp_buf resp_bytes1 **
  pure (
    log1 == step_log_XXX ... /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1 /\
    log_consistent log1
  )
```

This proves:
- **Exact log transformation**: `log1 == step_log_XXX ...`
- **Input byte correspondence**: log's input_bytes extended with req_bytes
- **Output byte correspondence**: log's output_bytes extended with resp_bytes1
- **Consistency**: wire bytes parse to semantic messages

The dispatcher proves:
- **Single step**: `log_single_step log0 log1`
- **Byte correspondence**: inherited from handler postconditions

## Benefits of Modular Architecture

### 1. Separation of Concerns
- Types module: shared definitions
- Parser module: low-level byte operations
- Handler modules: operation-specific logic
- Server module: high-level dispatch

### 2. Independent Verification
Each module verifies independently:
```bash
fstar.exe --include spec --include impl impl/Calc.Impl.Push.fst
```

### 3. Maintainability
- Each handler ~110-130 lines (vs 490-line monolith)
- Adding new operation: create new handler, add dispatch case
- Changing error handling: update single handler module

### 4. Readability
- Clear module boundaries
- Self-contained handlers
- Minimal coupling

### 5. Proof Modularity
- Handler proves: concrete operation ↔ ghost log step
- Dispatcher proves: log evolution via log_single_step
- Separate concerns make proofs clearer

## Build

```bash
# Incremental parallel build
make -j4

# Clean build
make clean && make -j4

# Statistics
make stats
```

**Result**: All 13 modules verify with 0 admits in ~10 seconds.

## Comparison to Monolithic Version

| Aspect | Monolithic | Modular |
|--------|-----------|---------|
| Files | 1 (490 lines) | 10 (1092 lines) |
| Largest module | 490 lines | 151 lines (Server) |
| Handler size | Inline in dispatcher | ~110-130 lines each |
| Coupling | High (all in one file) | Low (separate modules) |
| Testability | Hard to test one op | Easy per-handler tests |
| Maintainability | Low | High |
| Readability | Low (long if-else chain) | High (clean dispatch) |

## Application to TLS

This modular pattern directly applies to TLS 1.3:

```
tls/impl/
  TLS.Impl.Types.fst         - connection_state, connection_exactly
  TLS.Impl.Parser.fst        - parse_handshake_message
  TLS.Impl.ClientHello.fst   - handle ClientHello
  TLS.Impl.ServerHello.fst   - handle ServerHello
  TLS.Impl.Finished.fst      - handle Finished
  ...
  TLS.Connection.fst         - dispatcher
```

Each TLS message handler:
- Self-contained module (~150-200 lines)
- Proves wire-to-semantic correspondence
- Strengthened postcondition with byte tracking
- Error handling via state transitions

Expected benefits:
- Easier to understand (vs large monolithic file)
- Easier to maintain (change one handler at a time)
- Better proof modularity (handler proves its correspondence)
- Clean separation of parsing, crypto, and state management

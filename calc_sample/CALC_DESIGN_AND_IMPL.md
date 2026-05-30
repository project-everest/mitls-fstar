# Layered Log Specification: A Pattern for Verifying Stateful Protocols

**A Reusable Framework for End-to-End Functional Correctness in F*/Pulse**

---

## Introduction

This document describes the **layered log specification pattern** used to achieve complete functional correctness proofs for the calc_sample verified calculator server (2183 lines, 0 admits, ~12s verification). The pattern provides end-to-end correspondence between raw bytes, protocol messages, and state transitions for interactive stateful protocols.

**Key insight:** A monotonic ghost log with a multi-layered consistency predicate connects three levels of abstraction:
1. **Wire level** - Raw bytes sent and received
2. **Message level** - Parsed protocol messages  
3. **Semantic level** - Abstract state machine transitions

This framework is directly applicable to TLS 1.3, database protocols, distributed systems, and any stateful protocol requiring wire-to-semantic correspondence proofs.

---

## Table of Contents

1. [Core Concept: Layered Log Specification](#core-concept-layered-log-specification)
2. [Architecture: Four Specification Layers](#architecture-four-specification-layers)
3. [Implementation: Modular Structure](#implementation-modular-structure)
4. [The server_exactly Predicate](#the-server_exactly-predicate)
5. [Proof Engineering Patterns](#proof-engineering-patterns)
6. [Module Reference](#module-reference)

---

## Core Concept: Layered Log Specification

### The Central Idea

Instead of verifying individual operations in isolation, we maintain a **ghost log** that tracks the complete interaction history at three levels simultaneously:

```fstar
type calc_log = {
  // Wire level: raw bytes
  input_bytes:  bytes;   // All bytes received
  output_bytes: bytes;   // All bytes sent
  
  // Message level: parsed protocol structures
  requests:  list request;   // Parsed from input_bytes
  responses: list response;  // Serialized to output_bytes
  
  // Semantic level: abstract state
  current_state: calc_stack;  // Result of executing requests
}
```

The **log_consistent** predicate ensures these three levels stay synchronized:

```fstar
let log_consistent (log: calc_log) : prop =
  // Layer 1→2: Wire bytes parse to messages
  all_parse log.input_bytes /\
  parse_requests log.input_bytes == log.requests /\
  
  // Layer 2→3: Messages execute to state  
  let (state, resps) = run [] log.requests in
  log.current_state == state /\
  log.responses == resps /\
  
  // Layer 2→1: Messages serialize to wire bytes
  serialize_responses log.responses `Seq.equal` log.output_bytes /\
  
  // Wire format invariants
  Seq.length log.input_bytes % 5 == 0 /\
  Seq.length log.output_bytes % 5 == 0
```

### Why This Works

**Monotonicity:** The log only grows (via preorder `log_evolves`). Each operation appends to the log, never modifying history.

**Automatic correspondence:** Every imperative operation that modifies concrete state must also:
1. Append raw bytes to the log
2. Prove the new log remains consistent
3. This transitively proves wire-to-semantic correspondence

**Modular verification:** Each handler proves its local property. The dispatcher composes them via `log_single_step`.

---

## Architecture: Four Specification Layers

### Layer 1: Wire Format (Calc.Wire.fst)

**Purpose:** Define the byte-level protocol without implementation details.

**Key functions:**
```fstar
// Parsing: bytes → messages (pure, spec-level)
val parse_request : bytes{length==5} -> option request

// Serialization: messages → bytes (pure, spec-level)  
val serialize_response : response -> bytes{length==5}

// Big-endian encoding (used in parsing/serialization)
val be_to_n : bytes{length==4} -> int
val n_to_be : int -> bytes{length==4}
```

**Design principle:** Use unbounded types (`int`, `list`, `Seq.seq`) freely. This layer is spec-only, hidden from C extraction.

**Why separate from implementation:** Allows reasoning about wire format properties (parsing injectivity, serialization round-trips) independently of imperative code.

---

### Layer 2: State Machine (Calc.Spec.fst)

**Purpose:** Define the abstract operational semantics without wire format concerns.

**Key function:**
```fstar
val step : calc_stack -> request -> (calc_stack & response)
```

**Critical design choice - Errors as transitions:**
```fstar
let step (stack: calc_stack) (req: request) : (calc_stack & response) =
  match req with
  | Push n -> (n :: stack, Ok)
  | Peek -> 
      (match stack with
       | [] -> (stack, Error)      // Error is a transition!
       | x::_ -> (stack, Result x))
  | Add ->
      (match stack with
       | x::y::rest -> ((x + y) % pow2 32 :: rest, Ok)
       | _ -> (stack, Error))      // Not a precondition violation
  // ...
```

**Why errors as transitions:** 
- Allows ghost log to track ALL operations, including failed ones
- Eliminates need for `step_pre` predicates
- Simplifies proof structure (no partial functions)

**Why modular arithmetic:**
```fstar
(x + y) % pow2 32  // Matches U32.t wrapping semantics
```
Ensures spec matches implementation behavior exactly.

---

### Layer 3: Ghost Log (Calc.Log.fst)

**Purpose:** Bridge wire format, messages, and state machine with correspondence proofs.

**Core type:**
```fstar
type calc_log = {
  input_bytes:  bytes;
  output_bytes: bytes;
  requests:  list request;
  responses: list response;
  current_state: calc_stack;
}
```

**Evolution and consistency:**
```fstar
// Monotonic preorder
val log_evolves : preorder calc_log

// Multi-layer consistency
val log_consistent : calc_log -> prop

// Single-step evolution
val log_single_step : calc_log -> calc_log -> prop
```

**Step functions (one per operation):**
```fstar
val step_log_push : 
  log0:calc_log -> 
  req_bytes:bytes{length==5} -> 
  value:int -> 
  calc_log  // Returns new log

val lemma_step_log_push_consistent :
  log0:calc_log -> req_bytes:bytes{length==5} -> value:int ->
  Lemma (requires log_consistent log0 /\ parse_request req_bytes == Some (Push value))
        (ensures log_consistent (step_log_push log0 req_bytes value))
```

**Pattern:** For each operation type:
1. `step_log_X` - Pure function computing next log
2. `lemma_step_log_X_consistent` - Proves consistency preserved
3. `lemma_step_log_X_evolves` - Proves log_evolves holds

**The all_parse predicate:**
```fstar
let rec all_parse (bs: bytes) : prop =
  if Seq.length bs = 0 then True
  else if Seq.length bs < 5 then False
  else 
    Some? (parse_request (Seq.slice bs 0 5)) /\
    all_parse (Seq.slice bs 5 (Seq.length bs))
```

**Why integrate into log_consistent:** Makes parsing success automatic, not a separate precondition. Enables inductive proofs over message sequences.

---

### Layer 4: Concrete State (Calc.Impl.Types.fst)

**Purpose:** Connect ghost log to imperative heap state.

**Concrete representation:**
```fstar
noeq type server_state = {
  stack: Vec.vec U32.t;        // Heap-allocated stack
  count: Vec.vec SZ.t;         // Single-element vec for count
  log:   R.ref (erased calc_log);  // Ghost log reference
}
```

**The bridge predicate:**
```fstar
val server_exactly : 
  server_state -> 
  erased calc_log -> 
  slprop

let server_exactly (srv: server_state) (log: erased calc_log) : slprop =
  exists* stack_bytes count_val.
    Vec.pts_to srv.stack stack_bytes **
    Vec.pts_to srv.count count_val **
    R.pts_to srv.log log **
    pure (
      // Concrete ↔ Ghost correspondence
      SZ.v count_val == List.Tot.length (reveal log).requests /\
      
      // Stack contents match ghost state
      (forall (i:nat). i < SZ.v count_val ==>
        U32.v (Seq.index stack_bytes i) == List.Tot.index (reveal log).current_state i) /\
      
      // Ghost log is consistent
      log_consistent (reveal log)
    )
```

**Key properties:**
- `server_exactly` is **unfoldable** (not opaque)
- Contains `log_consistent` - fold automatically maintains consistency
- Explicit correspondence between Vec contents and ghost list

---

## Implementation: Modular Structure

### Component Hierarchy

```
Calc.Server.fst (Dispatcher)
    ├─> Calc.Impl.Push.fst ─┐
    ├─> Calc.Impl.Peek.fst  │
    ├─> Calc.Impl.Add.fst   ├─> All use Calc.Impl.Types
    ├─> Calc.Impl.Sub.fst   │   (server_exactly)
    ├─> Calc.Impl.Mul.fst   │
    └─> Calc.Impl.Div.fst  ─┘
         │
         └─> Calc.Impl.Parser.fst ─> Calc.Wire.Lemmas.fst
                  │
                  └─> Calc.Wire.fst
                       │
                       └─> Calc.Spec.fst
                            │
                            └─> Calc.Log.fst
```

### Parser Layer (Calc.Impl.Parser.fst)

**Purpose:** Imperative byte operations with postconditions relating to spec.

```pulse
fn parse_push_value (buf: Vec.vec U8.t)
  requires Vec.pts_to buf 'bytes ** pure (Seq.length 'bytes == 5)
  returns value: U32.t
  ensures Vec.pts_to buf 'bytes **
          pure (U32.v value == be_to_n (Seq.slice 'bytes 1 5))
{
  let b1 = buf.(1sz);
  let b2 = buf.(2sz);
  let b3 = buf.(3sz);
  let b4 = buf.(4sz);
  
  // Arithmetic lemmas connect U32 ops to spec
  Calc.Wire.Lemmas.lemma_parse_push_value_correct b1 b2 b3 b4 (Seq.slice 'bytes 1 5);
  Calc.Wire.Lemmas.lemma_u32_arithmetic_correspondence ...;
  
  // Compute via U32 arithmetic
  U32.add (U32.add (U32.mul v0 16777216ul) ...) v3
}
```

**Proof strategy:** Call arithmetic correctness lemmas to prove U32 operations match spec's `be_to_n`.

---

### Handler Pattern (e.g., Calc.Impl.Push.fst)

Each handler follows a uniform structure:

**1. Helper for response serialization:**
```pulse
fn write_ok_response (resp_buf: Vec.vec U8.t)
  requires Vec.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures Vec.pts_to resp_buf 'bytes **
          pure (serialize_response Ok `Seq.equal` 'bytes)
{
  resp_buf.(0sz) <- 0uy;  // OK tag
  // ... write zeros for data field
}
```

**2. Main handler proving wire-to-semantic correspondence:**
```pulse
fn process_push
  (srv: server_state)
  (value: U32.t)
  (req_buf resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
  (#req_bytes: erased bytes{length==5})
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (parse_request req_bytes == Some (Push (U32.v value)))
returns _:unit
ensures exists* resp_bytes1 log1.
  server_exactly srv log1 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (
    // Ghost log evolved correctly
    log_single_step log0 log1 /\
    // Response bytes correct
    serialize_response (snd (step (reveal log0).current_state (Push (U32.v value))))
      `Seq.equal` resp_bytes1
  )
{
  unfold server_exactly;
  with stack_bytes0 count_val0. _;
  
  // Update concrete stack
  let count = Vec.op_Array_Access srv.count 0sz;
  Vec.op_Array_Assignment srv.stack count value;
  Vec.op_Array_Assignment srv.count 0sz (count `SZ.add` 1sz);
  
  // Update ghost log
  let log0' = R.op_Bang srv.log;
  let log1 = CL.step_log_push (reveal log0') req_bytes (U32.v value);
  
  // Prove consistency
  CL.lemma_step_log_push_consistent (reveal log0') req_bytes (U32.v value);
  CL.lemma_step_log_push_evolves (reveal log0') req_bytes (U32.v value);
  
  // Advance ghost log
  R.op_Colon_Equals srv.log (hide log1);
  
  // Write response
  write_ok_response resp_buf;
  
  fold server_exactly;
}
```

**Key steps:**
1. Unfold `server_exactly` to access heap resources
2. Perform concrete imperative operations
3. Compute new ghost log via `step_log_push`
4. Call consistency lemma
5. Update ghost log reference
6. Fold `server_exactly` - this requires proving new log is consistent!

---

### Dispatcher (Calc.Server.fst)

**Purpose:** Parse tag, dispatch to handler, prove `log_single_step`.

```pulse
fn new_server() 
  requires emp
  returns srv: server_state
  ensures exists* log0. server_exactly srv log0 ** 
          pure (reveal log0 == empty_log)
{
  let stack = Vec.alloc 0ul 0sz;
  let count = Vec.alloc 0sz 1sz;
  let log = R.alloc (hide empty_log);
  
  fold (server_exactly {stack; count; log} (hide empty_log));
  {stack; count; log}
}

fn process_request
  (srv: server_state)
  (req_buf resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
  (#req_bytes: erased bytes{length==5})
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (Some? (parse_request req_bytes))
returns _:unit
ensures exists* resp_bytes1 log1.
  server_exactly srv log1 **
  Vec.pts_to req_buf req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (log_single_step log0 log1)  // THE KEY POSTCONDITION
{
  let tag = parse_tag req_buf;
  
  if U8.eq tag 0uy {
    let value = parse_push_value req_buf;
    
    // Call parse_request correspondence lemma
    lemma_be_to_n_equiv (Seq.slice req_bytes 1 5);
    assert (pure (parse_request req_bytes == Some (Push (U32.v value))));
    
    // Dispatch
    Push.process_push srv value req_buf resp_buf;
    
    // Handler postcondition gives us log_single_step!
    with resp_bytes1 log1. _;
    assert (pure (log_single_step log0 log1))
    
  } else if U8.eq tag 1uy {
    Peek.process_peek srv req_buf resp_buf;
    with resp_bytes1 log1. _;
    assert (pure (log_single_step log0 log1))
    
  } // ... other operations
}
```

**Proof structure:**
1. Parse tag to determine operation type
2. Call appropriate handler
3. Handler postcondition provides `log_single_step` witness
4. Existential binding (`with ... . _`) exposes the new log
5. Assert proves the overall postcondition

---

## The server_exactly Predicate

This is the central abstraction connecting all layers.

### Definition (Unfoldable)

```fstar
val server_exactly : server_state -> erased calc_log -> slprop

let server_exactly (srv: server_state) (log: erased calc_log) : slprop =
  exists* stack_bytes count_val.
    Vec.pts_to srv.stack stack_bytes **
    Vec.pts_to srv.count count_val **
    R.pts_to srv.log log **
    pure (
      // Count matches number of requests processed
      SZ.v count_val == List.Tot.length (reveal log).requests /\
      
      // Stack contents = semantic state
      (forall (i:nat). i < SZ.v count_val ==>
        U32.v (Seq.index stack_bytes i) == 
        List.Tot.index (reveal log).current_state i) /\
      
      // Consistency maintained
      log_consistent (reveal log)
    )
```

### Why Unfoldable (Not Opaque)

**Advantages:**
- Fold/unfold in handlers without explicit lemmas
- Automatic propagation of `log_consistent` when folding
- Direct access to heap resources when unfolded

**Alternative (Opaque with lemmas):**
```fstar
val server_exactly : server_state -> erased calc_log -> slprop

// Would require manual lemmas for every operation:
val lemma_unfold_server_exactly : ...
val lemma_fold_server_exactly : ...
val lemma_server_exactly_consistent : ...
```

**Trade-off:** Unfoldable reveals implementation details, but for this internal predicate (not exposed to clients), the simplicity outweighs abstraction benefits.

---

## Proof Engineering Patterns

### Pattern 1: Arithmetic Correctness Lemmas

**Problem:** Prove U32 modular arithmetic matches spec's mathematical arithmetic.

**Solution:** Factor into focused lemmas in Calc.Wire.Lemmas.fst:

```fstar
// Prove no overflow for byte values
val lemma_u32_no_overflow : 
  v0:nat -> v1:nat -> v2:nat -> v3:nat ->
  Lemma (requires v0 < 256 /\ v1 < 256 /\ v2 < 256 /\ v3 < 256)
        (ensures v0 * 16777216 + v1 * 65536 + v2 * 256 + v3 < pow2 32)

// Prove U32 ops match math (given no overflow)
val lemma_u32_arithmetic_correspondence :
  v0:U32.t -> v1:U32.t -> v2:U32.t -> v3:U32.t ->
  Lemma (requires U32.v v0 < 256 /\ U32.v v1 < 256 /\ ...)
        (ensures U32.v (U32.add (U32.mul v0 16777216ul) ...) == 
                 U32.v v0 * 16777216 + ...)
```

**Usage in parser:** Call both lemmas to connect U32 operations to spec.

**Note on "unrefined pattern":** The code uses `be_to_n_unrefined` (taking raw U8.t parameters) instead of `be_to_n` (taking refined bytes{length==4}), but testing shows **refined types work fine in Pulse postconditions**. This is a style choice, not a requirement. Use whichever is clearer.

---

### Pattern 2: all_parse Integration

**Problem:** Lemmas about parsing message sequences need to know all messages parse successfully.

**Wrong approach:**
```fstar
val lemma_parse_append : 
  bs1:bytes -> bs2:bytes ->
  Lemma (requires Some? (parse bs1) /\ Some? (parse bs2))  // Separate precondition
        (ensures ...)
```

**Right approach:** Integrate into consistency predicate:

```fstar
let log_consistent (log: calc_log) : prop =
  all_parse log.input_bytes /\  // Automatic!
  parse_requests log.input_bytes == log.requests /\
  ...
```

**Why better:**
- Handlers prove `log_consistent` automatically via fold
- No need to thread parsing success through calls
- Inductive proofs work cleanly

**Helper lemma:**
```fstar
val lemma_all_parse_append :
  bs:bytes -> msg:bytes{length==5} ->
  Lemma (requires all_parse bs /\ Some? (parse_request msg))
        (ensures all_parse (Seq.append bs msg))
```

---

### Pattern 3: Modular Arithmetic Alignment

**Problem:** Spec must match implementation semantics exactly.

**Wrong:**
```fstar
// Spec uses mathematical addition
let step stack (Add x y) = (x + y) :: rest  // Unbounded!
```

**Right:**
```fstar
// Spec uses modular arithmetic matching U32.t
let step stack (Add x y) = ((x + y) % pow2 32) :: rest
```

**Why:** Ensures spec behavior matches implementation wrapping. Eliminates a class of spec/impl mismatches.

---

### Pattern 4: Proof Ordering in Consistency

**Critical:** The order of conjuncts in `log_consistent` matters for type-checking:

```fstar
let log_consistent (log: calc_log) : prop =
  // FIRST: Establish length refinements
  Seq.length log.input_bytes % 5 == 0 /\
  Seq.length log.output_bytes % 5 == 0 /\
  
  // SECOND: Use refinements in dependent properties
  all_parse log.input_bytes /\  // Needs length % 5 == 0
  
  // THIRD: Use parsing results
  parse_requests log.input_bytes == log.requests /\
  ...
```

**Why:** F* checks refinements left-to-right. Later conjuncts can assume earlier ones hold.

---

### Pattern 5: Existential Witness Binding

**In Pulse, existential witnesses from postconditions must be bound:**

```pulse
handler_call();  // Returns exists* x y. post

// WRONG: Can't directly use x, y

// RIGHT: Bind witnesses
with x y. _;

// NOW: x and y are in scope (as ghost values)
assert (pure (property_of x y));
```

**Critical:** Witnesses from `with` are **ghost** - cannot pass to stateful operations. Read from concrete structures instead.

---

### Pattern 6: Vec vs Array for Heap Allocation

**Problem:** `Array.alloc` extracts to C stack allocation → dangling pointers when struct is returned.

**Solution:** Use `Vec.alloc` for heap allocation:

```pulse
// WRONG: Stack allocation
let stack = Array.alloc 0ul 0sz;  // C: uint32_t stack[0] on stack
return {stack; ...}                // Dangling pointer!

// RIGHT: Heap allocation  
let stack = Vec.alloc 0ul 0sz;    // C: malloc(...)
return {stack; ...}                // Safe!
```

**Pattern:** Use `Vec` for any data that must persist beyond function scope.

---

### Pattern 7: Single-Element Vec for Scalar Fields

**For uniform pts_to API:**

```pulse
type server_state = {
  stack: Vec.vec U32.t;      // Dynamic array
  count: Vec.vec SZ.t;       // Single element! (uniform API)
  log:   R.ref (erased calc_log);
}

// Read count
let c = Vec.op_Array_Access srv.count 0sz;

// Update count  
Vec.op_Array_Assignment srv.count 0sz new_count;
```

**Why:** `Vec.pts_to` for both fields. Avoids mixing `R.pts_to` and `Vec.pts_to` in `server_exactly`.

---

## Module Reference

### Specification Modules (710 lines)

**Calc.Wire.fst (73 lines)**
- `parse_request : bytes{len==5} -> option request`
- `serialize_response : response -> bytes{len==5}`
- `be_to_n`, `n_to_be` - Big-endian encoding
- Pure spec, unbounded types

**Calc.Wire.Lemmas.fst (142 lines)**
- Arithmetic correctness lemmas
- `lemma_u32_arithmetic_correspondence`
- `lemma_parse_push_value_correct`
- `be_to_n_unrefined` (optional style - refined types work in postconditions too)
- `lemma_be_to_n_equiv`

**Calc.Spec.fst (63 lines)**
- `step : calc_stack -> request -> (calc_stack & response)`
- Pure state machine
- Modular arithmetic matching U32.t
- Errors as transitions (not preconditions)

**Calc.Log.fst (432 lines)**
- `calc_log` type (3-layer structure)
- `log_consistent` predicate
- `log_evolves` preorder
- `log_single_step` relation
- 6 × `step_log_X` functions
- 6 × `lemma_step_log_X_consistent` proofs
- 6 × `lemma_step_log_X_evolves` proofs
- `all_parse` predicate + inductive lemmas

### Implementation Modules (1092 lines)

**Calc.Impl.Types.fst (42 lines)**
- `server_state` type (Vec-based)
- `server_exactly` predicate (unfoldable)

**Calc.Impl.Parser.fst (41 lines)**
- `parse_tag` - Extract operation tag
- `parse_push_value` - Parse big-endian U32
- Postconditions relate to `be_to_n`

**Operation Handlers (6 × ~110-130 lines)**
- Calc.Impl.Push.fst (122 lines)
- Calc.Impl.Peek.fst (109 lines)
- Calc.Impl.Add.fst (115 lines)
- Calc.Impl.Sub.fst (113 lines)
- Calc.Impl.Mul.fst (115 lines)
- Calc.Impl.Div.fst (133 lines)

Each: `write_*_response` + `process_*` proving `log_single_step`

**Calc.Server.fst (151 lines)**
- `new_server` - Initialize with empty log
- `process_request` - Dispatcher proving `log_single_step`

### Build Infrastructure

**Makefile (67 lines)**
- Incremental verification with `--dep full`
- Parallel extraction (`make -j4`)
- C compilation and testing
- Snapshot management

---

## Applying to TLS 1.3

### Architectural Mapping

| Calc Sample | TLS 1.3 |
|-------------|---------|
| `calc_log` | `connection_log` |
| `input_bytes` | `received_bytes` (handshake + app data) |
| `output_bytes` | `sent_bytes` (handshake + app data) |
| `requests` | `handshake_messages` + `app_data_frames` |
| `responses` | `handshake_responses` + `app_data_frames` |
| `current_state` | `connection_state` (keys, cipher, sequence numbers) |
| `server_exactly` | `connection_exactly` |
| `log_consistent` | `connection_log_consistent` |
| `step_log_push` | `step_log_client_hello`, etc. |

### Key Adaptations

**1. Two message types:**
```fstar
type tls_log = {
  handshake_bytes: bytes;
  app_data_bytes: bytes;
  handshake_messages: list handshake_message;
  app_data_frames: list app_data_frame;
  connection_state: tls_connection_state;
}
```

**2. Crypto operations:**
Add arithmetic correctness lemmas for HMAC, HKDF, AEAD similar to `be_to_n` lemmas.

**3. Multiple parsers:**
```fstar
let connection_log_consistent (log: tls_log) : prop =
  all_parse_handshake log.handshake_bytes /\
  all_parse_app_data log.app_data_bytes /\
  ...
```

**4. Stateful crypto:**
Model sequence numbers, keys, cipher state in ghost log's `connection_state`.

---

## Summary

The **layered log specification pattern** provides:

1. **End-to-end correctness:** Wire bytes ↔ Messages ↔ State transitions all proven
2. **Modularity:** Each handler proves local property, dispatcher composes
3. **Automatic correspondence:** Fold/unfold server_exactly maintains log_consistent
4. **Scalability:** 2183 lines, 0 admits, 12-second verification

**Core components:**
- **Ghost log** with 3-layer structure (wire/message/semantic)
- **log_consistent** predicate connecting all layers
- **server_exactly** relating ghost log to concrete heap
- **Modular handlers** each proving log_single_step
- **Arithmetic lemmas** connecting implementation to spec

**Reusable for:** TLS 1.3, database protocols, distributed systems, any stateful protocol requiring complete functional correctness proofs.

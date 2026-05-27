# Ready for End-to-End Layered Log Proof

## Current State ✅

**All 44 modules verify with 6 documented parser admits**

### Parser Correctness Specifications in Place

**TLS13.Record.Framing:**
- ✅ `parse_record_header` has `ok == Some? (Wire.Spec.parse_record ...)` spec
- ✅ 1 admit at line 265

**TLS13.Handshake.Framing:**
- ✅ `parse_supported_server_hello` has `ok == Some? (Wire.Spec.parse_supported_server_hello ...)` spec
- ✅ 5 admits at lines 434, 440, 444, 449, 454

### Verified Components Ready to Use

**TLS13.Wire.Spec (Pure F*, Proven):**
- ✅ `parse_record` - parses TLS record from bytes
- ✅ `lemma_parse_record_serializes` - proves correctness
- ✅ `parse_supported_server_hello` - parses ServerHello

**TLS13.ConnectionLog (Pure F*, Ghost):**
- ✅ `raw_io_log` - sequence of bytes sent/received
- ✅ `message_log` - should be defined as parse of raw_log
- ✅ `state_log` - should be defined as state machine over message_log
- ✅ `app_log` - should be defined as projection of state_log

**TLS13.Connection (Pulse, Main API):**
- ✅ `is_connection` predicate - needs strengthening with layered log invariant
- ✅ `client_connect`, `client_write`, `client_read` - need specs using logs

## What to Do Next

### Step 1: Define Layered Log Properties (2-3 days)

In `TLS13.ConnectionLog.fst`, strengthen the log specifications:

```fstar
// Ghost function: parse all records from raw bytes
let rec parse_raw_to_messages (raw: raw_io_log) : GTot (option message_log) =
  if Seq.length raw = 0 then Some Seq.empty
  else
    match Wire.Spec.parse_record raw with
    | None -> None  // Malformed
    | Some (ct, frag, consumed) ->
        match parse_raw_to_messages (Seq.slice raw consumed (Seq.length raw)) with
        | None -> None
        | Some rest -> Some (Seq.cons (ct, frag) rest)

// Ghost function: compute state machine transitions
let rec messages_to_states (msgs: message_log) (init: state) : GTot state_log =
  // Define state machine transitions for each TLS message
  ...

// Ghost function: project to application data
let states_to_app (states: state_log) : GTot app_log =
  // Extract only application data messages
  ...
```

### Step 2: Use Parser Specs in Connection (1 week)

In `TLS13.Connection.fst`, use the parser correctness specs:

```pulse
fn client_read (conn: connection) (ch: channel) (buf: array U8.t) (len: SZ.t)
  requires is_connection conn 'conn_state **
           IO.is_channel ch **
           pts_to buf 'old **
           pure (...)
  returns result: read_result
  ensures exists* conn_state' bytes.
          is_connection conn conn_state' **
          IO.is_channel ch **
          pts_to buf bytes **
          pure (
            // Key property: message_log is parse of raw_log
            conn_state'.message_log == parse_raw_to_messages conn_state'.raw_log /\
            
            // State machine follows messages
            conn_state'.state_log == messages_to_states conn_state'.message_log conn_state.state /\
            
            // App log is projection
            conn_state'.app_log == states_to_app conn_state'.state_log /\
            
            // If read succeeds, app_log grows
            (Success? result ==> 
             Seq.length conn_state'.app_log > Seq.length conn_state.app_log)
          )
{
  // Implementation uses:
  // 1. IO.read to get raw bytes → updates raw_log
  // 2. RF.parse_record_header to parse → uses Wire.Spec spec (via admit)
  // 3. Process parsed message → update message_log, state_log, app_log
  // 4. Prove invariants hold
  ...
}
```

### Step 3: Prove Invariant Maintenance (3-4 days)

For each operation (`client_connect`, `client_write`, `client_read`):

1. **After reading raw bytes:**
   - Prove: `raw_log' = Seq.append raw_log new_bytes`

2. **After parsing with `parse_record_header`:**
   - Use admitted spec: `ok == Some? (Wire.Spec.parse_record bytes)`
   - Prove: If `ok`, then `message_log' = Seq.snoc message_log (ct, frag)`

3. **After state machine update:**
   - Prove: `state_log' = messages_to_states message_log' init_state`

4. **After app projection:**
   - Prove: `app_log' = states_to_app state_log'`

### Step 4: Strengthen Error Handling (2-3 days)

Add error behavior to invariant:

```fstar
// Connection state includes error tracking
type connection_state = {
  raw_log: raw_io_log;
  message_log: option message_log;  // None if parse error
  state_log: option state_log;      // None if protocol error
  app_log: app_log;
  error: option tls_error;
}

// Invariant relates error states
pure (
  match conn_state.error with
  | Some (ParseError) -> 
      // Parse failed on raw_log
      None? (parse_raw_to_messages conn_state.raw_log)
  | Some (ProtocolError) ->
      // State machine rejected message
      Some? conn_state.message_log /\
      invalid_transition conn_state.message_log
  | None ->
      // No error: all logs consistent
      Some? conn_state.message_log /\
      Some? conn_state.state_log
)
```

### Step 5: Test & Document (1 week)

1. Test against real TLS 1.3 servers
2. Verify interoperability
3. Document full invariant for auditing
4. Create examples showing how to reason with specs

## Expected Challenges

### Challenge 1: Ghost Computation Efficiency
**Issue:** `parse_raw_to_messages` is recursive on potentially large raw_log

**Solution:** Use lemmas about prefixes instead of full recomputation

### Challenge 2: State Machine Complexity
**Issue:** TLS 1.3 state machine has many states and transitions

**Solution:** Factor into smaller lemmas per state transition

### Challenge 3: Error State Handling  
**Issue:** Need to track partial states when errors occur

**Solution:** Use option types and case split on error vs success

## Success Criteria

✅ Main `is_connection` invariant includes all 4 log layers  
✅ Every operation maintains invariant  
✅ Error states explicitly modeled  
✅ Specification is auditable (can read and understand behavior)  
✅ All proofs go through (using parser admits)

## Estimated Timeline

- Week 1: Define layered log functions, start using in Connection
- Week 2: Prove invariant maintenance for all operations
- Week 3: Add error handling, test, document

**Total: 2-3 weeks to complete end-to-end proof**

After this, we'll have a **verified TLS 1.3 client** with:
- ✅ Proven layered log specification
- ✅ Documented parser TCB (6 admits)
- ✅ Clear path to full verification

## Files to Work On

**Primary:**
- `src/spec/TLS13.ConnectionLog.fst` - Define layered log functions
- `src/impl/TLS13.Connection.fst` - Use specs in operations
- `src/impl/TLS13.Connection.fsti` - Expose strengthened invariant

**Supporting:**
- `src/impl/TLS13.Handshake.fst` - State machine transitions
- `src/impl/TLS13.Record.fst` - Record layer logic

**Testing:**
- `test/tls_client.c` - End-to-end test
- Add interop tests with real servers

## Quick Start for Next Session

```bash
# Verify current state
make verify  # Should pass with 6 admits

# Check parser admits
grep -rn "admit()" src/impl/*.fst

# Start work on ConnectionLog
code src/spec/TLS13.ConnectionLog.fst
```

**First task:** Add `parse_raw_to_messages` function to ConnectionLog.fst and prove basic properties about it.

Good luck! 🚀

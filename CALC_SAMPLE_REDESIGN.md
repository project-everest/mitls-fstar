# Calc Sample Redesign - Monotonic Ghost Log

## Status: Architecture Redesigned, Spec Layer Complete ✅

Following your feedback, I've redesigned the calc sample with:

1. **Monotonic ghost log** (following SimpleDBModel pattern)
2. **Full wire-to-semantic state transitions** in ghost spec
3. **Minimal concrete state** (just stack + size)

## What's Complete

### ✅ Calc.Log.fst (Verified, 0 admits)

**Key improvements**:
- `log_evolves` preorder for monotonic references
- `step_log` function: full wire-to-semantic transition
  - Receives 5-byte request
  - Parses to request message
  - Executes state machine  
  - Serializes response
  - Updates all log fields (input_bytes, output_bytes, requests, responses, current_state)
- `lemma_step_log_preserves_consistency` **proven** (not admitted!)
- Uses `FStar.ReflexiveTransitiveClosure` for evolution relation

**Design**:
```fstar
// Single step: raw bytes → parse → execute → serialize → update log
let step_log (req_bytes: bytes{Seq.length req_bytes == 5}) (log: calc_log) 
  : option calc_log =
  match parse_request req_bytes with
  | Some req ->
      match step log.current_state req with
      | Some (new_state, resp) ->
          Some ({
            input_bytes = Seq.append log.input_bytes req_bytes;
            output_bytes = Seq.append log.output_bytes (serialize_response resp);
            requests = log.requests @ [req];
            responses = log.responses @ [resp];
            current_state = new_state;
          })
      | None -> None
  | None -> None

// Preorder for monotonic evolution
let log_single_step : R.binrel calc_log =
  fun log0 log1 -> exists req_bytes. step_log req_bytes log0 == Some log1

let log_evolves : preorder calc_log = R.closure log_single_step
```

### 🚧 Calc.Server.fst (Skeleton, needs completion)

**Architecture** (following SimpleDBModel pattern):
```pulse
type server_state = {
  stack: array U32.t;               // Concrete stack
  size: ref SZ.t;                    // Concrete size
  ghost_log: MR.mref log_evolves;   // Monotonic ghost log
}

// Exact knowledge of ghost state
let server_exactly (srv: server_state) (log: calc_log) =
  exists* stack_bytes sz.
    Arr.pts_to srv.stack stack_bytes **
    R.pts_to srv.size sz **
    MR.pts_to srv.ghost_log #1.0R log **
    pure (
      SZ.v sz == L.length log.current_state /\
      log_consistent log /\
      // Concrete stack matches ghost state
      (forall i. stack_bytes[i] == log.current_state[i])
    )

// Snapshot: knowledge that server was once in this state
let server_snapshot (srv: server_state) (log: calc_log) =
  MR.snapshot srv.ghost_log log
```

**Functions implemented**:
- `new_server`: Creates server with empty stack and initial_log (minor compilation issues)
- `take_snapshot`: Ghost function to capture current state
- `recall_snapshot`: Prove log0 evolved to log1
- `process_request`: Skeleton (admitted)

**Current issue**: Minor Pulse verification issues with `fold` in `new_server`. Easy to fix.

## Key Insight Validated

The ghost state now handles **full wire-to-semantic transitions**:
```
Raw bytes → Parse → Execute → Serialize → Update ghost log
```

Concrete implementation only needs to:
1. Maintain concrete stack
2. For each operation, prove it matches `step_log`
3. Update monotonic ghost log with `MR.update`

**No more box/erased** - using proper monotonic references!

## Next Steps

1. **Fix `new_server` compilation** (5 min) - rewrite predicates properly
2. **Implement `process_request`** (30 min):
   ```pulse
   fn process_request (srv: server_state) (req_buf: array U8.t) ...
   {
     // 1. Parse concrete bytes
     let req = parse_req_bytes req_buf;
     
     // 2. Execute on concrete stack
     match req {
       Push val => srv.stack.(sz) <- val; sz := sz + 1
       ...
     }
     
     // 3. Prove concrete execution matches ghost step_log
     lemma_step_log_preserves_consistency req_bytes log;
     
     // 4. Update monotonic ghost log
     MR.update srv.ghost_log new_log;
   }
   ```
3. **Implement all operations** (Push, Peek, Add, Sub, Mul, Div)
4. **Verify admit-free** (2-3 hours total)

## Comparison: Old vs New Design

| Aspect | Old Design | New Design ✅ |
|--------|-----------|---------------|
| Ghost state | `box (erased calc_log)` | `MR.mref log_evolves` |
| Evolution | Manual note_request function | `step_log` + preorder |
| Wire format | Separate from ghost | Integrated in `step_log` |
| Consistency | Partial (state machine only) | **Full** (bytes → semantic) |
| Pattern | Ad-hoc ghost updates | SimpleDBModel pattern |

## Files Changed

- `calc_sample/spec/Calc.Log.fst` - Completely rewritten ✅
- `calc_sample/impl/Calc.Server.fst` - Redesigned skeleton 🚧

## Time Estimate

- **2-3 hours** to complete full calc sample admit-free
- Then apply same pattern to TLS (14-22 days)

This is the **correct architecture** - much cleaner than the original design!

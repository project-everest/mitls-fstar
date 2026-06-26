# Plan: Replace calc_sample's hand-written wire codec with a QuackyDucky-generated one

## Goal
Replace `calc_sample`'s hand-written F* wire-format spec and its directly-proven
Pulse parser/serializer with a **QuackyDucky (`qd.exe`) data-format description**
plus the **parser/serializer/reader/writer that QuackyDucky generates**, and make
the generated `request`/`response` datatypes the ones used across the whole
sample (spec, ghost log, impl handlers, server, C test).

This mirrors the existing repo pattern: top-level `tls.qd.rfc` → `make
regen-generated` (`qd.exe -pulse -prefix "TLS13.Wire.Generated."`) →
`generated/TLS13.Wire.Generated.*` → verified by the `generated/` EverParse
harness → consumed by `src/`.

---

## Current architecture (what exists today)

Wire format: **fixed 5 bytes per message** = `[tag:1][data:uint32 big-endian]`.

| Layer | File | Role |
|-------|------|------|
| Wire (spec) | `spec/Calc.Wire.fst` | `type request = Push of int \| Peek \| Add \| Sub \| Mul \| Div`; `type response = Ok \| Result of int \| Error`; `be_to_n`/`n_to_be`; `parse_request : bytes{len=5} -> option request`; `serialize_response : response -> bytes{len=5}`; 3 hand-written `serialize_*_bytes` lemmas |
| Wire lemmas (spec) | `spec/Calc.Wire.Lemmas.fst` | Arithmetic-correspondence lemmas for the manual byte-poking impl (`be_to_n_unrefined`, `n_to_be_b{0..3}`, shift/cast lemmas) |
| State machine (spec) | `spec/Calc.Spec.fst` | `calc_stack = list int`; `step : calc_stack -> request -> calc_stack & response`; `run` |
| Ghost log (spec) | `spec/Calc.Log.fst` (624 lines) | `calc_log` record; `parse_requests`/`serialize_responses`/`all_parse`; `log_consistent`; `step_log_{push,peek,add,sub,mul,div}`; `log_single_step`; `log_evolves`; ~15 correspondence lemmas |
| Impl types | `impl/Calc.Impl.Types.fst` | `server_state` (Vec stack + Vec size + monotonic ghost log); `server_exactly` |
| Impl parser | `impl/Calc.Impl.Parser.fst` | `parse_tag`, `parse_push_value` (manual `Vec.vec U8.t` byte reads) |
| Impl handlers | `impl/Calc.Impl.{Push,Peek,Add,Sub,Mul,Div}.fst` | per-op: manual `write_{ok,result,error}_response` byte writes + wire lemmas + ghost-log update |
| Server | `impl/Calc.Server.fst` | `new_server`; `process_request` dispatcher (`parse_tag` then branch on tag) |
| Harness | `test_main.c`, `test.fst`, `Makefile`, `.fst.config.json` | C driver + build |

Buffers are `Pulse.Lib.Vec.vec U8.t` of length 5. 0 admits, ~12s verify.

## Target architecture (what changes)

New `calc.qd.rfc` → generated `Calc.Wire.Generated.*` modules supply the
`request`/`response` **types** and their **spec parser/serializer** +
**Pulse reader/writer/validator/jumper** + **copyful `read_`/`write_`/`size_`**.

- `Calc.Wire` is **deleted entirely** (no adapter/alias module). `Calc.Spec`,
  `Calc.Log`, and the impl `open` the generated modules and use the generated
  `request`/`response`/`opType`/`respType` types and constructors directly. The
  two spec-level leaf wrappers (`parse_request`/`serialize_response`, just
  `LP.parse`/`LP.serialize` over the generated parser/serializer) move into
  `Calc.Log`, their only consumer, beside the stream helpers already there.
- `Calc.Wire.Lemmas` is **deleted** (manual arithmetic no longer needed).
- `Calc.Spec.step` and `Calc.Log.step_log_*` switch from matching the inductive
  to the generated representation (record field / generated constructors).
- `Calc.Impl.Parser` is **deleted**; request parsing uses the generated reader.
- Impl handlers stop poking bytes / calling wire lemmas: they call the generated
  writer (which yields `out == serialize response_serializer resp` for free) and
  keep only the ghost-log update logic.
- `server_state` is unchanged. The public request/response **I/O buffers stay
  `Vec.vec U8.t`** (params of `process_request`); they're bridged to
  `Pulse.Lib.Slice byte` (the generated API's buffer type) once inside
  `process_request`, so the extracted C signature and `test_main.c` are unchanged.
- Build: add a `qd.exe` regen step + a `generated/` EverParse sub-harness
  (LowParse + LowParse.Pulse includes, `--already_cached +Calc.Wire.Generated`),
  verify generated, extract generated to C, bundle with the server C.

---

## The QuackyDucky data format (`calc.qd.rfc`)

`uint32` is a built-in QD type (4-byte big-endian, `U32.t`), so the existing
5-byte wire is expressible exactly. Closed enums (no `/*@open*/`) make the parser
**reject** unknown tags — matching `parse_request` returning `None` for tag ≥ 6.

### Design A — fixed 5-byte struct (RECOMMENDED: preserves wire + C test verbatim)
```
enum { push(0), peek(1), add(2), sub(3), mul(4), div(5), (255) } OpType;
struct { OpType op; uint32 operand; } Request;   /* always 5 bytes */

enum { ok(0), result(1), error(2), (255) } RespType;
struct { RespType tag; uint32 value; } Response;  /* always 5 bytes */
```
- Generated types: `request = { op:opType; operand:U32.t }`, `response = { tag:respType; value:U32.t }` — **records**, not sums. Enum constructors: `Push..Div`, `Ok/Result/Error`.
- Payload fields are deliberately named **distinctly** (`operand` vs `value`) so a
  module may `open` both generated record modules without a `data`-field ambiguity.
- Wire identical to today (Peek/Add/… still carry a 4-byte payload, ignored). `test_main.c` unchanged.
- `step` switches on `req.op`, uses `req.operand` (as `U32.v`) only for `push`.

### Design B — `select` sum (idiomatic, but CHANGES the wire to variable length)
```
struct {
  OpType op;
  select (op) { case push: uint32; default: Empty; } data;
} Request;
```
- Generated `request` is a genuine sum (`Push of U32.t | Peek | …`), closer to today's inductive.
- Wire becomes Push = 5 bytes, others = 1 byte ⇒ **breaks** the fixed-5-byte invariant the log relies on (`len % 5 == 0`) and requires rewriting `test_main.c`/`make_op_request`.

**DECISION (confirmed by user): Design A.** It keeps the byte-level wire, the C
harness, and the log's length invariants intact; the only cost is `step`/`step_log_*`
matching a record field instead of an inductive constructor. Designs B and A2 are
rejected alternatives, kept here only for context (B changes the wire; A2 gives a
fixed-5-byte sum `Push of u32 | Peek of u32 | …` that is faithful but semantically odd).

Location: `calc_sample/calc.qd.rfc`; generate with prefix `Calc.Wire.Generated.`
into `calc_sample/generated/`.

---

## Generated API surface (what `qd.exe -pulse` emits per type)
For each enum/struct (confirmed from `generated/TLS13.Wire.Generated.*`):
- Spec: `<t>_parser` (`LP.parser (strong_parser_kind 5 5 None) request`), `<t>_serializer`, `<t>_bytesize`(+`_eq`,`_eqn` SMTPat).
- Low/Pulse: `<t>_validator`, `<t>_jumper` (`jump_constant_size … 5sz`), `<t>_reader` (`leaf_reader`), `<t>_writer` (`l2r_leaf_writer`), `<t>_leaf_size`.
- Copyful Pulse (operate on `Pulse.Lib.Slice byte`):
  - `read_<t> : copyful_parse vmatch <t>_parser conv` — slice → value.
  - `write_<t> : l2r_safe_writer …` — value → out-slice (sets `perr` if no room, returns bytes written; postcondition gives `slice 0 len == serialize serializer v`).
  - `size_<t>`, `free_<t>`, field `accessor_*`.

These replace **all** of `Calc.Impl.Parser` and the manual `write_*_response`
helpers, and they discharge the "impl output == `serialize_response resp`"
obligation that the hand-written `serialize_*_bytes` lemmas exist to prove.

---

## Phased implementation plan

### Phase 0 — Toolchain sanity (no code change)
- Confirm `tools/everparse/bin/qd.exe` runs and locate the real `fstar.exe`
  (`tools/everparse/opt/FStar/bin/fstar.exe`; note the `out/bin` path in
  `calc_sample/.fst.config.json` is currently a stale symlink target).
- Inspect `generated/generated.Makefile` + top-level `Makefile` `regen/verify/extract-generated`
  rules as the template to copy.

### Phase 1 — Author `calc_sample/calc.qd.rfc` (Design A) and generate
- Write the `.qd.rfc` (enums + Request/Response structs above), using **distinct
  payload field names** (`operand`, `value`) so consumers can `open` both
  generated record modules without a field clash.
- `qd.exe -pulse -prefix "Calc.Wire.Generated." -odir generated calc.qd.rfc`.
- Stand up `calc_sample/generated/` with a `generated.Makefile` analogous to the
  TLS one (LowParse + LowParse.Pulse includes, `--already_cached … +Calc.Wire.Generated`),
  and verify the generated modules in isolation.

### Phase 2 — Delete `Calc.Wire`; use the generated types directly (no adapter)
- **Delete** `spec/Calc.Wire.fst` and `spec/Calc.Wire.Lemmas.fst` (the hand-written
  `request`/`response`, `be_to_n`/`n_to_be`, and all byte-arithmetic lemmas).
- `Calc.Spec`, `Calc.Log`, and the impl modules `open` (or qualified-alias) the
  generated `OpType`/`RespType`/`Request`/`Response` modules and use the generated
  `request`/`response`/`opType`/`respType` types + constructors directly.
- Relocate the two spec-level leaf wrappers into `Calc.Log` (their only consumer):
  `parse_request b = match LP.parse GReq.request_parser b with Some (r,_) -> Some r | _ -> None`
  and `serialize_response r = LP.serialize GResp.response_serializer r`
  (the `len = 5` refinement is free via `LP.serialize_length` + the generated
  `parser_kind 5 5`). These are `GTot` (LowParse `parse`/`serialize` are `GTot`),
  which is fine — they appear only in `Calc.Log`'s `prop`s/lemmas; the *runtime*
  codec is the generated reader/writer used in the impl.
- Note: the calc-specific **stream/log framing** (`parse_requests`,
  `serialize_responses`, `all_parse`) stays hand-written in `Calc.Log`; QuackyDucky
  generates the per-message codec only, not the append-only-log semantics.

### Phase 3 — Update `Calc.Spec`
- `open` the generated `OpType`/`Request`/`RespType`/`Response` modules. `step`
  matches `req.op`; for `push` push `req.operand`. **`calc_stack = list U32.t`**
  (decided with user): native `U32.add`/`sub`/`mul`/`div` replace `(_ % 2^32)`
  (identical computed values), `Peek` returns `{ tag = Result; value = top }`,
  and the spec stack now matches the impl's `Vec U32.t` (so `server_exactly`
  becomes direct equality and the impl sheds int↔U32 arithmetic correspondence).
  Other responses are `{ tag = Ok/Error; value = 0ul }`.

### Phase 4 — Update `Calc.Log` (the framing stays hand-written; only the leaf swaps)
The whole layered-log artifact is calc-specific and **stays hand-written** — only
the per-message leaf underneath it becomes generated. Concretely:

**Stays verbatim (structure unchanged):** the stream framing `parse_requests`
(maximal-valid-prefix decode), `serialize_responses` (concatenation), `all_parse`;
the `calc_log` record, `log_consistent`, `step_log_{push…div}`, `log_single_step`,
`log_evolves`. Inside these, `parse_request`/`serialize_response` become 2-line
`LP.parse request_parser` / `LP.serialize response_serializer` wrappers (moved here
from the deleted `Calc.Wire`); `step_log_*` build generated records/constructors.

**Deleted leaf lemmas** (were only there to justify the old byte-poking impl):
- Response: `lemma_serialize_{ok,error,result}_bytes` (impl↔spec) and the byte-math
  `n_to_be_b0..3`/`lemma_shift_right_byte`/`lemma_uint32_to_uint8_mod`/
  `lemma_n_to_be_correct`/`lemma_write_result_bytes`.
- Request: `be_to_n_unrefined`/`lemma_be_to_n_equiv`/`lemma_parse_push_value_correct`/
  `lemma_u32_no_overflow`/`lemma_u32_arithmetic_correspondence`.
- All live in `Calc.Wire`(`.Lemmas`), removed in Phase 2; the generated reader/writer
  postconditions replace them.

**Kept stream lemmas — codec-AGNOSTIC (carry over unchanged):** `lemma_run_extend`
(state machine), `lemma_serialize_responses_append`/`_single` (pure `Seq.append`),
`lemma_slice_append_prefix` (pure `Seq`), every `lemma_step_log_*_evolves` (trivial),
`lemma_initial_log_consistent`.

**Kept stream lemmas — codec-DEPENDENT (statements unchanged; proofs re-based on
LowParse facts, and several simplify):**
- `lemma_serialize_responses_length` (`== 5*n`): the per-element "= 5 bytes" now
  comes from the generated `parser_kind 5 5` via `LP.serialize_length` (SMTPat).
- `lemma_parse_requests_single`: from constant-size `parse request_parser` on a
  5-byte slice returning `Some (r,5)`/`None`.
- `lemma_parse_requests_append_one`, `lemma_all_parse_append`: re-based on LowParse
  `parse_strong_prefix` (a constant-size parse is unaffected by appended bytes),
  replacing the hand-rolled `slice_append_prefix`/`lemma_slice_first_in_append`.
- The response/request clauses inside `lemma_step_log_*_consistent` keep
  orchestrating the above; their `serialize_response (snd (step …)) =Seq= resp_bytes`
  precondition is now supplied by the impl's generated writer (Phase 5).

**Optional reduction — DEFERRED (decided: skip for now).** One could rebase
`serialize_responses := LP.serialize_list response_serializer` to reuse
`serialize_list_singleton`/`_append` and eliminate the one `Seq.append` induction
in `lemma_serialize_responses_append` (~10 lines; precond holds by `assert_norm`
since `response_parser_kind` is strong + `low=5`). Net is only ~10 lines and one
induction, at the cost of a `LowParse.Spec.List` coupling, and `lemma_serialize_responses_length`
would still be a hand induction. **Keep the self-contained hand-written
`serialize_responses` and its three lemmas** (clearer for a teaching sample); the
request side cannot fold onto `parse_list` anyway (all-or-nothing vs. maximal-valid-prefix).

### Phase 5 — Replace impl parsing/serialization with the generated reader/writer
- Delete `Calc.Impl.Parser`. Keep the public I/O buffers as `Vec.vec U8.t` (so the
  extracted `process_request(srv, uint8_t*, uint8_t*)` and `test_main.c` are
  unchanged); bridge **once** in `Calc.Server.process_request` with
  `S.from_array (V.vec_to_array buf) 5sz` … `S.to_array` (the `TLS13.Impl.Parser`
  pattern; `vec_to_array`/`from_array` are zero-copy, identity on the byte `Seq`).
- In `process_request`: build the request slice, run `request_validator` (runtime
  tag check, replacing `lemma_valid_tag`/`parse_tag`), then `read_request` to get
  `req`; build the response slice and dispatch on `req.op`.
- Make handlers **slice-native**: each takes the parsed `req` value + the response
  `slice byte`, replaces `write_{ok,result,error}_response` with `write_response`
  (whose postcondition yields `out_bytes == serialize response_serializer resp`,
  feeding the log's `serialize_response` directly), drops all wire-lemma calls, and
  keeps the ghost-log update (`MR.update`, `lemma_step_log_*_consistent/_evolves`).

### Phase 6 — Update `Calc.Server` dispatcher
- Parse once with `read_request`; branch on the parsed `req.op` (Design A) /
  constructor (Design B) to the handlers; serialize with the generated writer.

### Phase 7 — Build, extraction, and C test
- `calc_sample/Makefile`: add `regen-calc-wire` (qd), include `generated/` +
  LowParse/LowParse.Pulse, `--already_cached +Calc.Wire.Generated`; fix the
  `fstar.exe` path; update `.fst.config.json` similarly.
- Extract generated codec to C (KaRaMeL, as `extract-generated` does for TLS) and
  bundle with `Calc_Server` C; keep `test_main.c` (Design A) and rerun `make test-c`.

### Phase 8 — Verify & clean up
- `make verify` (0 admits), `make test-c` green.
- Remove dead files/backups (`*.bak`, `*.monolithic`, `Calc.Wire.Lemmas.fst`,
  `Calc.Impl.Parser.fst`); update `CALC_DESIGN_AND_IMPL.md`.

---

## Verification tooling
Use the **proof-copilot** plugin for the proof-heavy phases (4 & 5): the
`fstarmcp`/`fstarverifier` skills for incremental typechecking and error
interpretation, `proofdebugging` for failures, and the `proof-copilot:fstar-coder`
agent for porting the log lemmas and handler proofs.

## Key risks / decision points
1. **Wire compatibility** — DECIDED: **Design A** (keep exact 5-byte wire, record
   type, `test_main.c` unchanged).
2. **Spec type shape**: generated records `{op;operand}` / `{tag;value}` (A) force
   `step`/`step_log_*` to read a field instead of pattern-matching a nullary
   constructor; payload fields are named distinctly so consumers can `open` both
   record modules without a field-name clash (else use qualified module aliases).
3. **Buffers** — DECIDED: keep public I/O buffers as `Vec.vec U8.t` (extracts to
   `uint8_t*`, so the `process_request(srv, uint8_t*, uint8_t*)` C signature and
   `test_main.c` are unchanged); bridge to `Pulse.Lib.Slice byte` **once** inside
   `Calc.Server.process_request` via `S.from_array (V.vec_to_array buf) 5sz` …
   `S.to_array` (the `TLS13.Impl.Parser` pattern), and make handlers slice-native.
4. **Log re-proofs**: the kept codec-dependent lemmas hinge on three LowParse facts
   being surfaced — `serialize_length` (constant `parser_kind 5 5` ⇒ 5-byte leaf,
   for `% 5` invariants + `serialize_responses` length), constant-size `parse`
   on a 5-byte slice (for `parse_requests_single`), and `parse_strong_prefix`
   (for the `append_one`/`all_parse_append` lemmas).
5. **C bundling**: the generated LowParse-based C must link cleanly with the
   server C (KaRaMeL bundle/-no-prefix flags), as in the TLS `extract-generated`.

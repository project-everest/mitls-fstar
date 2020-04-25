module TLS.Tracing

/// A module to support printf-style debugging, guarded behind debug flags,
/// compatible with C. This mostly reuses the machinery from LowStar.Printf,
/// adding a couple convenience helpers to deal with reprs and bytes (not Low*!)
/// as we lower the code of miTLS.

open FStar.HyperStack.ST

module B = LowStar.Buffer
module C = LowStar.ConstBuffer
module R = LowParse.Repr
module Printf = LowStar.Printf

/// Low-level machinery (useless for clients)
/// -----------------------------------------

#set-options "--max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let print_frags_t acc =
  (_: unit) ->
  Stack unit
    (requires fun h0 -> Printf.(live_frags h0 acc))
    (ensures fun h0 _ h1 -> h0 == h1)

inline_for_extraction noextract
let print_frags (acc: Printf.(list frag_t)): print_frags_t acc =
  fun _ ->
    Printf.print_frags acc

inline_for_extraction noextract
let trace_frags (prefix: string) (acc: Printf.(list frag_t)): Stack unit
  (requires fun h0 -> Printf.(live_frags h0 acc))
  (ensures fun h0 _ h1 -> h0 == h1)
=
  if DebugFlags.debug_HS then begin
    Printf.print_string (normalize_term (FStar.Printf.sprintf "%s |" prefix));
    (normalize_term #(print_frags_t acc) (print_frags acc)) ();
    Printf.print_string "\n"
  end else
    ()

#push-options "--ifuel 1 --fuel 2"
noextract inline_for_extraction
let trace' (prefix: string) (s: Printf.format_string): Printf.(interpret_format_string s) =
  normalize_term
  Printf.(match parse_format_string s with
    | Some frags -> aux frags [] (trace_frags prefix))
#pop-options

/// Client-facing API
/// -----------------

/// Make a tracer for a given module, by providing a prefix that will be
/// prepended to any output. Note that a tracer generated in this fashion also
/// takes care of suffixing any output with a newline.
inline_for_extraction noextract
let mk_trace prefix =
  Printf.(intro_normal_f #format_string interpret_format_string (trace' prefix))

inline_for_extraction noextract
let mbuffer_type_of_repr_pos #t #b (r: R.repr_pos t b) =
  //C.(Printf.lmbuffer UInt8.t (qbuf_pre (as_qbuf b.R.base)) (qbuf_pre (as_qbuf b.R.base)) r.R.length)
  C.(B.mbuffer UInt8.t (qbuf_pre (as_qbuf b.R.base)) (qbuf_pre (as_qbuf b.R.base)))

/// One often needs to convert a repr type to a raw buffer suitable for passing
/// to the printf facility.
inline_for_extraction noextract
let mbuf_of_repr #t #b (r: R.repr_pos t b): Stack (mbuffer_type_of_repr_pos r)
  (requires fun h0 ->
    R.valid_repr_pos r h0)
  (ensures fun h0 b h1 ->
    h0 == h1 /\
    B.live h1 b /\
    B.len b == r.R.length)
=
  let R.Ptr b _ _ _ = R.as_ptr r in
  LowStar.ConstBuffer.cast b

/// As a temporary escape hatch, if one needs to print bytes, they can use "%a"
/// followed by ``print_bytes`` along with the bytes to print.
inline_for_extraction noextract
let print_bytes (b: FStar.Bytes.bytes): Printf.StTrivial unit =
  Printf.print_string (FStar.Bytes.print_bytes b)

module LowParse.Low.Bytes
include LowParse.Spec.Bytes
include LowParse.Low.Combinators
include LowParse.Low.VLData
include LowParse.Low.Int

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module B = LowStar.Buffer
module BY = LowParse.Bytes32
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8

inline_for_extraction
let validate_flbytes
  [| validator_cls |]
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz /\ sz <= U32.v validator_max_length } )
: Tot (validator (parse_flbytes sz))
= validate_total_constant_size (parse_flbytes sz) sz32 ()

inline_for_extraction
let jump_flbytes
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (jumper (parse_flbytes sz))
= jump_constant_size (parse_flbytes sz) sz32 ()

let valid_flbytes_intro
  (h: HS.mem)
  (sz: nat { sz < 4294967296 } )
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (U32.v pos + sz <= U32.v s.len /\ live_slice h s))
  (ensures (
    valid_content_pos (parse_flbytes sz) h s pos (BY.hide (B.as_seq h (B.gsub s.base pos (U32.uint_to_t sz)))) (pos `U32.add` U32.uint_to_t sz)
  ))
= valid_facts (parse_flbytes sz) h s pos

let valid_pos_flbytes_elim
  (h: HS.mem)
  (sz: nat { sz < 4294967296 } )
  (s: slice)
  (pos pos' : U32.t)
: Lemma
  (requires (valid_pos (parse_flbytes sz) h s pos pos'))
  (ensures (U32.v pos + sz == U32.v pos'))
  [SMTPat (valid_pos (parse_flbytes sz) h s pos pos')]
= valid_facts (parse_flbytes sz) h s pos

let clens_flbytes_slice
  (sz: nat)
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (clens #(BY.lbytes sz) (fun _ -> True) (BY.lbytes (U32.v to - U32.v from)))
= {
  clens_get = (fun (x: BY.lbytes sz) -> (BY.slice x from to <: BY.lbytes (U32.v to - U32.v from)));
}

let gaccessor_flbytes_slice
  (sz: nat { sz < 4294967296 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (gaccessor (parse_flbytes sz) (parse_flbytes (U32.v to - U32.v from)) (clens_flbytes_slice sz from to))
= fun (input: bytes) -> (
  begin
    if Seq.length input < sz
    then (0, 0) // dummy
    else (U32.v from, U32.v to - U32.v from)
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_flbytes sz) (parse_flbytes (U32.v to - U32.v from)) (clens_flbytes_slice sz from to) input res )))

inline_for_extraction
let accessor_flbytes_slice
  (sz: nat { sz < 4294967296 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (accessor (gaccessor_flbytes_slice sz from to))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_flbytes_slice sz from to) input pos in
  pos `U32.add` from

let clens_flbytes_get
  (sz: nat)
  (i: U32.t { U32.v i < sz } )
: Tot (clens #(BY.lbytes sz) (fun _ -> True) byte)
= {
  clens_get = (fun (x: BY.lbytes sz) -> (BY.get x i <: byte));
}

let gaccessor_flbytes_get
  (sz: nat { sz < 4294967296 } )
  (i: U32.t { U32.v i < sz } )
: Tot (gaccessor (parse_flbytes sz) (parse_u8) (clens_flbytes_get sz i))
= fun (input: bytes) -> (
  begin
    let res =
      if Seq.length input <= U32.v i
      then (0, 0) // dummy
      else (U32.v i, 1)
    in
    let g () : Lemma
      (requires (gaccessor_pre (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input))
      (ensures (gaccessor_post (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input res))
    = assert (res == (U32.v i, 1));
      parse_u8_spec (Seq.slice input (U32.v i) (U32.v i + 1))
    in
    Classical.move_requires g ();
    res
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input res )))

inline_for_extraction
let accessor_flbytes_get
  (sz: nat { sz < 4294967296 } )
  (i: U32.t { U32.v i < sz } )
: Tot (accessor (gaccessor_flbytes_get sz i))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_flbytes_get sz i) input pos in
  pos `U32.add` i

(* Temporary: flbytes as leaf values *)

inline_for_extraction
let serialize32_flbytes
  (sz32: U32.t)
: Tot (serializer32 (serialize_flbytes (U32.v sz32)))
= fun (src: BY.lbytes (U32.v sz32)) (dst: buffer8) ->
  begin if sz32 <> 0ul
  then
    let dst' = B.sub dst 0ul sz32 in
    BY.store_bytes src dst'
  end;
  sz32

inline_for_extraction
let write_flbytes
  (sz32: U32.t)
: Tot (leaf_writer_strong (serialize_flbytes (U32.v sz32)))
= leaf_writer_strong_of_serializer32 (serialize32_flbytes sz32) ()

inline_for_extraction
let write_flbytes_weak
  (sz32: U32.t { U32.v sz32 < 4294967295 } )  // need to return that value if output buffer is too small
: Tot (leaf_writer_weak (serialize_flbytes (U32.v sz32)))
= leaf_writer_weak_of_strong_constant_size (write_flbytes sz32) sz32 ()

inline_for_extraction
let read_flbytes
  (sz32: U32.t)
: Tot (leaf_reader (parse_flbytes (U32.v sz32)))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_flbytes (U32.v sz32)) h input pos in
  BY.of_buffer sz32 (B.sub input.base pos sz32)


inline_for_extraction
let validate_all_bytes
  [| validator_cls |]
  ()
: Tot (validator parse_all_bytes)
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts parse_all_bytes h input pos in
  input.len

inline_for_extraction
let validate_bounded_vlbytes
  [| validator_cls |]
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max <= U32.v validator_max_length  } )
: Tot (validator (parse_bounded_vlbytes min max))
= validate_synth
    (validate_bounded_vldata_strong min max serialize_all_bytes (validate_all_bytes ()) ())
    (synth_bounded_vlbytes min max)
    ()

inline_for_extraction
let jump_all_bytes
  ()
: Tot (jumper parse_all_bytes)
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts parse_all_bytes h input pos in
  input.len

inline_for_extraction
let jump_bounded_vlbytes
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296  } )
: Tot (jumper (parse_bounded_vlbytes min max))
= jump_synth
    (jump_bounded_vldata_strong min max serialize_all_bytes ())
    (synth_bounded_vlbytes min max)
    ()

let valid_exact_all_bytes_elim
  (h: HS.mem)
  (input: slice)
  (pos pos' : U32.t)
: Lemma
  (requires (valid_exact parse_all_bytes h input pos pos'))
  (ensures (
    let x = contents_exact parse_all_bytes h input pos pos' in
    let length = U32.v pos' - U32.v pos in
    BY.length x == length /\
    valid_content_pos (parse_flbytes length) h input pos x pos'
  ))
= valid_exact_equiv parse_all_bytes h input pos pos' ;
  contents_exact_eq parse_all_bytes h input pos pos' ;
  let length = U32.v pos' - U32.v pos in
  valid_facts (parse_flbytes length) h input pos ;
  assert (no_lookahead_on (parse_flbytes length) (B.as_seq h (B.gsub input.base pos (pos' `U32.sub` pos))) (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos))));
  assert (injective_postcond (parse_flbytes length) (B.as_seq h (B.gsub input.base pos (pos' `U32.sub` pos))) (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos))))

#push-options "--z3rlimit 32"

let valid_bounded_vlbytes_elim
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    valid (parse_bounded_vlbytes min max) h input pos
  ))
  (ensures (
    let sz = log256' max in
    valid (parse_bounded_integer sz) h input pos /\ (
    let len_payload = contents (parse_bounded_integer sz) h input pos in
    min <= U32.v len_payload /\ U32.v len_payload <= max /\
    sz + U32.v len_payload == content_length (parse_bounded_vlbytes min max) h input pos /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    let x = contents (parse_bounded_vlbytes min max) h input pos in
    BY.len x == len_payload /\
    valid_pos (parse_bounded_vlbytes min max) h input pos (pos_payload `U32.add` len_payload) /\
    valid_content_pos (parse_flbytes (U32.v len_payload)) h input pos_payload x (pos_payload `U32.add` len_payload)
  ))))
= valid_synth h (parse_bounded_vlbytes' min max) (synth_bounded_vlbytes min max) input pos;
  valid_bounded_vldata_strong_elim h min max serialize_all_bytes input pos;
  let sz = log256' max in
  let len_payload = contents (parse_bounded_integer sz) h input pos in
  let pos_payload = pos `U32.add` U32.uint_to_t sz in
  valid_exact_all_bytes_elim h input pos_payload (pos_payload `U32.add` len_payload);
  ()

#pop-options

inline_for_extraction
let bounded_vlbytes_payload_length
  (min: nat) // must be a constant
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h -> valid (parse_bounded_vlbytes min max) h input pos))
  (ensures (fun h len h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + log256' max + U32.v len <= U32.v input.len /\ (
    let x = contents (parse_bounded_vlbytes min max) h input pos in
    BY.len x == len /\
    valid_content_pos (parse_flbytes (U32.v len)) h input (pos `U32.add` U32.uint_to_t (log256' max)) x (get_valid_pos (parse_bounded_vlbytes min max) h input pos)
  )))
= let h = HST.get () in
  [@inline_let] let _ = valid_bounded_vlbytes_elim h min max input pos in
  read_bounded_integer (log256' max) input pos

let clens_vlbytes_cond
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: nat)
  (x: parse_bounded_vlbytes_t min max)
: GTot Type0
= BY.length x == length

let clens_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: nat)
: Tot (clens (clens_vlbytes_cond min max length) (BY.lbytes length))
= {
  clens_get = (fun (x: parse_bounded_vlbytes_t min max) -> (x <: Ghost (BY.lbytes length) (requires (clens_vlbytes_cond min max length x)) (ensures (fun _ -> True))));
}


#push-options "--z3rlimit 16 --max_fuel 2 --initial_fuel 2 --max_ifuel 6 --initial_ifuel 6"

let gaccessor_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: nat { length < 4294967296 } )
: Tot (gaccessor (parse_bounded_vlbytes min max) (parse_flbytes length) (clens_vlbytes min max length))
= fun (input: bytes) -> (begin
    let res = if Seq.length input = log256' max + length
    then (log256' max, length)
    else (0, 0)
    in
    let g () : Lemma
      (requires (gaccessor_pre (parse_bounded_vlbytes min max) (parse_flbytes length) (clens_vlbytes min max length) input))
      (ensures (gaccessor_post (parse_bounded_vlbytes min max) (parse_flbytes length) (clens_vlbytes min max length) input res))
    = parse_bounded_vlbytes_eq min max input
    in
    Classical.move_requires g ();
    res
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_bounded_vlbytes min max) (parse_flbytes length) (clens_vlbytes min max length) input res)))

#pop-options

#push-options "--z3rlimit 32 --max_fuel 2 --initial_fuel 2 --max_ifuel 6 --initial_ifuel 6"

inline_for_extraction
let accessor_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (length: U32.t)
: Tot (accessor (gaccessor_vlbytes min max (U32.v length)))
= fun sl pos ->
  let h = HST.get () in
  [@inline_let]
  let _ =
    slice_access_eq h (gaccessor_vlbytes min max (U32.v length)) sl pos;
    valid_bounded_vlbytes_elim h min max sl pos;
    parse_bounded_vlbytes_eq min max (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)))
  in
  pos `U32.add` U32.uint_to_t (log256' max)

#pop-options

#push-options "--z3rlimit 64 --max_fuel 2 --initial_fuel 2 --max_ifuel 6 --initial_ifuel 6"

let valid_bounded_vlbytes_intro
  (h: HS.mem)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
  (len: U32.t)
: Lemma
  (requires (
    let sz = log256' max in
    min <= U32.v len /\ U32.v len <= max /\
    valid (parse_bounded_integer sz) h input pos /\
    contents (parse_bounded_integer sz) h input pos == len /\
    U32.v pos + sz <= 4294967295 /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid (parse_flbytes (U32.v len)) h input pos_payload
  )))
  (ensures (
    let sz = log256' max in  
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid_content_pos (parse_bounded_vlbytes min max) h input pos (contents (parse_flbytes (U32.v len)) h input pos_payload) (pos_payload `U32.add` len)
  ))
= valid_facts (parse_bounded_vlbytes min max) h input pos;
  parse_bounded_vlbytes_eq min max (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)));
  let sz = log256' max in
  valid_facts (parse_bounded_integer sz) h input pos;
  valid_facts (parse_flbytes (U32.v len)) h input (pos `U32.add` U32.uint_to_t sz)

#pop-options

inline_for_extraction
let finalize_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (input: slice)
  (pos: U32.t)
  (len: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    let sz = log256' max in
    min <= U32.v len /\ U32.v len <= max /\
    U32.v pos + sz <= 4294967295 /\ (
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    valid (parse_flbytes (U32.v len)) h input pos_payload
  )))
  (ensures (fun h pos' h' ->
    let sz = log256' max in  
    let pos_payload = pos `U32.add` U32.uint_to_t sz in
    B.modifies (loc_slice_from_to input pos pos_payload) h h' /\
    valid_content_pos (parse_bounded_vlbytes min max) h' input pos (contents (parse_flbytes (U32.v len)) h input pos_payload) pos' /\
    U32.v pos' == U32.v pos_payload + U32.v len
  ))
= [@inline_let]
  let sz = log256' max in
  let _ = write_bounded_integer sz len input pos in
  let h = HST.get () in
  [@inline_let] let _ = valid_bounded_vlbytes_intro h min max input pos len in
  (pos `U32.add` U32.uint_to_t sz) `U32.add` len


(*
let h = HST.get () in
  [@inline_let] let _ = valid_facts (parse_bounded_vlbytes min max) h input pos in
  [@inline_let]
  let sz = log256' max in
  [@inline_let] let _ = valid_facts (parse_bounded_integer sz) h input pos in
  let len = read_bounded_integer sz input pos in
  [@inline_let] let pos' = pos `U32.add` U32.uint_to_t (log256' max) in
  [@inline_let] let _ = valid_facts (parse_flbytes (U32.v len)) h input pos' in
  [@inline_let] let _ = no_lookahead_on (parse_flbytes (U32.v len)) (B.as_seq h (B.gsub input.base pos' len)) (B.as_seq h (B.gsub input.base pos' (input.len `U32.sub` pos'))) in
  [@inline_let] let _ = injective_postcond (parse_flbytes (U32.v len)) (B.as_seq h (B.gsub input.base pos' len)) (B.as_seq h (B.gsub input.base pos' (input.len `U32.sub` pos'))) in
  len


(*

module M = LowStar.Modifies

inline_for_extraction
let read_byte
  (sz: nat { sz < 4294967296 } )
  (i: U32.t)
  (input: buffer8)
: HST.Stack byte
  (requires (fun h -> B.live h input /\ Some? (parse (parse_flbytes sz) (B.as_seq h input)) /\ U32.v i < sz))
  (ensures (fun h res h' ->
    h' == h /\
    U32.v i < B.length input /\ (
    let (Some (v, consumed)) = parse (parse_flbytes sz) (B.as_seq h input) in
    (consumed <: nat) == sz /\
    res == BY.get v i
  )))
= B.index input i

#set-options "--z3rlimit 16"

inline_for_extraction
let slice_bytes
  (sz: nat { sz < 4294967296 } )
  (i: U32.t)
  (sz' : U32.t { U32.v i + U32.v sz' <= sz } )
: Tot (accessor (parse_flbytes sz) (parse_flbytes (U32.v sz')) (fun x y -> y == BY.slice x i (U32.add i sz')))
= fun input ->
  B.sub input i sz'

inline_for_extraction
let validate32_all_bytes
: validator32 (parse_all_bytes)
= fun input len ->
    let h = HST.get () in
    0l

inline_for_extraction
let validate32_bounded_vlbytes'
  (min: nat)
  (min32: U32.t)
  (max: nat { min <= max /\ max > 0 /\ max < 2147483648 })
  (max32: U32.t)
  (sz32: I32.t)
  (u: squash (
    U32.v min32 == min /\ U32.v max32 == max /\
    I32.v sz32 == log256' max
  ))
: Tot (validator32 (parse_bounded_vlbytes' min max))
= validate32_bounded_vldata_strong min min32 max max32 (serialize_all_bytes) validate32_all_bytes sz32 ()

inline_for_extraction
let validate32_bounded_vlbytes
  (min: nat)
  (min32: U32.t)
  (max: nat { min <= max /\ max > 0 /\ max < 2147483648 } )
  (max32: U32.t)
  (sz32: I32.t)
  (u: squash (
    U32.v min32 == min /\ U32.v max32 == max /\
    I32.v sz32 == log256' max
  ))
: Tot (validator32 (parse_bounded_vlbytes min max))
= validate32_synth
    (validate32_bounded_vlbytes' min min32 max max32 sz32 ())
    (synth_bounded_vlbytes min max)
    ()

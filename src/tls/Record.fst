module Record

module HS = FStar.HyperStack

(* (optional) encryption and processing of the outer (untrusted) record format *)

open FStar.Seq
open FStar.Bytes
open FStar.Error
open FStar.UInt32

open Mem
open TLSError
open TLSInfo
open TLSConstants
open Range
open Content

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

// Consider merging some of this module with Content?

(* A flag for runtime debugging of record data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
private val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
private let discard _ = ()
private let print s = discard (IO.debug_print_string ("REC| "^s^"\n"))
private unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
private unfold let trace = if DebugFlags.debug_Record then print else (fun _ -> ())


private let p_of_f (f:bytes): (p:FStar.Bytes.bytes{ FStar.Bytes.length p = FStar.Bytes.length f }) = f
private let f_of_p (p:FStar.Bytes.bytes): (f:bytes{ FStar.Bytes.length p = FStar.Bytes.length f }) = p
private let ctBytes x = f_of_p (ctBytes x)
private let parseCT (x: lbytes 1) = parseCT (p_of_f x)
private let versionBytes x = f_of_p (versionBytes x) 
private let parseVersion (x: lbytes 2) = parseVersion (p_of_f x)


// ------------------------outer packet format -------------------------------

// the "outer" header has the same format for all versions of TLS
// but TLS 1.3 fakes its content type and protocol version.

private type header = b:lbytes 5 // for all TLS versions

private let fake = ctBytes Application_data @| versionBytes TLS_1p2

// this is the outer packet; the *caller* should switch from 1.3 to 1.0 whenever data is encrypted.
#reset-options "--admit_smt_queries true"
private inline_for_extraction 
let makeHeader ct plain ver (length:nat {repr_bytes length <= 2}): header =
  let ct_ver = 
    if TLS_1p3? ver then if plain then 
      (ctBytes ct @| versionBytes TLS_1p2) 
    else 
      fake 
    else 
      (ctBytes ct @| versionBytes ver) in
  ct_ver @| bytes_of_int 2 length 
#reset-options

// used only for testing
let makePacket ct plain ver (data: (b:bytes { repr_bytes (length b) <= 2})) =
  makeHeader ct plain ver (length data) @| data

let sendPacket tcp ct plain ver (data: (b:bytes { repr_bytes (length b) <= 2})) =
  // still some margin for progress to avoid intermediate copies
  let header = makeHeader ct plain ver (length data) in 
  trace ("record headers: "^print_bytes header);
  let res = Transport.send tcp (BufferBytes.from_bytes header) 5ul in
  if res = 5l then 
    let res = Transport.send tcp (BufferBytes.from_bytes data) (len data) in
    if Int32.v res = length data
    then Correct()
    else Error(Printf.sprintf "Transport.send returned %l" res)
  else   Error(Printf.sprintf "Transport.send returned %l" res)

private type parsed_header = result (contentType
                           * protocolVersion
                           * l:nat { l <= max_TLSCiphertext_fragment_length})
private val parseHeader: h5:header -> Tot parsed_header

let parseHeader (h5:header) =
    let (ct1,b4)   = FStar.Bytes.split h5 1ul in
    let (pv2,len2) = FStar.Bytes.split b4 2ul in
    match parseCT ct1 with
    | Error z -> Error z
    | Correct ct ->
      match parseVersion pv2 with
      | Error z -> Error z
      | Correct (Unknown_protocolVersion _) ->
        Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Parsed unknown protocol version")
      | Correct pv ->
          let len = int_of_bytes len2 in
          if len <= 0 || len > max_TLSCiphertext_fragment_length
          then Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Wrong fragment length")
          else correct(ct,pv,len)


(*** networking (floating) ***)

// in the spirit of TLS 1.3, we ignore the outer protocol version (see appendix C):
// our server never treats the ClientHello's record pv as its minimum supported pv;
// our client never checks the consistency of the server's record pv.
// (see earlier versions for the checks we used to perform)

// connectlon-local input state
type partial =
  | Header
  | Body: ct: contentType -> pv: protocolVersion -> partial

private let maxlen = UInt32.uint_to_t (5 + max_TLSCiphertext_fragment_length)
private type input_buffer = b: Buffer.buffer UInt8.t {Buffer.length b = v maxlen}

//TODO index by region
noeq abstract type input_state = | InputState:
  pos: ref (len:UInt32.t {len <=^ maxlen}) ->
  b: input_buffer {Buffer.frameOf b = Mem.frameOf pos} -> input_state

// type input_state = {
//   pos: ref (len:UInt32.t {len <=^ maxlen});
//   b: input_buffer }

private let parseHeaderBuffer (b: Buffer.buffer UInt8.t {Buffer.length b = 5}) : ST parsed_header
  (requires (fun h0 -> Buffer.live h0 b))
  (ensures (fun h0 hdr h1 -> modifies_none h0 h1 /\ hdr = parseHeader (Bytes.hide (Buffer.as_seq h0 b))))
=
  // some margin for progress
  parseHeader (BufferBytes.to_bytes 5 b)

abstract let input_inv h0 (s: input_state) = 
  Mem.contains h0 s.pos /\
  Buffer.live h0 s.b /\
  ( let pv = UInt32.v (sel h0 s.pos) in 
    5 <= pv ==> (
    match parseHeader (Bytes.hide (Buffer.as_seq h0 (Buffer.sub s.b 0ul 5ul))) with
    | Correct (_,_,length) -> pv <= 5 + length
    | _ -> False))

private val waiting_len:  s: input_state -> ST UInt32.t
  (requires fun h0 -> input_inv h0 s)
  (ensures fun h0 len h1 -> 
    modifies_none h0 h1 /\ 
    ( let pv = UInt32.v (sel h0 s.pos) in 
      let l = UInt32.v len in 
      ( pv + l = 5 \/ 
        ( match parseHeader (Bytes.hide (Buffer.as_seq h0 (Buffer.sub s.b 0ul 5ul))) with
        | Correct (_,_,length) -> pv + l == 5 + length 
        | _ -> False))))

let waiting_len s =
  if !s.pos <^ 5ul
  then 5ul -^ !s.pos
  else
    match parseHeaderBuffer (Buffer.sub s.b 0ul 5ul) with
    | Correct (_,_,length) -> 5ul +^ uint_to_t length -^ !s.pos
      //let pv = UInt32.v !s.pos in 
      //assert(length <= max_TLSCiphertext_fragment_length);
      //assert(pv <= 5 + length);
      //assert(FStar.UInt.size(length + 5) 32);
      //assert(FStar.UInt.size(length + 5 - pv) 32);
     // other case is statically excluded

val alloc_input_state: r:_ -> ST input_state 
  (requires (fun h0 -> is_eternal_region r))
  (ensures (fun h0 s h1 ->
    //TODO modifies? h0 h1 /\ 
    Mem.frameOf s.pos = r /\ 
    input_inv h1 s))
let alloc_input_state r = 
  let pos = ralloc r 0ul in 
  let b = Buffer.rcreate r 0uy maxlen in
  InputState pos b

type read_result =
  | ReadError of TLSError.error
  | ReadWouldBlock
  | Received:
      ct:contentType ->
      pv:protocolVersion ->
      b:bytes {length b <= max_TLSCiphertext_fragment_length} -> read_result

val read: Transport.t -> s: input_state -> ST read_result
  (requires fun h0 -> input_inv h0 s)
  (ensures fun h0 _ h1 ->
    let r = Mem.frameOf s.pos in
    // Mem.modifies_one r h0 h1 /\
    input_inv h1 s
  )
// Refine by adding this?
//    Buffer.modifies_bufs_and_refs
//      (Buffer.only s.b)
//      (Set.singleton (Heap.addr_of (HS.as_ref s.pos)))
//      h0 h1)

//#set-options "--detail_errors"
let rec read tcp s =
  let h0 = ST.get() in 
  assert(input_inv h0 s);
  let waiting = waiting_len s in
  let p0 = !s.pos in
  let dest = Buffer.sub s.b p0 waiting in
  let res = Transport.recv tcp dest waiting in
  let h1 = ST.get() in 
  let p1 = !s.pos in 
  assume(p0 = p1);
  assume(input_inv h1 s);// TODO sub-buffer framing, with 2 cases
  if res = -1l
  then ReadError (AD_internal_error, "Transport.recv")
  else if res = 0l
  then (trace "WouldBlock"; ReadWouldBlock)
  else (
    let received = Int.Cast.int32_to_uint32 res in
    assert(received <=^ waiting);
    assert(UInt32.v p0 + UInt32.v waiting <= UInt32.v maxlen);
    s.pos := p0 +^ received;
    if received <^ waiting
      then
        // partial read
        // should probably ReadWouldBlock instead when non-blocking
        read tcp s
      else
        if !s.pos = 5ul // we have buffered the record header
        then (
          match parseHeaderBuffer s.b with
          | Error e -> ReadError e
          | Correct(ct,pv,length) ->
            if length = 0 then
              // corner case, possibly excluded by the RFC
              ( s.pos := 0ul; Received ct pv empty_bytes )
            else read tcp s )
        else
          // we have buffered the whole record
          match parseHeaderBuffer s.b with
          | Correct(ct,pv,length) -> (
            let len = UInt32.uint_to_t length in
            let b = Buffer.sub s.b 5ul len in
            let payload = BufferBytes.to_bytes length b in
            s.pos := 0ul;
            Received ct pv payload ))

//18-01-24 recheck async I
//    if length fresh = 0 then
//      ReadError(AD_internal_error,"TCP close") // otherwise we loop...

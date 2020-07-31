module Record

(* (optional) encryption and processing of the outer, untrusted record format *)

open FStar.Seq
open FStar.Bytes
open FStar.UInt32

open Mem
open TLS.Result
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
private let discard (_: bool) : ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
= ()
private let print s = discard (IO.debug_print_string ("REC| "^s^"\n"))
private unfold let trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
= if DebugFlags.debug_Record then print else (fun _ -> ())


private let p_of_f (f:bytes): (p:FStar.Bytes.bytes{ FStar.Bytes.length p = FStar.Bytes.length f }) = f
private let f_of_p (p:FStar.Bytes.bytes): (f:bytes{ FStar.Bytes.length p = FStar.Bytes.length f }) = p
private let ctBytes x = f_of_p (ctBytes x)
private let parseCT (x: lbytes 1) = parseCT (p_of_f x)
private let versionBytes x = f_of_p (versionBytes x) 
private let parseVersion (x: lbytes 2) = parseVersion (p_of_f x)


// ------------------------outer packet format -------------------------------

// the "outer" header has the same format for all versions of TLS
// but TLS 1.3 fakes its content type and protocol version.

private let headerLen = 5ul 
private (* noextract *) let headerLength = v headerLen 
private type header = b:lbytes headerLength // for all TLS versions

#reset-options "--using_facts_from '* -LowParse.Spec.Base'"

private let fake = ctBytes Application_data @| versionBytes TLS_1p2

// this is the outer packet; to comply with legacy version signalling,
// the *caller* should switch from 1.3 to 1.0 whenever data is
// encrypted.
#set-options "--z3rlimit 10" //18-04-20 now required; why?
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

// used only for testing
let makePacket ct plain ver (data: (b:bytes { repr_bytes (length b) <= 2})) =
  makeHeader ct plain ver (length data) @| data

let sendPacket tcp ct plain ver (data: (b:bytes { repr_bytes (length b) <= 2})) =
  // still some margin for progress to avoid intermediate copies
  let header = makeHeader ct plain ver (length data) in 
  trace ("record headers: "^print_bytes header);
  let res = Transport.send tcp (BufferBytes.from_bytes header) headerLen in
  if res = Int.Cast.uint32_to_int32 headerLen then 
    let res = Transport.send tcp (BufferBytes.from_bytes data) (len data) in
    if Int32.v res = length data
    then Correct()
    else fatal Internal_error (Printf.sprintf "Transport.send(header) returned %l" res)
  else   fatal Internal_error (Printf.sprintf "Transport.send(payload) returned %l" res)

private type parsed_header = result (contentType
                           * protocolVersion
                           * l:nat { l <= max_TLSCiphertext_fragment_length})
// private // QUIC.fst needs access to this definition
let parseHeader (h5:header) : Tot parsed_header =
    let (ct1,b4)   = FStar.Bytes.split h5 1ul in
    let (pv2,len2) = FStar.Bytes.split b4 2ul in
    match parseCT ct1 with
    | Error z -> Error z
    | Correct ct ->
      match parseVersion pv2 with
      | Error z -> Error z
      | Correct (Unknown_protocolVersion _) ->
        fatal Decode_error (perror __SOURCE_FILE__ __LINE__ "Parsed unknown protocol version")
      | Correct pv ->
          let len = int_of_bytes len2 in
          if len <= 0 || len > max_TLSCiphertext_fragment_length
          then fatal Illegal_parameter (perror __SOURCE_FILE__ __LINE__ "Wrong fragment length")
          else correct(ct,pv,len)


(*** networking ***)

// in the spirit of TLS 1.3, we ignore the outer protocol version (see appendix C):
// our server never treats the ClientHello's record pv as its minimum supported pv;
// our client never checks the consistency of the server's record pv.
// (see earlier versions for the checks we used to perform)

// connectlon-local input state
type partial =
  | Header
  | Body: ct: contentType -> pv: protocolVersion -> partial

private let maxlen = headerLen +^ UInt32.uint_to_t max_TLSCiphertext_fragment_length
private type input_buffer = b: Buffer.buffer UInt8.t {Buffer.length b = v maxlen}

//TODO index by region. // number of bytes already buffered
val input_state : Type0

val input_state_pos
  (i: input_state)
: Tot (ref (len:UInt32.t {len <=^ maxlen}))

private let parseHeaderBuffer (b: Buffer.buffer UInt8.t {Buffer.length b = headerLength}) : ST parsed_header
  (requires (fun h0 -> Buffer.live h0 b))
  (ensures (fun h0 hdr h1 -> h0 == h1 /\ hdr = parseHeader (Bytes.hide (Buffer.as_seq h0 b))))
=
  // some margin for progress
  parseHeader (BufferBytes.to_bytes headerLength b)

val input_inv (h0: HS.mem) (s: input_state) : GTot Type0

// TODO later, use a length-field accessor instead of a header parser

val alloc_input_state: r:_ -> ST input_state 
  (requires (fun h0 -> is_eternal_region r))
  (ensures (fun h0 s h1 ->
    //18-04-20 TODO post-condition for allocating a ref and a buffer?
    Mem.frameOf (input_state_pos s) = r /\ 
    input_inv h1 s))

type read_result =
  | ReadError of TLS.Result.error
  | ReadWouldBlock
  | Received:
      ct:contentType ->
      pv:protocolVersion ->
      b:bytes {length b <= max_TLSCiphertext_fragment_length} -> read_result

// 2018.04.25 SZ:
// I had to modify the post-condition to say `input_inv` is preserved only if
// the result is not a ReadError.
// We return a ReadError when the header is invalid, but we still advance s.pos.
// We could preserve the invariant unconditionally if we advanced it only when
// the header is valid.
val read: Transport.t -> s: input_state -> ST read_result
  (requires fun h0 -> input_inv h0 s)
  (ensures fun h0 r h1 -> ReadError? r \/ input_inv h1 s)
//18-04-20 TODO modifies clause on a ref + a buffer
// let r = Mem.frameOf s.pos in
// Mem.modifies_one r h0 h1 
// Buffer.modifies_bufs_and_refs
//   (Buffer.only s.b)
//   (Set.singleton (Heap.addr_of (HS.as_ref s.pos)))
//   h0 h1)

(*        
//18-01-24 recheck async 
//    if length fresh = 0 then
//      ReadError(AD_internal_error,"TCP close") // otherwise we loop...

assert( Mem.contains h2 s.pos /\ Buffer.live h2 s.b )

assert(
  if v p0 < headerLength 
  then v p1 = headerLength 
  else 
    match parseHeader (Bytes.hide (Buffer.as_seq h0 (Buffer.sub s.b 0ul headerLen))) with
    | Correct (_,_,length) -> v p1 = headerLength + length 
    | _                    -> False)

assert(
  match parseHeader (Bytes.hide (Buffer.as_seq h1 (Buffer.sub s.b 0ul headerLen))) with
  | Correct (_,_,length) -> v p1 = headerLength + length 
  | _                    -> False)
*)

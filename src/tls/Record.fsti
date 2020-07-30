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

private let headerLen = 5ul 
private (* noextract *) let headerLength = v headerLen 
private type header = b:lbytes headerLength // for all TLS versions

// used only for testing
val makePacket
  (ct: contentType) (plain: bool) (ver: protocolVersion)
  (data: (b:bytes { repr_bytes (length b) <= 2}))
: St bytes

val sendPacket
  (tcp: Transport.t)
  (ct: contentType) (plain: bool) (ver: protocolVersion)
  (data: (b:bytes { repr_bytes (length b) <= 2}))
: St (result unit)

private type parsed_header = result (contentType
                           * protocolVersion
                           * l:nat { l <= max_TLSCiphertext_fragment_length})

// private // QUIC.fst needs access to this definition
val parseHeader: h5:header -> Tot parsed_header


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

//TODO index by region. // number of bytes already buffered
val input_state : Type0

val input_state_pos
  (s: input_state)
: Tot (ref (len: UInt32.t {len <=^ maxlen}))

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

module Record

module HS = FStar.HyperStack

(* (optional) encryption and processing of the outer (untrusted) record format *)

open FStar.Seq
open FStar.Bytes
open FStar.Error

open TLSError
open TLSInfo
open TLSConstants
open Range
open Content

// Consider merging some of this module with Content?

(* A flag for runtime debugging of record data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("REC| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_Record then print else (fun _ -> ())

// ------------------------outer packet format -------------------------------

// the "outer" header has the same format for all versions of TLS
// but TLS 1.3 fakes its content type and protocol version.


// inline_for_extraction let x = Transport.recv

type header = b:lbytes 5 // for all TLS versions

let fake = ctBytes Application_data @| versionBytes TLS_1p2

// this is the outer packet; the *caller* should switch from 1.3 to 1.0 whenever data is encrypted.
let makePacket ct plain ver (data: b:bytes { repr_bytes (length b) <= 2}) =
  let header =
    (if is_pv_13 ver then
      (if plain then ctBytes ct @| versionBytes TLS_1p2
       else fake)
     else (ctBytes ct @| versionBytes ver))
//      ctBytes ct
//   @| versionBytes ver
   @| bytes_of_int 2 (length data) in
  trace ("record headers: "^print_bytes header);
  header @| data

let sendPacket tcp ct plain ver (data: b:bytes { repr_bytes (length b) <= 2}) =
  // some margin for progress to avoid intermediate copies
  let packet = makePacket ct plain ver data in
  let res = Transport.send tcp (BufferBytes.from_bytes packet) (len packet) in
  if Int32.v res = Bytes.length packet then Correct()
  else Error(Printf.sprintf "Transport.send returned %l" res)



val parseHeader: h5:header -> Tot (result (contentType
                                         * protocolVersion
                                         * l:nat { l <= max_TLSCiphertext_fragment_length}))
let parseHeader (h5:header) =
    let (ct1,b4)   = FStar.Bytes.split h5 1ul in
    let (pv2,len2) = FStar.Bytes.split b4 2ul in
    match parseCT ct1 with
    | Error z -> Error z
    | Correct ct ->
      match TLSConstants.parseVersion pv2 with
      | Error z -> Error z
      | Correct (UnknownVersion _ _) ->
        Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Parsed unknown protocol version")
      | Correct pv ->
          let len = int_of_bytes len2 in
          if len <= 0 || len > max_TLSCiphertext_fragment_length
          then Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Wrong fragment length")
          else correct(ct,pv,len)

// hopefully we only care about the writer, not the cn state
// the postcondition is of the form
//   authId i ==> f is added to the writer log
let recordPacketOut (i:StatefulLHAE.id) (wr:StatefulLHAE.writer i) (pv: protocolVersion) f =
    let ct, rg = Content.ct_rg i f in
    let payload =
      if PlaintextID? i
      then Content.repr i f
      else
        let ad = StatefulPlain.makeAD i ct in
        let f = StatefulPlain.assert_is_plain i ad rg f in
        StatefulLHAE.encrypt #i wr ad rg f
    in
    makePacket ct (PlaintextID? i) pv payload


(*** networking (floating) ***)

// in the spirit of TLS 1.3, we ignore the outer protocol version (see appendix C):
// our server never treats the ClientHello's record pv as its minimum supported pv;
// our client never checks the consistency of the server's record pv.
// (see earlier versions for the checks we used to perform)

// connectlon-local input state
type partial =
  | Header
  | Body: ct: contentType -> pv: protocolVersion -> partial

open FStar.UInt32

private let maxlen = UInt32.uint_to_t (5 + max_TLSCiphertext_fragment_length)

private type input_buffer =
  b: Buffer.buffer UInt8.t {Buffer.length b = v maxlen}

//TODO index by region
type input_state = {
  pos: ref (len:UInt32.t {len <=^ maxlen});
  b: input_buffer }

let parseHeaderBuffer (b: Buffer.buffer UInt8.t {Buffer.length b = 5}) =
  // some margin for progress
  parseHeader (BufferBytes.to_bytes 5 b)

let waiting_len (s: input_state) =
  if !s.pos <^ 5ul
  then 5ul -^ !s.pos
  else
     match parseHeaderBuffer (Buffer.sub s.b 0ul 5ul) with
     | Correct (_,_,length) -> uint_to_t length +^ 5ul -^ (!s.pos)
     // other case to be statically excluded

let alloc_input_state r = {
  pos = ralloc r 0ul;
  b = Buffer.rcreate r 0uy maxlen }

type read_result =
  | ReadError of TLSError.error
  | ReadWouldBlock
  | Received:
      ct:contentType ->
      pv:protocolVersion ->
      b:bytes {length b <= max_TLSCiphertext_fragment_length} -> read_result


val read: Transport.t -> s: input_state -> ST read_result
  (requires fun h0 -> HS.contains h0 s.pos /\ Buffer.live h0 s.b)
  (ensures fun h0 _ h1 ->
    let r = HS.frameOf s.pos in
    HS.modifies_one r h0 h1)
// Refine by adding this?
//    Buffer.modifies_bufs_and_refs
//      (Buffer.only s.b)
//      (Set.singleton (Heap.addr_of (HS.as_ref s.pos)))
//      h0 h1)

let rec read tcp s =
  let waiting = waiting_len s in
  let p0 = !s.pos in
  let dest = Buffer.sub s.b p0 waiting in
  let res = Transport.recv tcp dest waiting in
  if res = -1l
  then ReadError (AD_internal_error, "Transport.recv")
  else if res = 0l
  then (trace "WouldBlock"; ReadWouldBlock)
  else (
    let received = Int.Cast.int32_to_uint32 res in
    s.pos := !s.pos +^ received;
    if received <^ waiting
      then
        // partial read
        // should probably ReadWouldBlock instead when non-blocking
        read tcp s
      else
        if !s.pos = 5ul // we have buffer the record header
        then (
          match parseHeaderBuffer s.b with
          | Error e -> ReadError e
          | Correct(ct,pv,length) ->
            if length = 0 then
              // corner case, possibly excluded by the RFC
              ( s.pos := 0ul; Received ct pv empty_bytes )
            else read tcp s )
        else
          // we have buffered the whoe record
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

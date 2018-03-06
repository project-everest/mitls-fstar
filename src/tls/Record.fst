module Record

(* (optional) encryption and processing of the outer (untrusted) record format *)

open FStar.Seq
open Platform.Bytes
open Platform.Error

open TLSError
open TLSInfo
open TLSConstants
module Range = Range
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

let x = Transport.recv

type header = b:lbytes 5 // for all TLS versions

let fake = ctBytes Application_data @| versionBytes TLS_1p0 

// this is the outer packet; the *caller* should switch from 1.3 to 1.0 whenever data is encrypted.
let makePacket ct plain ver (data: (b:bytes { repr_bytes (length b) <= 2})) =
  let header =
    (if ver = TLS_1p3 then
      (if plain then ctBytes ct @| versionBytes TLS_1p0
       else fake)
     else (ctBytes ct @| versionBytes ver))
//      ctBytes ct 
//   @| versionBytes ver
   @| bytes_of_int 2 (length data) in
  trace ("record headers: "^print_bytes header);
  header @| data 


val parseHeader: h5:header -> Tot (result (contentType 
                                         * protocolVersion 
                                         * l:nat { l <= max_TLSCiphertext_fragment_length}))
let parseHeader (h5:header) =
    let (ct1,b4)   = Platform.Bytes.split h5 1 in
    let (pv2,len2) = Platform.Bytes.split b4 2 in
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
// to be improved once we extract to C  
type partial = 
  | Header 
  | Body: ct: contentType -> pv: protocolVersion -> partial
type input_state = 
  | State:
    waiting: nat {waiting>0} -> 
    received: bytes -> 
    st: partial {
      match st with 
      | Header -> length received + waiting = 5 
      | Body _ _ -> length received + waiting <= max_TLSCiphertext_fragment_length } ->
    input_state
let wait_header = 
  let data = empty_bytes in
  assert(length empty_bytes = 0);
  State 5 empty_bytes Header

type read_result = 
  | ReadError of TLSError.error
  | ReadWouldBlock
  | Received:
      ct:contentType -> 
      pv:protocolVersion ->
      b:bytes {length b <= max_TLSCiphertext_fragment_length} -> read_result

val read: Transport.t -> s: HyperStack.ref input_state -> ST read_result
  (requires fun h0 -> HyperStack.contains h0 s)
  (ensures fun h0 _ h1 -> 
    let id = HyperStack.frameOf s in 
    HyperStack.modifies_one id h0 h1 /\ 
    HyperStack.modifies_ref id (Set.singleton (HyperStack.as_addr s)) h0 h1 )

let rec read tcp state =
  let State len prior partial = !state in 
  match Transport.recv tcp len with 
  | Platform.Tcp.RecvWouldBlock -> trace "WouldBlock"; ReadWouldBlock
  | Platform.Tcp.RecvError e -> ReadError (AD_internal_error, e) 
  | Platform.Tcp.Received fresh -> (
    let data = prior @| fresh in 
    if length fresh = 0 then 
      ReadError(AD_internal_error,"TCP close") // otherwise we loop...
    else if length fresh < len then (
      // partial read
      state := State (len - length fresh) data partial; 
      read tcp state // should probably ReadWouldBlock instead when non-blocking
      )
    else (
      // we have received what we asked for
      match partial with 
      | Header -> (
          match parseHeader data with  
          | Error e -> ReadError e 
          | Correct (ct,pv,len) -> 
              if len = 0 then (
                // corner case, possibly excluded by the RFC?
                state := State 5 empty_bytes Header; 
                Received ct pv empty_bytes )
              else (
                state := State  len empty_bytes (Body ct pv);
                read tcp state ))
      | Body ct pv -> (
              state := State 5 empty_bytes Header; 
              Received ct pv data )))


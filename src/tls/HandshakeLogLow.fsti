module HandshakeLogLow

open FStar.Bytes
open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module C = TLSConstants
module Hash = Hashing
module HashSpec = Hashing.Spec
module HSM = HandshakeMessages

module LP = LowParse.Low.Base


/// HandshakeMessages related definitions

type msg = HSM.hs_msg


/// Specifies which messages indicate the end of incoming flights
/// Triggers their Handshake processing

let end_of_flight : msg -> bool =
  let open HandshakeMessages in
  function
  | ClientHello _
  | HelloRetryRequest _
  | EndOfEarlyData
  | ServerHello _
  | ServerHelloDone
  | NewSessionTicket13 _
  | Finished _ -> true
  | _ -> false
// No support for binders yet -- comment copied from HandshakeLog


/// Specifies which messages require an intermediate transcript hash
/// in incoming flights. In doubt, we hash!

let tagged : msg -> bool =
  let open HSM in
  function
  | ClientHello _
  | ServerHello _
  | EndOfEarlyData        // for Client finished -- comment (and other comments below) copied from HandshakeLog
  | Certificate13 _       // for CertVerify payload in TLS 1.3
  | EncryptedExtensions _ // For PSK handshake: [EE; Finished]
  | CertificateVerify _   // for ServerFinish payload in TLS 1.3
  | ClientKeyExchange _   // only for client signing
  | NewSessionTicket _    // for server finished in TLS 1.2
  | Finished _ -> true     // for 2nd Finished
  | _ -> false
// NB CCS is not explicitly handled here, but can trigger tagging and end-of-flights -- comment copied from HandshakeLog


/// Towards defining validity of a transcript

let weak_valid_transcript (msgs:list msg) =
  let open HSM in
  match msgs with
  | []
  | [ClientHello _]
  | (ClientHello _)::(ServerHello _)::_ -> True
  | _ -> False

let transcript_version (msgs:list msg) :option C.protocolVersion =
  let open HSM in
  match msgs with
  | (ClientHello _)::(ServerHello sh)::_ -> Some sh.sh_protocol_version
  | _ -> None

let valid_transcript (msgs:list msg) =
  let version_opt = transcript_version msgs in
  weak_valid_transcript msgs /\
  (forall (m:msg).{:pattern List.memP m msgs} List.memP m msgs ==> HSM.valid_hs_msg_prop version_opt m)


/// Finally define the hs_transcript type

type hs_transcript : Type0 = msgs:list msg{valid_transcript msgs}

/// Bytes from the transcript

val transcript_bytes: hs_transcript -> GTot bytes


/// HSL main API

type lbuffer8 (l:uint_32) = b:B.buffer uint_8{B.len b == l}


/// Abstract HSL state

val hsl_state : Type0


/// With an abstract, state dependent invariant
///
/// TODO: Overwrite buffers for new flights OR content remains same?
///       For the I/O buffers

val hsl_invariant : HS.mem -> hsl_state -> Type0


/// Length of the input buffer that HSL reads from

val hsl_input_buf_len : hsl_state -> GTot uint_32


/// Input buffer itself

val hsl_input_buf : st:hsl_state -> GTot (lbuffer8 (hsl_input_buf_len st))


/// Index of the input buffer where HSL is at
/// Client (Record) should only add to the buffer at and after this index

val hsl_input_index : HS.mem -> st:hsl_state -> GTot (i:uint_32{i <= hsl_input_buf_len st})


/// Length of the output buffer, Handshake writes to it

val hsl_output_buf_len : hsl_state -> GTot uint_32


/// Output buffer itself

val hsl_output_buf : st:hsl_state -> GTot (lbuffer8 (hsl_output_buf_len st))


/// Index of the output buffer where HSL is at
/// Client (Handshake) should only add to the buffer at and after this index

val hsl_output_index : HS.mem -> st:hsl_state -> GTot (i:uint_32{i <= hsl_output_buf_len st})


/// HSL footprint
/// Local footprint is abstract and is allocated in the region provided at the creation time

val hsl_local_footprint : hsl_state -> B.loc

let hsl_footprint (h:HS.mem) (st:hsl_state) : GTot B.loc =
  let open B in
  loc_union (hsl_local_footprint st)  //local footprint
            (loc_union (loc_buffer (gsub (hsl_output_buf st) 0ul (hsl_output_index h st)))  //output buffer upto index
                       (loc_buffer (gsub (hsl_input_buf st) 0ul (hsl_input_index h st))))  //input buffer upto index


/// State dependent predicate
/// If true, HandShake can write

val writing : HS.mem -> hsl_state -> GTot bool


/// Hashing algorithm in use

val hash_alg : HS.mem -> hsl_state -> GTot (option Hash.alg)


/// Transcript of the messages so far, in both directions

val transcript : HS.mem -> hsl_state -> GTot hs_transcript


/// Invariant elimination

val elim_hsl_invariant (st:hsl_state) (h:HS.mem)
  : Lemma (requires (hsl_invariant h st))
          (ensures  (B.live h (hsl_input_buf st) /\ B.live h (hsl_output_buf st) /\
	             B.loc_pairwise_disjoint [hsl_local_footprint st; B.loc_buffer (hsl_input_buf st);
		                              B.loc_buffer (hsl_output_buf st)] /\
	             valid_transcript (transcript h st)))
	  [SMTPat (hsl_invariant h st)]

/// Invariant framing

val frame_hsl_invariant (st:hsl_state) (h0 h1:HS.mem) (l:B.loc)
  : Lemma (requires (hsl_invariant h0 st /\ B.modifies l h0 h1 /\ B.loc_disjoint (hsl_footprint h0 st) l))
          (ensures  (hsl_footprint h0 st == hsl_footprint h1 st /\ hsl_invariant h1 st))
          [SMTPat (hsl_invariant h1 st); SMTPat (B.modifies l h0 h1)]


/// Creation of the log

unfold private let create_post (r:Mem.rgn)
                               (input_len:uint_32) (input_buf:lbuffer8 input_len)
	                       (output_len:uint_32) (output_buf:lbuffer8 output_len)
  : HS.mem -> hsl_state -> HS.mem -> Type0

  = fun h0 st h1 ->
    hsl_input_buf_len st == input_len /\ hsl_input_buf st == input_buf /\
    hsl_output_buf_len st == output_len /\ hsl_output_buf st == output_buf /\  //I/O bufs are as given
    hsl_input_index h1 st == 0ul /\  //input index is 0
    hsl_output_index h1 st == 0ul /\  //output index is 0
    B.fresh_loc (hsl_local_footprint st) h0 h1 /\  //local footprint is fresh
    B.loc_includes (B.loc_regions true (Set.singleton r)) (hsl_local_footprint st) /\  //TODO: local footprint is in r only
    hsl_invariant h1 st /\  //invariant holds
    writing h1 st /\  //Handshake can write
    hash_alg h1 st == None /\  //hash_alg is not set
    transcript h1 st == [] /\  //empty transcript
    B.modifies B.loc_none h0 h1  //did not modify anything
  
val create (r:Mem.rgn) (pv:option C.protocolVersion)  //TODO: pv is always None?
           (input_len:uint_32) (input_buf:lbuffer8 input_len)
	   (output_len:uint_32) (output_buf:lbuffer8 output_len)
  : ST hsl_state (requires (fun h0 -> 
                            B.live h0 input_buf /\ B.live h0 output_buf /\
                            B.loc_disjoint (B.loc_buffer input_buf) (B.loc_buffer output_buf)))  //disjoint I/O buffers
                 (ensures  (create_post r input_len input_buf output_len output_buf))


/// Setting parameters such as the hashing algorithm

unfold private let set_params_post (st:hsl_state) (a:Hashing.alg)
  : HS.mem -> unit -> HS.mem -> Type0

  = fun h0 _ h1 ->
    B.modifies (hsl_local_footprint st) h0 h1 /\  //modifies only local footprint
    transcript h1 st == transcript h0 st /\  //transcript remains same
    writing h1 st == writing h0 st /\  //writing capability remains same
    hsl_input_index h1 st == hsl_input_index h0 st /\  //input index remains same
    hsl_output_index h1 st == hsl_output_index h0 st /\  //output index remains same
    hash_alg h1 st == Some a /\  //hash algorithm is set
    hsl_invariant h1 st  //invariant holds
                         //NB: we are not saying hsl_footprint is same explicitly, it is derivable though, as shown below

private let footprint_remains_same_across_set_params
  (st:hsl_state) (a:Hashing.alg) (h0 h1:HS.mem)
  : Lemma (requires (set_params_post st a h0 () h1))
          (ensures  (hsl_footprint h0 st == hsl_footprint h1 st))
  = ()

val set_params (st:hsl_state) (_:C.protocolVersion) (a:Hashing.alg) (_:option CipherSuite.kexAlg)
               (_:option CommonDH.group)
  : ST unit (requires (fun h0 -> hash_alg h0 st == None /\ hsl_invariant h0 st))
            (ensures  (set_params_post st a))


/// Receive API
/// Until a full flight is received, we lose "writing" capability -- as per the comment in HandshakeLog

val tags (a:Hash.alg) (prior:list msg) (ms:list msg) (hs:list HashSpec.anyTag) :Tot Type0  //TODO: this is implemented in HandshakeLog.fsti, copy

/// TODO: Should come from QD

val hs_transcript_parser : LP.parser (LP.strong_parser_kind 8 8 ({ LP.parser_kind_metadata_total = true })) hs_transcript

(* msgs is parsing of the input sub-buffer between p0 and p1 *)
unfold private let transcript_parsing_of (msgs:hs_transcript) (st:hsl_state)
                                         (p0:uint_32) (p1:uint_32{p0 <= p1 /\ p1 <= hsl_input_buf_len st})
			                 (h:HS.mem)
  = let delta = p1 - p0 in
    let sub = B.gsub (hsl_input_buf st) p0 delta in
    match LP.parse hs_transcript_parser (B.as_seq h sub) with
    | None -> False
    | Some (parse, consumed) -> parse == msgs /\ consumed == v delta

unfold private let receive_post (st:hsl_state) (p:uint_32)
  : HS.mem -> (TLSError.result (option (G.erased hs_transcript &
                               uint_32 & uint_32 &
                               list HashSpec.anyTag))) -> HS.mem -> Type0
  = fun h0 r h1 ->  
    let open FStar.Error in
    let oa = hash_alg h0 st in
    let t0 = transcript h0 st in
    let t1 = transcript h1 st in
    B.modifies (hsl_local_footprint st) h0 h1 /\  //only local footprint is modified
    hash_alg h1 st == oa /\  //hash alg remains same
    hsl_invariant h1 st /\  //invariant holds
    hsl_output_index h1 st == hsl_output_index h0 st /\  //output index remains same
    hsl_input_index h1 st == p /\  //input index is advanced to p
    (match r with
     | Error _ -> True  //underspecified
     | Correct None -> t0 == t1  //waiting for more data
     | Correct (Some (ms, p0, p1, hs)) ->
       let ms = G.reveal ms in
       t1 == t0 @ ms /\  //added ms to the transcript
       writing h1 st /\  //Handshake can now write
       p <= hsl_input_buf_len st /\
       p0 <= p1 /\ p1 <= p /\  //returned indices are valid in the input buffer
       transcript_parsing_of ms st p0 p1 h1 /\  //ms is a valid parsing of input buffer contents between p0 and p1
       (match oa with
        | Some a -> tags a t0 ms hs  //hashed properly
        | None -> hs == []))

//TODO: return a list of message flight constructors so that Handshake does not have to parse it again
//TODO: delay the hashing OR Handshake explicitly calls Log to compute the digest 
val receive (st:hsl_state) (p:uint_32)
  : ST (TLSError.result (option (G.erased hs_transcript &  //ghost transcript, list msg or hs_transcript
                                 uint_32 & uint_32 &  //buffer indices in the input buffer
                                 list HashSpec.anyTag)))  //TODO: erased transcript and concrete hash?
       (requires (fun h0 ->
                  hsl_invariant h0 st /\  //invariant should hold
                  hsl_input_index h0 st <= p /\  //TODO: should have written >= 0 bytes (> 0?)
		  p <= hsl_input_buf_len st))  //p should be in the input buffer range
       (ensures  (receive_post st p))


/// TODO: receive_CCS


/// Send API

/// TODO: should come from QD

val msg_parser : LP.parser (LP.strong_parser_kind 8 8 ({ LP.parser_kind_metadata_total = true })) msg

unfold private let msg_parsing_of (m:msg) (st:hsl_state)
                                  (p0:uint_32) (p1:uint_32{p0 <= p1 /\ p1 <= hsl_output_buf_len st})
			          (h:HS.mem)
  = let delta = p1 - p0 in
    let sub = B.gsub (hsl_output_buf st) p0 delta in
    match LP.parse msg_parser (B.as_seq h sub) with
    | None -> False
    | Some (parse, consumed) -> parse == m /\ consumed == v delta

unfold private let send_pre (st:hsl_state) (p:uint_32) (m:G.erased msg)
  : HS.mem -> Type0
  = fun h0 ->
    let open HandshakeMessages in
    hsl_invariant h0 st /\  //invariant holds
    hsl_output_index h0 st <= p /\ p <= hsl_output_buf_len st /\  //p is in range of output buffer
    msg_parsing_of (G.reveal m) st (hsl_output_index h0 st) p h0 /\  //m is a valid parsing of sub-buffer between p0 and p1
    writing h0 st /\  //Handshake is allowed to write
    valid_transcript (transcript h0 st @ [G.reveal m]) /\  //valid transcript
    (match G.reveal m with  //copied from HandshakeLog as is
     | HelloRetryRequest req -> Some? (C.cipherSuite_of_name req.hrr_cipher_suite)
     | _ -> True)

unfold private let send_post (st:hsl_state) (p:uint_32) (m:G.erased msg)
  : HS.mem -> unit -> HS.mem -> Type0
  = fun h0 _ h1 ->
    B.modifies (hsl_local_footprint st) h0 h1 /\  //only local footprint is modified
    writing h1 st /\  //writing capability remains
    hash_alg h1 st == hash_alg h0 st /\  //hash algorithm is same as before
    transcript h1 st == transcript h0 st @ [G.reveal m] /\  //transcript includes m
    hsl_invariant h1 st /\  //invariant hold
    hsl_input_index h1 st == hsl_input_index h0 st /\  //input buffer index remains same
    hsl_output_index h1 st == p  //output buffer index is advanced to p

val send (st:hsl_state) (p:uint_32) (m:G.erased msg)
  : ST unit (requires (send_pre st p m))
            (ensures  (send_post st p m))
		       
/// hash_tag API

/// TODO: the postcondition fails to typecheck

#push-options "--admit_smt_queries true"
val hash_tag (a:Hash.alg) (st:hsl_state)
  : ST (Hash.tag a) (requires (fun h0 -> hsl_invariant h0 st))
                    (ensures  (fun h0 r h1 ->
		               let bs = transcript_bytes (transcript h1 st) in
			       h0 == h1 /\ Hashing.CRF.hashed a bs /\ r == Hash.h a bs))
#pop-options

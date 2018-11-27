module HandshakeLogLow

open FStar.Integers
open FStar.HyperStack.ST

module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module C = TLSConstants
module Hash = Hashing
module HSM = HandshakeMessages


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


/// HSL main API

type lbuffer8 (l:uint_32) = b:B.buffer uint_8{B.len b == l}


/// Abstract HSL state

val hsl_state : Type0


/// With an abstract, state dependent invariant

val hsl_invariant : HS.mem -> hsl_state -> Type0


/// Length of the input buffer that HSL reads from

val hsl_input_buf_len : hsl_state -> uint_32


/// Input buffer itself

val hsl_input_buf : st:hsl_state -> lbuffer8 (hsl_input_buf_len st)


/// Index of the input buffer where HSL is at

val hsl_input_index : HS.mem -> st:hsl_state -> i:uint_32{i <= hsl_input_buf_len st}


/// Length of the output buffer that HSL writes to

val hsl_output_buf_len : hsl_state -> uint_32


/// Output buffer itself

val hsl_output_buf : st:hsl_state -> lbuffer8 (hsl_output_buf_len st)


/// HSL footprint

val hsl_local_footprint : hsl_state -> B.loc

let hsl_footprint (h:HS.mem) (st:hsl_state) : GTot B.loc =
  let open B in
  loc_union (hsl_local_footprint st)  //local footprint
            (loc_union (loc_buffer (hsl_output_buf st))  //output buffer
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
		                              B.loc_buffer (hsl_output_buf st)]))
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
    B.fresh_loc (hsl_local_footprint st) h0 h1 /\  //local footprint is fresh
    B.loc_includes (B.loc_regions true (Set.singleton r)) (hsl_local_footprint st) /\  //TODO: local footprint is in r only
    hsl_invariant h1 st /\  //invariant holds
    writing h1 st /\  //Handshake can write
    hash_alg h1 st == None /\  //hash_alg is not set
    transcript h1 st == [] /\  //empty transcript
    B.modifies B.loc_none h0 h1  //did not modify anything
  
val create (r:Mem.rgn) (pv:option C.protocolVersion)
           (input_len:uint_32) (input_buf:lbuffer8 input_len)
	   (output_len:uint_32) (output_buf:lbuffer8 output_len)
  : ST hsl_state (requires (fun _ -> B.loc_disjoint (B.loc_buffer input_buf) (B.loc_buffer output_buf)))
                 (ensures  (create_post r input_len input_buf output_len output_buf))


/// Setting parameters such as the hashing algorithm

unfold private let set_params_post (st:hsl_state) (a:Hashing.alg)
  : HS.mem -> unit -> HS.mem -> Type0

  = fun h0 _ h1 ->
    B.modifies (hsl_local_footprint st) h0 h1 /\
    transcript h1 st == transcript h0 st /\
    writing h1 st == writing h0 st /\
    hsl_input_index h1 st == hsl_input_index h0 st /\
    hash_alg h1 st == Some a /\
    hsl_invariant h1 st  //NB: we are not saying hsl_footprint is same explicitly, it is derivable though

val set_params (st:hsl_state) (_:C.protocolVersion) (a:Hashing.alg) (_:option CipherSuite.kexAlg)
               (_:option CommonDH.group)
  : ST unit (requires (fun h0 -> hash_alg h0 st == None /\ hsl_invariant h0 st))
            (ensures  (set_params_post st a))


/// Receive API
/// Until a full flight is received, we lose "writing" capability -- as per the comment in HandshakeLog

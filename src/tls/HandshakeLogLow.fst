module HandshakeLogLow

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

module IncHash = EverCrypt.Hash.Incremental

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -LowParse'"


/// Its corresponding format_hs_msg is in the .fsti
/// These will be implemented using the high-level parsers and serializers from LowParse

assume
val parse_hs_msg (b:hbytes) : GTot (option HSM.hs_msg)


// AR: 1/23: implemented in the .fsti now (was needed for hashing spec)

// /// Bytes from the transcript

// let transcript_bytes (ts:hs_transcript)
//   : GTot bytes
//   = admit() //Need to use LowParse spec formatters


//buffer and in index into it
let index (max:uint_32) = i:uint_32{i <= max}

noeq
type indexed_buf = {
  len:uint_32;
  buf:lbuffer8 len;
  idx:(p:B.pointer (index len){B.disjoint buf p});

  // AR: 1/23: as per most recent discussions, hashing state is kept in HS, HSL is stateless as far as hashing is concerned

  // hash_idx:(p:B.pointer (index len) {
  //   B.all_disjoint [B.loc_buffer buf;
  //                   B.loc_buffer idx;
  //                   B.loc_buffer p]
  // })
}

// AR: 1/23: same comment as above, commenting hashing index

unfold
let loc_indexed_buf_indices i = B.loc_buffer i.idx
  // B.(loc_union_l [loc_buffer i.idx;
  //    loc_buffer i.hash_idx])

unfold
let loc_indexed_buf i = B.(loc_union_l [loc_indexed_buf_indices i;
                                        loc_buffer i.buf])

let empty_transcript : hs_transcript = []


// AR: 1/23: this also seems like it is trying to keep some hashing state?
//           instead we could just keep an erased list?

// noeq
// type tx (#max_i:uint_32) (#max_j:uint_32) : i:index max_i -> j:index max_j -> hs_transcript -> Type0 =
//   | Nil : tx #max_i #max_j 0ul 0ul empty_transcript

//   | IFrag : #i:index max_i ->
//             #j:index max_j ->
//             #msgs:hs_transcript ->
//             tl:tx i j msgs ->
//             k:index max_i{i < k} ->
//             msg:HSM.hs_msg{valid_transcript (msg::msgs)} ->
//             tx k j (msg::msgs)

//   | OFrag : #i:index max_i ->
//             #j:index max_j ->
//             #msgs:hs_transcript ->
//             tl:tx i j msgs ->
//             k:index max_j{j < k} ->
//             msg:HSM.hs_msg{valid_transcript (msg::msgs)} ->
//             tx i k (msg::msgs)

// let tx_repr max_i max_j = i:index max_i & j:index max_j & msgs:hs_transcript & tx i j msgs
// let tx_repr_ptr max_i max_j = B.pointer (G.erased (tx_repr max_i max_j))

noeq
type hsl_state = {
  input:indexed_buf;

  // AR: 1/23: it seems like we don't maintain any invariants for the output buffer, could we just keep it out of (low) HSL?
  //output:indexed_buf;

  // AR: 1/23: changing it to a dependent tuple, not low-level?
  //hash_alg: B.pointer (option Hash.alg);

  hash_state: B.pointer (option (a:Hash.alg & IncHash.state a));

  tx: (p:B.pointer (G.erased hs_transcript){B.all_disjoint [loc_indexed_buf input;
                                                            B.loc_buffer hash_state;
                                                            B.loc_buffer p]})
							    

  // AR: 1/23: trying to simplify a bit, by removing hash state

  // tx: (p:tx_repr_ptr input.len output.len{
  //   B.(all_disjoint [loc_indexed_buf input;
  //                    loc_indexed_buf output;
  //                    loc_buffer hash_alg;
  //                    loc_buffer p])
  //  })
}

let indexed_buf_liveness (h:HS.mem) (i:indexed_buf) =
  B.live h i.buf /\
  B.live h i.idx
  // AR: 1/23: as per comments above, commenting hash state
  //B.live h i.hash_idx

let hsl_input_buf_len s = s.input.len
let hsl_input_buf s = s.input.buf
let hsl_input_index s h = B.deref h s.input.idx

// AR: 1/23: commenting as part of removing hash-based state
// let hsl_input_hash_index h s = B.deref h s.input.hash_idx


// AR: 1/23: commenting as part of removing output state
// let hsl_output_buf_len (s:hsl_state) = s.output.len
// let hsl_output_buf (s:hsl_state) = s.output.buf
// let hsl_output_index h s = B.deref h s.output.idx
// let hsl_output_hash_index h s = B.deref h s.output.hash_idx

let hsl_local_footprint s h =
  B.loc_union_l [loc_indexed_buf_indices s.input;

                 // AR: 1/23: commenting out as part of removing output related state
                 // loc_indexed_buf_indices s.output;
		 
                 B.loc_buffer s.hash_state;

                 (match B.deref h s.hash_state with
                  | None -> B.loc_none
		  | Some (| _, hash_st |) -> IncHash.footprint hash_st h);

                 B.loc_buffer s.tx]

/// Handshake can write if all the input messages have been hashed

// AR: 1/23: this is still not clear. HSL is not maintaining any hashing state now
//           and we have also discussed if this is needed at all
//           (we are not proving, as of now, anything about state machines of two ends being synchronized)
let writing h s = true
  //hsl_input_hash_index h s = hsl_input_index h s

let hash_alg s h =
  match B.deref h s.hash_state with
  | None -> None
  | Some (| a, _ |) -> Some a


// AR: 1/23: commenting as part of hash state cleanup
// let get_tx_repr h s : GTot (tx_repr (hsl_input_buf_len s) (hsl_output_buf_len s)) =
//   G.reveal (B.deref h s.tx)

let transcript s h = G.reveal (B.deref h s.tx)
  // let (| _, _, msgs, _ |) = get_tx_repr h s in
  // msgs

// AR: 1/23: commenting to simplify some hash-related state

// let tx_input_index h s : GTot (index (hsl_input_buf_len s)) =
//   let (| i, _, msgs, _ |) = get_tx_repr h s in
//   i

// let tx_output_index h s : GTot (index (hsl_output_buf_len s)) =
//   let (| _, j, msgs, _ |) = get_tx_repr h s in
//   j

// let get_tx h s : GTot (tx (tx_input_index h s) (tx_output_index h s) (transcript h s)) =
//   let (| i, j, msgs, tx |) = get_tx_repr h s in
//   tx

// #push-options "--initial_ifuel 1 --max_ifuel 1"
// let msg_correspondence (msg:HSM.hs_msg) (b:Bytes.bytes) (from:index (Bytes.len b)) (to:index (Bytes.len b){from < to}) =
//     let x = Bytes.sub b from (to - from) in
//     let popt = parse_hs_msg x in
//     Some? popt /\
//     Some?.v popt == msg

// let rec transcript_correspondence
//           #max_i #max_j
//           (input:Bytes.bytes)
//           (output:Bytes.bytes)
//           (#i:index max_i {i <= Bytes.len input})
//           (#j:index max_j {j <= Bytes.len output})
//           #msgs
//           (tx:tx i j msgs)
//    : GTot prop
//           (decreases tx)
//    = match tx with
//      | Nil ->    //nothing hashed yet
//        True

//      | IFrag #_ #_ #from tl to msg ->
//        msg_correspondence msg input from to /\
//        transcript_correspondence input output tl

//      | OFrag #_ #_ #_ #from tl to msg ->
//        msg_correspondence msg output from to /\
//        transcript_correspondence input output tl

// let indexed_buf_bytes (h:HS.mem) (i:indexed_buf)
//   : GTot (b:Bytes.bytes{Bytes.len b = B.deref h i.hash_idx})
//   = Bytes.hide (B.as_seq h (B.gsub i.buf 0ul (B.deref h i.hash_idx)))

let format_hs_msg m = admit ()  //implement in .fsti with LowParse

let hsl_invariant s h =
  indexed_buf_liveness h s.input /\

  // AR: 1/23: commented as part of removing output state
  // indexed_buf_liveness h s.output /\
 
  B.live h s.hash_state /\
  B.live h s.tx /\

  hsl_input_index s h <= hsl_input_buf_len s /\

  (match B.deref h s.hash_state with
   | None -> True
   | Some (| a, hash_st |) ->
     //IncHash.hashes already includes the invariant of hash
     IncHash.hashes #a h hash_st (transcript_bytes (G.reveal (B.deref h s.tx))) /\

     //disjointness of hash footprint from everything else
     (let hash_fp = IncHash.footprint hash_st h in
      B.(loc_disjoint hash_fp (loc_indexed_buf s.input) /\
         loc_disjoint hash_fp (loc_buffer s.hash_state) /\
	 loc_disjoint hash_fp (loc_buffer s.tx))))

   

  // AR: 1/23: commented as part of removing hash-based state

  // hsl_input_hash_index h s <= hsl_input_index h s /\
  // hsl_output_hash_index h s <= hsl_output_index h s /\
  // hsl_input_hash_index h s == tx_input_index h s /\
  // hsl_output_hash_index h s == tx_output_index h s /\
  // transcript_correspondence (indexed_buf_bytes h s.input)
  //                           (indexed_buf_bytes h s.output)
  //                           #(tx_input_index h s)
  //                           #(tx_output_index h s)
  //                           #(transcript h s)
  //                           (get_tx h s)

let elim_hsl_invariant st h = admit ()

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit_factor 2"
let frame_hsl_invariant (s:hsl_state) (h0 h1:HS.mem) (l:B.loc) = admit ()
#pop-options

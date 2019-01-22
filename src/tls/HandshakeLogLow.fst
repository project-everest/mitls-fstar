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


assume
val parse_hs_msg (b:bytes) : GTot (option HSM.hs_msg)


/// Bytes from the transcript

let transcript_bytes (ts:hs_transcript)
  : GTot bytes
  = admit() //Need to use LowParse spec formatters

//buffer and in index into it
let index (max:uint_32) = i:uint_32{i <= max}

noeq
type indexed_buf = {
  len:uint_32;
  buf:lbuffer8 len;
  idx:B.pointer (index len);
  hash_idx:(p:B.pointer (index len) {
    B.all_disjoint [B.loc_buffer buf;
                    B.loc_buffer idx;
                    B.loc_buffer p]
  })
}

unfold
let loc_indexed_buf_indices i = B.(loc_union_l [loc_buffer i.idx;
                                                loc_buffer i.hash_idx])

unfold
let loc_indexed_buf i = B.(loc_union_l [loc_indexed_buf_indices i;
                                        loc_buffer i.buf])

#push-options "--initial_ifuel 1 --max_ifuel  1 --initial_fuel 1 --max_fuel 1"
let empty_transcript : hs_transcript = []
#pop-options

noeq
type tx (#max_i:uint_32) (#max_j:uint_32) : i:index max_i -> j:index max_j -> hs_transcript -> Type0 =
  | Nil : tx #max_i #max_j 0ul 0ul empty_transcript

  | IFrag : #i:index max_i ->
            #j:index max_j ->
            #msgs:hs_transcript ->
            tl:tx i j msgs ->
            k:index max_i{i < k} ->
            msg:HSM.hs_msg{valid_transcript (msg::msgs)} ->
            tx k j (msg::msgs)

  | OFrag : #i:index max_i ->
            #j:index max_j ->
            #msgs:hs_transcript ->
            tl:tx i j msgs ->
            k:index max_j{j < k} ->
            msg:HSM.hs_msg{valid_transcript (msg::msgs)} ->
            tx i k (msg::msgs)

let tx_repr max_i max_j = i:index max_i & j:index max_j & msgs:hs_transcript & tx i j msgs
let tx_repr_ptr max_i max_j = B.pointer (G.erased (tx_repr max_i max_j))

noeq
type hsl_state = {
  input:indexed_buf;
  output:indexed_buf;
  hash_alg: B.pointer (option Hash.alg);
  tx: (p:tx_repr_ptr input.len output.len{
    B.(all_disjoint [loc_indexed_buf input;
                     loc_indexed_buf output;
                     loc_buffer hash_alg;
                     loc_buffer p])
   })
}

let indexed_buf_liveness (h:HS.mem) (i:indexed_buf) =
  B.live h i.buf /\
  B.live h i.idx /\
  B.live h i.hash_idx

let hsl_input_buf_len (s:hsl_state) = s.input.len
let hsl_input_buf (s:hsl_state) = s.input.buf
let hsl_input_index h s = B.deref h s.input.idx
let hsl_input_hash_index h s = B.deref h s.input.hash_idx

let hsl_output_buf_len (s:hsl_state) = s.output.len
let hsl_output_buf (s:hsl_state) = s.output.buf
let hsl_output_index h s = B.deref h s.output.idx
let hsl_output_hash_index h s = B.deref h s.output.hash_idx

let hsl_local_footprint s =
  B.loc_union_l [loc_indexed_buf_indices s.input;
                 loc_indexed_buf_indices s.output;
                 B.loc_buffer s.hash_alg;
                 B.loc_buffer s.tx]

/// Handshake can write if all the input messages have been hashed
let writing h s =
  hsl_input_hash_index h s = hsl_input_index h s

let hash_alg h s = B.deref h s.hash_alg

let get_tx_repr h s : GTot (tx_repr (hsl_input_buf_len s) (hsl_output_buf_len s)) =
  G.reveal (B.deref h s.tx)

let transcript h s =
  let (| _, _, msgs, _ |) = get_tx_repr h s in
  msgs

let tx_input_index h s : GTot (index (hsl_input_buf_len s)) =
  let (| i, _, msgs, _ |) = get_tx_repr h s in
  i

let tx_output_index h s : GTot (index (hsl_output_buf_len s)) =
  let (| _, j, msgs, _ |) = get_tx_repr h s in
  j

let get_tx h s : GTot (tx (tx_input_index h s) (tx_output_index h s) (transcript h s)) =
  let (| i, j, msgs, tx |) = get_tx_repr h s in
  tx

#push-options "--initial_ifuel 1 --max_ifuel 1"
let msg_correspondence (msg:HSM.hs_msg) (b:Bytes.bytes) (from:index (Bytes.len b)) (to:index (Bytes.len b){from < to}) =
    let x = Bytes.sub b from (to - from) in
    let popt = parse_hs_msg x in
    Some? popt /\
    Some?.v popt == msg

let rec transcript_correspondence
          #max_i #max_j
          (input:Bytes.bytes)
          (output:Bytes.bytes)
          (#i:index max_i {i <= Bytes.len input})
          (#j:index max_j {j <= Bytes.len output})
          #msgs
          (tx:tx i j msgs)
   : GTot prop
          (decreases tx)
   = match tx with
     | Nil ->    //nothing hashed yet
       True

     | IFrag #_ #_ #from tl to msg ->
       msg_correspondence msg input from to /\
       transcript_correspondence input output tl

     | OFrag #_ #_ #_ #from tl to msg ->
       msg_correspondence msg output from to /\
       transcript_correspondence input output tl

let indexed_buf_bytes (h:HS.mem) (i:indexed_buf)
  : GTot (b:Bytes.bytes{Bytes.len b = B.deref h i.hash_idx})
  = Bytes.hide (B.as_seq h (B.gsub i.buf 0ul (B.deref h i.hash_idx)))

#set-options "--print_implicits"
unfold
let hsl_invariant' (h:HS.mem) (s:hsl_state) =
 indexed_buf_liveness h s.input /\
 indexed_buf_liveness h s.output /\
 B.live h s.hash_alg /\
 B.live h s.tx /\
 hsl_input_hash_index h s <= hsl_input_index h s /\
 hsl_output_hash_index h s <= hsl_output_index h s /\
 hsl_input_hash_index h s == tx_input_index h s /\
 hsl_output_hash_index h s == tx_output_index h s /\
 transcript_correspondence (indexed_buf_bytes h s.input)
                           (indexed_buf_bytes h s.output)
                           #(tx_input_index h s)
                           #(tx_output_index h s)
                           #(transcript h s)
                           (get_tx h s)

let hsl_invariant h s = hsl_invariant' h s

let elim_hsl_invariant (st:hsl_state) (h:HS.mem) = ()

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit_factor 2"
let frame_hsl_invariant (s:hsl_state) (h0 h1:HS.mem) (l:B.loc) = ()
#pop-options

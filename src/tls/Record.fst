module Record

(* (optional) encryption and processing of the outer, untrusted record format *)

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

#reset-options "--using_facts_from '* -LowParse.Spec.Base'"

#set-options "--z3rlimit 10" //18-04-20 now required; why?
noeq type input_state = | InputState:
  pos: ref (len:UInt32.t {len <=^ maxlen}) ->
  b: input_buffer {
    Buffer.disjoint_ref_1 b pos /\
    Buffer.frameOf b = Mem.frameOf pos /\ 
    Buffer.length b = v maxlen} -> 
  input_state

let input_inv h0 (s: input_state) = 
  Mem.contains h0 s.pos /\
  Buffer.live h0 s.b /\
  ( let p0 = UInt32.v (sel h0 s.pos) in 
    p0 < headerLength \/ 
    ( let hdr = parseHeader (Bytes.hide (Buffer.as_seq h0 (Buffer.sub s.b 0ul headerLen))) in
      match hdr with  
      | Correct (_,_,length) -> p0 < headerLength + length 
      | _                    -> False ))
// we are waiting either for header bytes or payload bytes

let input_pos s = s.pos
let input_b s = s.b

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -LowParse -Format'"
let waiting_len s =
  if !s.pos <^ headerLen
  then headerLen -^ !s.pos
  else
    let Correct (_,_,length) = parseHeaderBuffer (Buffer.sub s.b 0ul headerLen) in
    headerLen +^ uint_to_t length -^ !s.pos

// TODO later, use a length-field accessor instead of a header parser

let alloc_input_state r = 
  let pos = ralloc r 0ul in
  let b = Buffer.rcreate r 0uy maxlen in
  InputState pos b

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -LowParse -Format' --z3rlimit 30"
let rec read tcp s =
  let h0 = ST.get() in 
  let header = Buffer.sub s.b 0ul headerLen in 
  let p0 = !s.pos in
  let waiting = waiting_len s in
  let dest = Buffer.sub s.b p0 waiting in
  let res = Transport.recv tcp dest waiting in
  let h1 = ST.get() in
  Buffer.lemma_reveal_modifies_1 dest h0 h1;
  // framing, with two cases depending on the input state.
  //assert(p0 <^ headerLen \/ Buffer.disjoint header dest);
  //assert(p0 <^ headerLen \/ Buffer.as_seq h0 header == Buffer.as_seq h1 header);
  if res = -1l then
    ReadError (fatalAlert Internal_error, "Transport.recv")
  else
  if res = 0l
  then ( trace "WouldBlock"; ReadWouldBlock )
  else
    begin
    let received = Int.Cast.int32_to_uint32 res in
    assert (received <=^ waiting);
    assert (p0 +^ waiting <=^ maxlen);
    let p1 = p0 +^ received in 
    s.pos := p1;
    //let h2 = ST.get() in
    //assert(p0 <^ headerLen \/ Buffer.as_seq h0 header == Buffer.as_seq h2 header);
    if received <^ waiting
    then
      // partial read; we remain in the same logical state
      // we should probably return ReadWouldBlock instead when non-blocking
      read tcp s
    else
      begin
      if p1 = headerLen 
      then
        begin
        // we have just buffered the record header
        match parseHeaderBuffer header with
        | Error e -> ReadError e
        | Correct(ct, pv, length) ->
          if length = 0 then
            begin
            // zero-length packet, a corner case possibly excluded by the RFC
            s.pos := 0ul;
            Received ct pv empty_bytes
            end
          else read tcp s
        end
      else
        begin
        // we have just buffered the whole record
        assert(headerLen <=^ p0); 
        let hdr = parseHeaderBuffer header in 
        match hdr with
        | Correct(ct, pv, length) ->
          begin
          let len = UInt32.uint_to_t length in
          let b = Buffer.sub s.b headerLen len in
          let payload = BufferBytes.to_bytes length b in
          s.pos := 0ul;
          Received ct pv payload
          end
        end
      end
    end

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

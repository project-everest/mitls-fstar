module HSL.Receive

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module HSM = HandshakeMessages
module LP = LowParse.Low.Base

open HSL.Common

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

type inc_st_t = G.erased (bytes & in_progress_flt_t)

noeq
type hsl_state = {
  rgn: Mem.rgn;
  inc_st: (p:B.pointer inc_st_t{
    rgn `region_includes` B.loc_buffer p
  });
}

let region_of st = st.rgn

let parsed_bytes st h = fst (G.reveal (B.deref h st.inc_st))

let in_progress_flt st h = snd (G.reveal (B.deref h st.inc_st))

let invariant s h = B.live h s.inc_st

let footprint s = B.loc_buffer s.inc_st

let frame_hsl_state _ _ _ _ = ()

let create r =
  let inc_st = B.malloc r (G.hide (Seq.empty, F_none)) 1ul in
  { rgn = r; inc_st = inc_st }

let receive_flight13_ee_c_cv_fin _ _ _ _ = admit()
let receive_flight13_ee_cr_c_cv_fin _ _ _ _ = admit ()
let receive_flight13_ee_fin _ _ _ _ = admit ()

module HSM13 = Parsers.Handshake13


assume val parsing_error : TLSError.error

let receive_flight13_fin st b from to =
  let open FStar.Error in
  
  //first use the handshake13 validator
  let pos = HSM13.handshake13_validator b from in

  if pos <= LP.validator_max_length then admit ()

  else if pos = LP.validator_error_not_enough_data then begin
    let inc_st =
      let h = ST.get () in
      let parsed_bytes = LP.bytes_of_slice_from_to h b from to in
      let in_progress = F13_fin in
      G.hide (parsed_bytes, in_progress)
    in
    B.upd st.inc_st 0ul inc_st;
    FStar.Error.Correct None
  end
 
  else Error parsing_error

let receive_flight13_c_cv_fin _ _ _ _ = admit ()
let receive_flight13_eoed _ _ _ _ = admit ()
let receive_flight13_nst _ _ _ _ = admit ()

module HSL.Receive

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
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
let receive_flight13_fin _ _ _ _ = admit ()
let receive_flight13_c_cv_fin _ _ _ _ = admit ()
let receive_flight13_eoed _ _ _ _ = admit ()
let receive_flight13_nst _ _ _ _ = admit ()

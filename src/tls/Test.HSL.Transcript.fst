module Test.HSL.Transcript
module HT = HSL.Transcript
module Receive = HSL.Receive
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
open FStar.Integers

open FStar.HyperStack.ST

module R = MITLS.Repr

module R_CH = MITLS.Repr.ClientHello
module CH = Parsers.ClientHello

module R_SH = MITLS.Repr.ServerHello
module SH = Parsers.ServerHello

module R_HS = MITLS.Repr.Handshake
module HSM = Parsers.Handshake

let preorder : LP.srel LP.byte =
  Ghost.hide (LowStar.Buffer.trivial_preorder LP.byte)

assume
val input: LP.slice preorder preorder

let r_ch = r:R_HS.repr input{
  HSM.M_client_hello? (R.value r) /\
  R.fp r == B.loc_buffer LP.(input.base) //loc_slice_from_to doesn't work well
 }

assume
val output: o:LP.slice preorder preorder{
  B.loc_disjoint (LP.loc_slice_from o 0ul)
                 (LP.loc_slice_from input 0ul)
  }
let r_sh = r:R_HS.repr output{
  HSM.M_server_hello? (R.value r) /\
  R.fp r == B.loc_buffer LP.(output.base) //loc_slice_from_to doesn't work well
 }


assume
val receive_client_hello
   (from to : uint_32)
 : Stack r_ch
    (requires fun h ->
      LP.live_slice h input)
    (ensures fun h0 ch h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid ch h1)

assume
val nego (ch: r_ch)
  : Stack r_sh
    (requires fun h ->
      R.valid ch h /\
      LP.live_slice h output)
    (ensures fun h0 sh h1 ->
      B.modifies (R.fp sh) h0 h1 /\
      R.valid sh h1)

assume
val is_hrr (sh:r_sh)
  : Stack bool
    (requires
      R.valid sh)
    (ensures fun h0 b h1 ->
      B.modifies B.loc_none h0 h1 /\
      b == HSL.Transcript.is_hrr (R.value sh))

module TX = HSL.Transcript

assume
val is_psk (ch:r_ch)
  : Stack bool
    (requires
      R.valid ch)
    (ensures fun h0 b h1 ->
      B.modifies B.loc_none h0 h1 /\
      TX.client_hello_has_psk (HSM.M_client_hello?._0 (R.value ch)))

assume
val check_binder
    (#a:_)
    (ch:r_ch)
    (tag:Hacl.Hash.Definitions.hash_t a)
    (chosen_psk_identity:Parsers.PskBinderEntry.pskBinderEntry)
 : Stack bool
   (requires fun h0 ->
     R.valid ch h0 /\
     B.live h0 tag)
   (ensures fun h0 _ h1 ->
     B.modifies B.loc_none h0 h1)

assume
val select_psk_binder_entry
      (ch:r_ch) (sh:r_sh)
   : Stack Parsers.PskBinderEntry.pskBinderEntry
     (requires fun h0 ->
       R.valid ch h0 /\
       R.valid sh h0)
     (ensures fun h0 p h1 ->
       B.modifies B.loc_none h0 h1 /\
       True //maybe say that p is actually in ch?
       )

assume
val hash_len (a:_)
  : Tot (x:uint_32{ UInt32.v x == Spec.Hash.Definitions.hash_length a })

val server (from to:uint_32)
  : ST unit
    (requires fun h ->
      LP.live_slice h input /\
      LP.live_slice h output)
    (ensures fun h0 _ h1 ->
      B.modifies (LP.loc_slice_from output 0ul) h0 h1)

#reset-options
  "--query_stats \
   --print_z3_statistics"
#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit_factor  4"

let server from to
  = push_frame();
    let ch = receive_client_hello from to in
    let sh = nego ch in
    let h1 = get () in
    let cs = R_SH.cipherSuite (R_HS.serverHello sh) in
    let _ =
    match CipherSuite.cipherSuite'_of_name cs with
    | Some (CipherSuite.CipherSuite13 _ hash_alg) ->
      let thash, tx_0 = TX.create Mem.tls_region hash_alg in
      if is_hrr sh
      then let tx1 = TX.extend_hrr thash ch sh tx_0 in
           ()
      else begin
        if is_psk ch
        then let hash, tx_1 = TX.extend_ch_with_psk thash ch tx_0 in
             let psk = select_psk_binder_entry ch sh in
             if check_binder ch hash psk
             then let _ = assume (TX.nego_version
                                    (HSM.M_client_hello?._0 (R.value ch))
                                    (HSM.M_server_hello?._0 (R.value sh))
                                  == Parsers.ProtocolVersion.TLS_1p3) in
                  let tx_2 = TX.extend_hash_hsm thash sh (Ghost.hide (Ghost.reveal tx_1)) in
                  ()
             else ()
        else ()
     end

    | _ -> ()
    in
    pop_frame()

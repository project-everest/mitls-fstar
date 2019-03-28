module Test.HSL.Transcript
module HT = HSL.Transcript
module Receive = HSL.Receive
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer

let preorder : LP.srel LP.byte = Ghost.hide (LowStar.Buffer.trivial_preorder LP.byte)

assume
val input: LP.slice preorder preorder

open FStar.Integers
noeq
type flight_ch = {
  begin_ch: uint_32;
  ch_msg: Ghost.erased Parsers.ClientHello.clientHello
}

module HS = FStar.HyperStack
module HSM = Parsers.Handshake

let valid_flight_ch
  = fun (flt:flight_ch) (flight_begin flight_end:uint_32) (input: LP.slice preorder preorder) (h:HS.mem) ->
      flight_begin < flt.begin_ch /\ flt.begin_ch < flight_end /\
      LP.valid_pos HSM.handshake_parser h input flight_begin flight_end /\
      LP.valid_pos Parsers.ClientHello.clientHello_parser h input flt.begin_ch flight_end /\
      (let msg = LP.contents HSM.handshake_parser h input flight_begin in
       HSM.M_client_hello? msg /\
       Ghost.reveal flt.ch_msg == (HSM.M_client_hello?._0 msg))

open FStar.HyperStack.ST
assume
val receive_client_hello
   (from to : uint_32)
 : Stack flight_ch
    (requires fun h -> True)
    (ensures fun h0 fch h1 ->
      B.modifies B.loc_none h0 h1 /\
      valid_flight_ch fch from to input h1
    )

assume
val output: o:LP.slice preorder preorder{
  B.loc_disjoint (LP.loc_slice_from o 0ul)
                 (LP.loc_slice_from input 0ul)
  }

noeq
type flight_sh = {
  begin_hsm:uint_32;
  begin_sh: uint_32;
  end_sh: uint_32;
  sh_msg: Ghost.erased Parsers.ServerHello.serverHello
}

unfold
let valid_flight_sh
  = fun (flt:flight_sh) (output: LP.slice preorder preorder) (h:HS.mem) ->
      flt.begin_hsm <= flt.begin_sh /\
      flt.begin_sh < flt.end_sh /\
      LP.valid_pos HSM.handshake_parser h output flt.begin_hsm flt.end_sh /\
      LP.valid_pos Parsers.ServerHello.serverHello_parser h output flt.begin_sh flt.end_sh /\
      (let msg = LP.contents HSM.handshake_parser h output flt.begin_hsm in
       HSM.M_server_hello? msg /\
       Ghost.reveal flt.sh_msg == HSM.M_server_hello?._0 msg)

assume
val nego (ch: flight_ch)
  : Stack flight_sh
    (requires fun h ->
      exists from to. valid_flight_ch ch from to input h
    )
    (ensures fun h0 fsh h1 ->
      B.modifies (LP.loc_slice_from_to output fsh.begin_sh fsh.end_sh) h0 h1 /\
      LP.live_slice h1 output /\
      valid_flight_sh fsh output h1)

module LL = LowParse.Low.Base

// #reset-options
//   "--query_stats \
//    --print_z3_statistics \
//    --using_facts_from \
//        '* \
//         -TLSConstants \
//         -Parsers \
//         +Parsers.ClientHello \
//         +Parsers.ServerHello \
//         +Parsers.CipherSuite \
//         +Parsers.Handshake' \
//    --log_queries"

assume
val is_hrr (sh:flight_sh)
  : Stack bool
    (requires fun h ->
      valid_flight_sh sh output h)
    (ensures fun h0 b h1 ->
      B.modifies B.loc_none h0 h1 /\
      b == HSL.Transcript.is_hrr (Ghost.reveal sh.sh_msg))

#reset-options
  "--query_stats \
    --print_z3_statistics \
    --using_facts_from \
         'Prims \
          FStar \
          LowStar \
          LowParse \
          Test.HSL.Transcript \
          HSL \
          CipherSuite \
          +Hacl.Hash.Definitions
          +Parsers.ClientHello \
          +Parsers.ServerHello \
          +Parsers.CipherSuite \
          +Parsers.Handshake'"
#set-options "--max_fuel 0"

let flush (x:nat) = assert (x >= 0)

module TX = HSL.Transcript

assume
val is_psk (ch:flight_ch) (from to:uint_32)
  : Stack bool
    (requires fun h ->
      valid_flight_ch ch from to input h)
    (ensures fun h0 b h1 ->
      B.modifies B.loc_none h0 h1 /\
      TX.client_hello_has_psk (Ghost.reveal ch.ch_msg))

assume
val truncate_at (ch:flight_ch) (from to:uint_32)
  : Stack (uint_32 & Ghost.erased LL.bytes)
    (requires fun h ->
      valid_flight_ch ch from to input h /\
      TX.client_hello_has_psk (Ghost.reveal ch.ch_msg))
    (ensures fun h0 (i, b) h1 ->
      B.modifies B.loc_none h0 h1 /\
      from < i /\ i < to /\
      Ghost.reveal b == LP.bytes_of_slice_from_to h1 input from i)

#set-options "--max_ifuel 0 --z3rlimit_factor 10 --initial_ifuel 0"

assume
val check_binder
    (#a:_)
    (ch:flight_ch)
    (tag:Hacl.Hash.Definitions.hash_t a)
    (chosen_psk_identity:Parsers.PskBinderEntry.pskBinderEntry)
 : Stack bool
   (requires fun h0 ->
     B.live h0 tag)
   (ensures fun h0 _ h1 ->
     B.modifies B.loc_none h0 h1)

assume
val select_psk_binder_entry
      (ch:flight_ch) (from to:uint_32) (sh:flight_sh)
   : Stack Parsers.PskBinderEntry.pskBinderEntry
     (requires fun h0 ->
       valid_flight_ch ch from to input h0 /\
       valid_flight_sh sh output h0)
     (ensures fun h0 p h1 ->
       B.modifies B.loc_none h0 h1 /\
       True //maybe say that p is actually in ch?
       )

assume
val hash_len (a:_)
  : Tot (x:uint_32{ UInt32.v x == Spec.Hash.Definitions.hash_length a })

inline_for_extraction
let new_tag (a:_) :
  StackInline (Hacl.Hash.Definitions.hash_t a)
    (requires fun h0 -> True)
    (ensures fun h0 t h1 ->
      B.modifies B.loc_none h0 h1 /\
      B.live h1 t /\
      B.fresh_loc (B.loc_buffer t) h0 h1)
  = B.malloca 0uy (hash_len a)

#set-options "--z3rlimit_factor 30"
let server (from to:uint_32)
  : ST unit
    (requires fun h ->
      LP.live_slice h input /\
      LP.live_slice h output)
    (ensures fun h0 _ h1 ->
      B.modifies (LP.loc_slice_from output 0ul) h0 h1)
  = push_frame();
    let ch = receive_client_hello from to in
    let sh = nego ch in
    let cipherSuite_pos =
        Parsers.ServerHello.accessor_serverHello_cipher_suite
          output
          sh.begin_sh
    in
    let cipherSuite : Parsers.CipherSuite.cipherSuite =
      Parsers.CipherSuite.cipherSuite_reader
        output
        cipherSuite_pos
    in
    let _ =
    match CipherSuite.cipherSuite'_of_name cipherSuite with
    | Some (CipherSuite.CipherSuite13 _ hash_alg) ->
      let h = get () in
      let thash, tx_0 = TX.create Mem.tls_region hash_alg in
      let h1 = get () in
      if is_hrr sh
      then begin
        let tx_1 = HSL.Transcript.extend_hrr thash input from to output sh.begin_hsm sh.end_sh tx_0 in
        assert (Ghost.reveal tx_1 == TX.Start (Some (Ghost.reveal ch.ch_msg, Ghost.reveal sh.sh_msg)));
        ()
      end
      else begin
        if is_psk ch from to
        then let tch_i, tch_b = truncate_at ch from to in
             let tx_1 = TX.extend_tch thash input from tch_i tx_0 in
             assert (Ghost.reveal tx_1 == TX.TruncatedClientHello None (Ghost.reveal tch_b));
             let h = get () in
             TX.elim_invariant thash (Ghost.reveal tx_1) h;
//             assert (TX.invariant thash (Ghost.reveal tx_1) h);
             // assume (B.loc_not_unused_in h `B.loc_includes` TX.footprint thash);
             let tag = new_tag hash_alg in
             B.loc_unused_in_not_unused_in_disjoint h;
             assert (B.loc_unused_in h `B.loc_disjoint` B.loc_not_unused_in h);
             assert (B.loc_unused_in h `B.loc_includes` B.loc_buffer tag);
             B.loc_disjoint_includes
               (B.loc_unused_in h)
               (B.loc_not_unused_in h)
               (B.loc_buffer tag)
               (TX.footprint thash);
             TX.extract_hash thash tag tx_1;
             let psk = select_psk_binder_entry ch from to sh in
             let h2 = get () in
             if check_binder ch tag psk
             then ()
             else ()
      end

    | _ -> ()
    in
    pop_frame ()


    //   else begin
    //       if is_psk ch
    //       then let tx = TX.extend_tch thash input from (compute_tch_index input ch) in
    //            let tch_hash = extract thash in
    //            if not (binder.verify tch_hash (get_selected_binder ch sh.selected_binder))
    //            then Error
    //            else let tx = extend_tch_binders input (compute_tch_index input ch) to in
    //               //state of thash = hash ch
    //                 tx
    //      else extend_hash_hsm input from to  //state of hash = hash ch
    //     in

    //   end
    // | _ -> ()

    //     let tx =
    //       if is_psk ch sh
    //       then let tx = extend_tch thash input from (compute_tch_index input ch) in
    //            let tch_hash = extract thash in
    //            if not (binder.verify tch_hash (get_selected_binder ch sh.selected_binder))
    //            then Error
    //            else let tx = extend_tch_binders input (compute_tch_index input ch) to in
    //               //state of thash = hash ch
    //                 tx
    //      else extend_hash_hsm input from to  //state of hash = hash ch
    //     in
    //     let tx = extend_hash_hsm13 output sh.begin_hsm sh.end_sh in
    //     ()


    // | _ -> ()


// //     | _ ->
// //       Error

//     | _ -> ()

// let flush2 (x:nat) = assert (x >= 0)
// let flush3 (x:nat) = assert (x >= 0)


// // --------------------------------------------------------------------------------

// //  ch = [ prefix ; id1..idn; b1...bn ]

// //  tch = [ prefix ; id1..idn]

// //  bi = HMAC(binder_key_i, tch)



// // // let server2 (from to:uint_32)
// // //   : ST unit
// // //     (requires fun h ->
// // //       LP.live_slice h input /\
// // //       LP.live_slice h output)
// // //     (ensures fun h0 _ h1 ->
// // //       B.modifies (LP.loc_slice_from output 0ul) h0 h1)
// // //   = let ch = receive_client_hello from to in
// // //     let sh = nego ch in
// // //     let h0 = get () in
// // //     // assert (LP.valid_pos HSM.handshake_parser h0 output sh.begin_hsm sh.end_sh);
// // // //    assert (trigger (LP.get_valid_pos HSM.handshake_parser h0 output sh.begin_hsm));
// // //       let cipherSuite_pos =
// // //         Parsers.ServerHello.accessor_serverHello_cipher_suite
// // //           output
// // //           sh.begin_sh
// // //       in
// // //       let h1 = get () in
// // //       //LL.valid_frame HSM.handshake_parser h0 output sh.begin_hsm B.loc_none h1;
// // //       // assume (LP.valid_content_pos HSM.handshake_parser h1 output sh.begin_hsm
// // //       //                              (LP.contents HSM.handshake_parser h0 output sh.begin_hsm)
// // //       //                              sh.end_sh);
// // //       // assert (sh.end_sh == LP.get_valid_pos HSM.handshake_parser h1 output sh.begin_hsm);
// // //       // assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh);
// // //       // admit()
// // //       // test_frame HSM.handshake_parser h0 sh.begin_hsm B.loc_none h1;
// // //       // assert (LP.valid HSM.handshake_parser h0 output sh.begin_hsm);
// // //       // assert (B.modifies B.loc_none h0 h1);
// // //       assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh)


// // let server3 (from to:uint_32)
// //   : ST unit
// //     (requires fun h ->
// //       LP.live_slice h input /\
// //       LP.live_slice h output)
// //     (ensures fun h0 _ h1 ->
// //       B.modifies (LP.loc_slice_from output 0ul) h0 h1)
// //   = let ch = receive_client_hello from to in
// //     let sh = nego ch in
// //     let h0 = get () in
// //     // assert (LP.valid_pos HSM.handshake_parser h0 output sh.begin_hsm sh.end_sh);
// // //    assert (trigger (LP.get_valid_pos HSM.handshake_parser h0 output sh.begin_hsm));
// //       let cipherSuite_pos =
// //         Parsers.ServerHello.accessor_serverHello_cipher_suite
// //           output
// //           sh.begin_sh
// //       in
// //       let h1 = get () in
// //       //LL.valid_frame HSM.handshake_parser h0 output sh.begin_hsm B.loc_none h1;
// //       // assume (LP.valid_content_pos HSM.handshake_parser h1 output sh.begin_hsm
// //       //                              (LP.contents HSM.handshake_parser h0 output sh.begin_hsm)
// //       //                              sh.end_sh);
// //       // assert (sh.end_sh == LP.get_valid_pos HSM.handshake_parser h1 output sh.begin_hsm);
// //       // assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh);
// //       // admit()
// //       // test_frame HSM.handshake_parser h0 sh.begin_hsm B.loc_none h1;
// //       // assert (LP.valid HSM.handshake_parser h0 output sh.begin_hsm);
// //       // assert (B.modifies B.loc_none h0 h1);
// //       assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh)


// // let server4 (from to:uint_32)
// //   : ST unit
// //     (requires fun h ->
// //       LP.live_slice h input /\
// //       LP.live_slice h output)
// //     (ensures fun h0 _ h1 ->
// //       B.modifies (LP.loc_slice_from output 0ul) h0 h1)
// //   = let ch = receive_client_hello from to in
// //     let sh = nego ch in
// //     let h0 = get () in
// //     // assert (LP.valid_pos HSM.handshake_parser h0 output sh.begin_hsm sh.end_sh);
// // //    assert (trigger (LP.get_valid_pos HSM.handshake_parser h0 output sh.begin_hsm));
// //       let cipherSuite_pos =
// //         Parsers.ServerHello.accessor_serverHello_cipher_suite
// //           output
// //           sh.begin_sh
// //       in
// //       let h1 = get () in
// //       //LL.valid_frame HSM.handshake_parser h0 output sh.begin_hsm B.loc_none h1;
// //       // assume (LP.valid_content_pos HSM.handshake_parser h1 output sh.begin_hsm
// //       //                              (LP.contents HSM.handshake_parser h0 output sh.begin_hsm)
// //       //                              sh.end_sh);
// //       // assert (sh.end_sh == LP.get_valid_pos HSM.handshake_parser h1 output sh.begin_hsm);
// //       // assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh);
// //       // admit()
// //       // test_frame HSM.handshake_parser h0 sh.begin_hsm B.loc_none h1;
// //       // assert (LP.valid HSM.handshake_parser h0 output sh.begin_hsm);
// //       // assert (B.modifies B.loc_none h0 h1);
// //       assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh)

// // #reset-options
// //   "--query_stats \
// //     --print_z3_statistics \
// //     --log_queries \
// //     --using_facts_from \
// //          '* \
// //           -TLSConstants \
// //           -Parsers \
// //           +Parsers.ClientHello \
// //           +Parsers.ServerHello \
// //           +Parsers.CipherSuite \
// //           +Parsers.Handshake'"

// // let server5 (from to:uint_32)
// //   : ST unit
// //     (requires fun h ->
// //       LP.live_slice h input /\
// //       LP.live_slice h output)
// //     (ensures fun h0 _ h1 ->
// //       B.modifies (LP.loc_slice_from output 0ul) h0 h1)
// //   = let ch = receive_client_hello from to in
// //     let sh = nego ch in
// //     let h0 = get () in
// //     // assert (LP.valid_pos HSM.handshake_parser h0 output sh.begin_hsm sh.end_sh);
// // //    assert (trigger (LP.get_valid_pos HSM.handshake_parser h0 output sh.begin_hsm));
// //       let cipherSuite_pos =
// //         Parsers.ServerHello.accessor_serverHello_cipher_suite
// //           output
// //           sh.begin_sh
// //       in
// //       let h1 = get () in
// //       //LL.valid_frame HSM.handshake_parser h0 output sh.begin_hsm B.loc_none h1;
// //       // assume (LP.valid_content_pos HSM.handshake_parser h1 output sh.begin_hsm
// //       //                              (LP.contents HSM.handshake_parser h0 output sh.begin_hsm)
// //       //                              sh.end_sh);
// //       // assert (sh.end_sh == LP.get_valid_pos HSM.handshake_parser h1 output sh.begin_hsm);
// //       // assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh);
// //       // admit()
// //       // test_frame HSM.handshake_parser h0 sh.begin_hsm B.loc_none h1;
// //       // assert (LP.valid HSM.handshake_parser h0 output sh.begin_hsm);
// //       // assert (B.modifies B.loc_none h0 h1);
// //       assert (LP.valid_pos HSM.handshake_parser h1 output sh.begin_hsm sh.end_sh)



// // let test4 (x:nat) = assert (x >= 0)
// //     //   ;
// //     //   admit()
// //     // let cipherSuite : Parsers.CipherSuite.cipherSuite =
// //     //   Parsers.CipherSuite.cipherSuite_reader
// //     //     output
// //     //     cipherSuite_pos
// //     // in
// //     // match CipherSuite.cipherSuite'_of_name cipherSuite with
// //     // | Some (CipherSuite.CipherSuite13 _ hash_alg) ->
// //     //   let h = get () in
// //     //   assert (valid_flight_sh sh output h);
// //     //   admit();
// //     //   let tx = HSL.Transcript.create Mem.tls_region hash_alg in
// //     //   if is_hrr sh
// //     //   then ()
// //     //   else ()
// //     // | _ ->
// //     //   ()

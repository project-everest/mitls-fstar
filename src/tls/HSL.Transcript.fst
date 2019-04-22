module HSL.Transcript
open FStar.Integers
open FStar.HyperStack.ST
module List = FStar.List.Tot
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13

module PV = Parsers.ProtocolVersion
module LP = LowParse.Low.Base
module IncHash = EverCrypt.Hash.Incremental

module R = MITLS.Repr
module R_HS = MITLS.Repr.Handshake

module R_CH = MITLS.Repr.ClientHello
module CH = Parsers.ClientHello

module R_SH = MITLS.Repr.ServerHello
module SH = Parsers.ServerHello

let is_hrr _ = false

let nego_version _ _ = admit ()
let transcript_bytes _ = admit ()
let state _ = admit ()
let invariant #_ _ _ _ = admit ()
let footprint #_ _ = admit ()
let elim_invariant #_ _ _ _ = admit ()
let region_of #_ _ = admit ()
let frame_invariant #_ _ _ _ _ _ = admit ()
let create _ _ = admit ()
let extend_hsm #_ _ #_ _ _ = admit ()
let extend_hsm12 #_ _ #_ _ _ = admit ()
let extend_hsm13 #_ _ #_ _ _ = admit ()
let extend_ch_with_psk #_ _ #_ _ _ = admit ()
let extend_hrr #_ _ #_ _ #_ _ _ = admit ()
let extend_hash #_ _ _ _ = admit ()
let extract_hash #_ _ _ _ = admit ()
let injectivity _ _ _ = admit ()

// assume
// val serialize (#pk:_) (#t:_) (#p:LP.parser pk t) (s:LP.serializer p)
//               (x:t)
//   : GTot (b:bytes{Seq.length b < max_message_size})

// let rec serialize_list (#pk:_) (#t:_) (#p:LP.parser pk t) (s:LP.serializer p)
//                        (x:list t)
//   : GTot (b:bytes{Seq.length b <= List.Tot.length x * max_message_size})
//   = match x with
//     | [] -> Seq.empty
//     | hd::tl -> serialize s hd `Seq.append` serialize_list s tl

// let transcript_bytes (t:transcript_t)
//   : GTot (b:bytes {
//     Seq.length b <= (max_transcript_size + 4) * max_message_size
//     })
//   =
//   let serialize_retry (r:option retry)
//     : GTot (b:bytes{Seq.length b < 2 * max_message_size })
//     =
//     match r with
//     | None -> Seq.empty
//     | Some (ch, sh) ->
//       serialize HSM.handshake_serializer ch `Seq.append`
//       serialize HSM.handshake_serializer sh
//   in
//   match t with
//   | Start r ->
//     serialize_retry r

//   | Hello r ch ->
//     serialize_retry r `Seq.append`
//     serialize HSM.handshake_serializer ch

//   | Transcript12 ch sh rest ->
//     serialize HSM.handshake_serializer ch `Seq.append`
//     serialize HSM.handshake_serializer sh `Seq.append`
//     serialize_list HSM12.handshake12_serializer rest

//   | Transcript13 retry ch sh rest ->
//     serialize_retry retry `Seq.append`
//     serialize HSM.handshake_serializer ch `Seq.append`
//     serialize HSM.handshake_serializer sh `Seq.append`
//     serialize_list HSM13.handshake13_serializer rest

// let transcript_bytes_injective (t1 t2:transcript_t)
//   : Lemma
//     (requires
//       transcript_bytes t1 `Seq.equal` transcript_bytes t2)
//     (ensures
//       t1 == t2)
//   = admit()

// noeq
// type state (a:alg) = {
//   region:Mem.rgn;
//   loc: Ghost.erased B.loc;
//   hash_state: IncHash.state a
// }

// let invariant (#a:alg) (s:state a) (tx:transcript_t) (h:HS.mem) =
//   IncHash.hashes h s.hash_state (transcript_bytes tx) /\
//   B.loc_region_only true s.region `B.loc_includes` Ghost.reveal s.loc /\
//   Ghost.reveal s.loc == IncHash.footprint s.hash_state h /\
//   B.loc_not_unused_in h `B.loc_includes` Ghost.reveal s.loc

// let footprint (#a:alg) (s:state a) = Ghost.reveal s.loc

// let elim_invariant #a s t h = ()

// let region_of #a s = s.region

// let frame_invariant (#a:_) (s:state a) (t: transcript_t) (h0 h1:HS.mem) (l:B.loc) =
//   IncHash.modifies_disjoint_preserves l h0 h1 s.hash_state

// #set-options "--max_fuel 0 --max_ifuel  1 --initial_ifuel  1"
// let create r a =
//   let h0 = get() in
//   let s = IncHash.create_in a r in
//   let h1 = get () in
//   {region=r;
//    loc=Ghost.hide (IncHash.footprint s h1);
//    hash_state=s},
//   Ghost.hide (Start None)


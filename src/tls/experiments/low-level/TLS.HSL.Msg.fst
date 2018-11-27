module TLS.HSL.Msg

open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

type msg' = (U32.t * U32.t)

inline_for_extraction let synth_msg (x: msg') : msg =
  let (x, y) = x in
  {
    x = x;
    y = y;
  }

inline_for_extraction let synth_msg_recip (x: msg) : msg' =
  (x.x, x.y)

#push-options "--initial_ifuel 2 --max_ifuel 2"
let synth_msg_injective' (x x':msg') : Lemma (synth_msg x == synth_msg x' ==> x == x') = ()
#pop-options

let synth_msg_injective () : Lemma (LP.synth_injective synth_msg) =
  FStar.Classical.forall_intro_2 synth_msg_injective'

let synth_msg_inverse () : Lemma (LP.synth_inverse synth_msg synth_msg_recip) =
  assert_norm (LP.synth_inverse synth_msg synth_msg_recip)

noextract let msg'_parser : LP.parser _ msg' =
  LP.parse_u32
  `LP.nondep_then` LP.parse_u32

noextract let msg'_parser_kind = LP.get_parser_kind msg'_parser

let msg_parser =
  synth_msg_injective ();
  assert_norm (msg_parser_kind == msg'_parser_kind);
  msg'_parser `LP.parse_synth` synth_msg

noextract let msg'_serializer : LP.serializer msg'_parser =
  LP.serialize_nondep_then _ (LP.serialize_u32) ()
  _ LP.serialize_u32

let msg_serializer =
  [@inline_let] let _ = synth_msg_injective () in
  [@inline_let] let _ = synth_msg_inverse () in
  [@inline_let] let _ = assert_norm (msg_parser_kind == msg'_parser_kind) in
  LP.serialize_synth _ synth_msg msg'_serializer synth_msg_recip ()

inline_for_extraction let msg'_parser32 : LP.parser32 msg'_parser =
  LP.parse32_u32
  `LP.parse32_nondep_then` LP.parse32_u32

inline_for_extraction let msg_parser32 =
  [@inline_let] let _ = synth_msg_injective () in
  [@inline_let] let _ = assert_norm (msg_parser_kind == msg'_parser_kind) in
  LP.parse32_synth _ synth_msg (fun x -> synth_msg x) msg'_parser32 ()

inline_for_extraction let msg'_serializer32 : LP.serializer32 msg'_serializer =
  LP.serialize32_nondep_then (LP.serialize32_u32) ()
  LP.serialize32_u32 ()

inline_for_extraction let msg_serializer32 =
  [@inline_let] let _ = synth_msg_injective () in
  [@inline_let] let _ = synth_msg_inverse () in
  [@inline_let] let _ = assert_norm (msg_parser_kind == msg'_parser_kind) in
  LP.serialize32_synth _ synth_msg _ msg'_serializer32 synth_msg_recip (fun x -> synth_msg_recip x) ()

inline_for_extraction let msg'_size32 : LP.size32 msg'_serializer =
  LP.size32_nondep_then (LP.size32_u32) ()
  (LP.size32_u32)

let msg_size32 =
  [@inline_let] let _ = synth_msg_injective () in
  [@inline_let] let _ = synth_msg_inverse () in
  [@inline_let] let _ = assert_norm (msg_parser_kind == msg'_parser_kind) in
  LP.size32_synth _ synth_msg _ msg'_size32 synth_msg_recip (fun x -> synth_msg_recip x) ()


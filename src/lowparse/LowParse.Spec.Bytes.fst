module LowParse.Spec.Bytes
include LowParse.Spec.VLData

module B32 = FStar.Bytes
module Seq = FStar.Seq
module U32 = FStar.UInt32

#set-options "--z3rlimit 128 --max_fuel 64 --max_ifuel 64"

let lt_pow2_32
  (x: nat)
: Lemma
  (x < 4294967296 <==> x < pow2 32)
= ()

#reset-options

let parse_flbytes_gen
  (sz: nat { sz < 4294967296 } )
  (s: bytes { Seq.length s == sz } )
: GTot (B32.lbytes sz)
= lt_pow2_32 sz;
  B32.hide s

let parse_flbytes
  (sz: nat { sz < 4294967296 } )
: Tot (parser (total_constant_size_parser_kind sz) (B32.lbytes sz))
= make_total_constant_size_parser sz (B32.lbytes sz) (parse_flbytes_gen sz)

let serialize_flbytes'
  (sz: nat { sz < 4294967296 } )
: Tot (bare_serializer (B32.lbytes sz))
= fun (x: B32.lbytes sz) -> (
    lt_pow2_32 sz;
    B32.reveal x
  )

let serialize_flbytes_correct
  (sz: nat { sz < 4294967296 } )
: Lemma
  (serializer_correct (parse_flbytes sz) (serialize_flbytes' sz))
= let prf
    (input: B32.lbytes sz)
  : Lemma
    (
      let ser = serialize_flbytes' sz input in
      Seq.length ser == sz /\
      parse (parse_flbytes sz) ser == Some (input, sz)
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_flbytes
  (sz: nat { sz < 4294967296 } )
: Tot (serializer (parse_flbytes sz))
= serialize_flbytes_correct sz;
  serialize_flbytes' sz

(* VLBytes *)

(* For the payload: since the input buffer is truncated at the time of
reading the length header, "parsing" the payload will always succeed,
by just returning it unchanged (unless the length of the input
is greater than 2^32) *)

let parse_all_bytes_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = {
      parser_kind_metadata_total = false;
    };
    parser_kind_subkind = Some ParserConsumesAll;
  }

let parse_all_bytes'
  (input: bytes)
: GTot (option (B32.bytes * consumed_length input))
= let len = Seq.length input in
  if len >= 4294967296
  then None
  else begin
    lt_pow2_32 len;
    Some (B32.hide input, len)
  end

#set-options "--z3rlimit 16"

let parse_all_bytes_injective () : Lemma
  (injective parse_all_bytes')
= let prf
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond parse_all_bytes' b1 b2))
    (ensures (injective_postcond parse_all_bytes' b1 b2))
  = assert (Seq.length b1 < 4294967296);
    assert (Seq.length b2 < 4294967296);
    lt_pow2_32 (Seq.length b1);
    lt_pow2_32 (Seq.length b2);
    B32.reveal_hide b1;
    B32.reveal_hide b2
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x))

#reset-options

let parse_all_bytes_correct () : Lemma
  (parser_kind_prop parse_all_bytes_kind parse_all_bytes')
= parse_all_bytes_injective ();
  injective_consumes_all_no_lookahead_weak parse_all_bytes'

let parse_all_bytes : parser parse_all_bytes_kind B32.bytes =
  parse_all_bytes_correct ();
  parse_all_bytes'

let serialize_all_bytes'
  (input: B32.bytes)
: GTot bytes
= B32.reveal input

#set-options "--z3rlimit 32"

let serialize_all_bytes_correct () : Lemma (serializer_correct parse_all_bytes serialize_all_bytes') =
  let prf
    (input: B32.bytes)
  : Lemma
    (
      let ser = serialize_all_bytes' input in
      let len : consumed_length ser = Seq.length ser in
      parse parse_all_bytes ser == Some (input, len)
    )
  = assert (Seq.length (serialize_all_bytes' input) == B32.length input);
    lt_pow2_32 (B32.length input);
    B32.hide_reveal input
  in
  Classical.forall_intro prf

#reset-options

let serialize_all_bytes : serializer parse_all_bytes =
  serialize_all_bytes_correct ();
  serialize_all_bytes'

let parse_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes))
= parse_bounded_vldata_strong min max serialize_all_bytes

let parse_bounded_vlbytes_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: B32.bytes)
: GTot Type0
= let reslen = B32.length x in
  min <= reslen /\ reslen <= max

let parse_bounded_vlbytes_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot Type0
= (x: B32.bytes { parse_bounded_vlbytes_pred min max x } )

let synth_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (x: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
: Tot (parse_bounded_vlbytes_t min max)
= x

let parse_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vlbytes_t min max))
= parse_synth (parse_bounded_vlbytes' min max) (synth_bounded_vlbytes min max)

let serialize_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (serializer (parse_bounded_vlbytes' min max))
= serialize_bounded_vldata_strong min max serialize_all_bytes

let serialize_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (serializer (parse_bounded_vlbytes min max))
= serialize_synth
    (parse_bounded_vlbytes' min max)
    (synth_bounded_vlbytes min max)
    (serialize_bounded_vlbytes' min max)
    (fun (x: parse_bounded_vlbytes_t min max) ->
      (x <: parse_bounded_vldata_strong_t min max #_ #_ #parse_all_bytes serialize_all_bytes)
    )
    ()

module LowParse.Spec.VLData.Header

module U32 = FStar.UInt32
module E = LowParse.BigEndian

#reset-options "--z3cliopt smt.arith.nl=false --using_facts_from '*  -FStar.UInt8 -FStar.UInt16' --z3rlimit 32"

let integer_size_values i = ()

#reset-options

let decode_bounded_integer i b
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

#set-options "--z3rlimit 16"
let decode_bounded_integer_injective'
  (i: integer_size)
  (b1: bytes { Seq.length b1 == i } )
  (b2: bytes { Seq.length b2 == i } )
: Lemma
  (decode_bounded_integer i b1 == decode_bounded_integer i b2 ==> Seq.equal b1 b2)
= if decode_bounded_integer i b1 = decode_bounded_integer i b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    E.be_to_n_inj b1 b2
  end else ()
#reset-options

let decode_bounded_integer_injective i
= Classical.forall_intro_2 (decode_bounded_integer_injective' i)

let serialize_bounded_integer'
  (sz: integer_size)
: Tot (bare_serializer (bounded_integer sz))
= (fun (x: bounded_integer sz) ->
    let res = E.n_to_be (U32.uint_to_t sz) (U32.v x) in
    res
  )

let serialize_bounded_integer_correct
  (sz: integer_size)
: Lemma
  (serializer_correct (parse_bounded_integer sz) (serialize_bounded_integer' sz))
= let prf
    (x: bounded_integer sz)
  : Lemma
    (
      let res = serialize_bounded_integer' sz x in
      Seq.length res == (sz <: nat) /\
      parse (parse_bounded_integer sz) res == Some (x, (sz <: nat))
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_bounded_integer sz
= serialize_bounded_integer_correct sz;
  serialize_bounded_integer' sz

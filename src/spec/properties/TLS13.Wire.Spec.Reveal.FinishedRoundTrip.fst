module TLS13.Wire.Spec.Reveal.FinishedRoundTrip

friend TLS13.Wire.Generated.Finished
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module GHS = TLS13.Wire.Generated.Handshake
module GFin = TLS13.Wire.Generated.Finished
module LP = LowParse.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(* Converse round-trip: a fragment that parses as a Finished handshake message
   re-serializes to exactly that fragment.  The generated parser is injective
   (LowParse [parsed_data_is_serialize]) and [serialize_handshake (M.Finished fin)]
   unfolds (via [friend TLS13.Wire.Spec]) to the generated serializer applied to
   [Body_finished fin], so the two coincide. *)
#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_parse_finished_handshake_round_trip fragment fin =
  match LP.parse GHS.handshake_parser fragment with
  | Some (h, consumed) ->
    if consumed = B.length fragment then
      begin
        LP.parsed_data_is_serialize GHS.handshake_serializer fragment;
        Seq.lemma_eq_intro
          (Seq.slice fragment consumed (B.length fragment))
          B.empty;
        Seq.lemma_eq_intro
          (Seq.append (LP.serialize GHS.handshake_serializer h)
                      (Seq.slice fragment consumed (B.length fragment)))
          (LP.serialize GHS.handshake_serializer h);
        match h with
        | GHS.Body_finished vd ->
          assert (fin == vd);
          assert (WS.serialize_handshake (M.Finished fin) ==
                  LP.serialize GHS.handshake_serializer h);
          Seq.lemma_eq_elim
            fragment
            (WS.serialize_handshake (M.Finished fin))
        | _ -> assert False
      end
    else assert False
  | None -> assert False
#pop-options

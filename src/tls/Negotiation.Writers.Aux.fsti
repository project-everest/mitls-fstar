module Negotiation.Writers.Aux

module LWP = LowParseWriters.Parsers
module LPI = LowParse.Low.Int

val valid_pskBinderEntry_intro : LWP.valid_synth_t (LWP.parse_vlbytes 32ul 255ul) Parsers.PskBinderEntry.lwp_pskBinderEntry (fun _ -> True) (fun x -> x)

val valid_pskIdentity_intro : LWP.valid_synth_t (Parsers.PskIdentity.lwp_pskIdentity_identity `LWP.star` LWP.parse_u32) Parsers.PskIdentity.lwp_pskIdentity (fun _ -> True) (fun (identity, age) -> { Parsers.PskIdentity.identity = identity; Parsers.PskIdentity.obfuscated_ticket_age = age; })

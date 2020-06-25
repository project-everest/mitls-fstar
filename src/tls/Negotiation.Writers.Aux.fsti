module Negotiation.Writers.Aux

module LWP = LowParseWriters.Parsers

val valid_pskBinderEntry_intro : LWP.valid_synth_t (LWP.parse_vlbytes 32ul 255ul) Parsers.PskBinderEntry.lwp_pskBinderEntry (fun _ -> True) (fun x -> x)



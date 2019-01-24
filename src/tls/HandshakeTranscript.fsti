module HandshakeTranscript

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module C = TLSConstants
module Hash = Hashing
module HashSpec = Hashing.Spec
module HSM = HandshakeMessages

module LP = LowParse.Low.Base
open HandshakeLog.Common

let transcript_t = list HSM.hs_msg
let transcript_bytes (t:transcript_t) : GTot hbytes =
  List.fold_right_gtot t (fun x a -> Seq.append (format_hs_msg x) a) Seq.empty

val state : Type0

val region_of : state -> GTot Mem.rgn

val footprint : state -> HS.mem -> GTot B.loc

val transcript : state -> HS.mem -> GTot transcript_t

/// Hashing algorithm in use

val hash_alg : state -> HS.mem -> GTot (option Hash.alg)

let region_includes r l = B.loc_regions true (Set.singleton r) `B.loc_includes` l

val invariant : state -> HS.mem -> prop

val framing (s:state) (l:B.loc) (h0 h1: HS.mem)
  : Lemma
      (requires
        B.modifies l h0 h1 /\
        B.loc_disjoint l (footprint s h0) /\
        invariant s h0)
      (ensures
        hash_alg s h0 == hash_alg s h1 /\
        footprint s h0 == footprint s h1 /\
        transcript s h0 == transcript s h1 /\
        invariant s h1)


val create (r:Mem.rgn)
  : ST state
       (requires fun _ -> True)
       (ensures fun h0 s h1 ->
         let open B in
         invariant s h1 /\
         region_of s == r /\
         modifies loc_none h0 h1 /\
         fresh_loc (footprint s h1) h0 h1 /\
         r `region_includes` footprint s h1 /\
	 hash_alg s h1 == None /\
	 transcript s h1 == [])

val set_hash_alg (a:Hash.alg) (s:state)
  : ST unit
       (requires fun h ->
         invariant s h /\
         hash_alg s h == None)
       (ensures fun h0 _ h1 ->
         let open B in
         invariant s h1 /\
	 hash_alg s h1 == Some a /\
	 transcript s h1 == transcript s h0 /\
         (exists l. fresh_loc l h0 h1 /\
               footprint s h1 == B.loc_union l (footprint s h0) /\
               region_of s `region_includes` footprint s h1))

let extend_transcript (s:state) (msg:HSM.hs_msg) (h:HS.mem) =
  match hash_alg s h with
  | None -> []
  | Some _ -> msg :: transcript s h

val extend_hash (s:state)
                (b:B.buffer uint_8)
                (p0:uint_32{p0 <= B.len b})
                (p1:uint_32{p0 <= p1 /\ p1 <= B.len b})
                (msg:G.erased HSM.hs_msg)
  : ST unit
       (requires fun h ->
         invariant s h /\
         valid_parsing (G.reveal msg) p0 p1 b h)
       (ensures (fun h0 _ h1 ->
         invariant s h0 /\
         footprint s h0 == footprint s h1 /\
         hash_alg s h1 == hash_alg s h0 /\
         transcript s h1 == extend_transcript s (G.reveal msg) h0))

val buf_is_hash_of_b (a:Hash.alg) (buf:Hacl.Hash.Definitions.hash_t a) (b:hbytes) : prop
val extract_hash (#a:Hash.alg) (s:state) (tag:Hacl.Hash.Definitions.hash_t a)
  : ST unit (fun h0 ->
             invariant s h0 /\
             hash_alg s h0 == Some a /\
             B.live h0 tag /\
             B.loc_disjoint (footprint s h0) (B.loc_buffer tag))
            (fun h0 _ h1 ->
             let open B in
             invariant s h1 /\
             modifies (B.loc_buffer tag) h0 h1 /\
             buf_is_hash_of_b a tag (transcript_bytes (transcript s h1)))

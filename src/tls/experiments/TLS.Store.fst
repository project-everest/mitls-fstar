module TLS.Store

module B = LowStar.Buffer

module AE = Crypto.AE

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let store_regions : (l:list Mem.substore{List.Tot.length l == 4 /\ Mem.r_pairwise_disjoint l})
  = Mem.r_disjoint_alloc _ _ 4

module HS = FStar.HyperStack

#push-options "--z3rlimit 40 --max_fuel 4  --max_ifuel 0"

val store_regions_disjoint: i:nat{i < 4} -> j:nat{j < 4} -> Lemma
  (requires i <> j)
  (ensures  (List.Tot.index store_regions i) `HS.disjoint` (List.Tot.index store_regions j))
  [SMTPat (List.Tot.index store_regions i); SMTPat (List.Tot.index store_regions j)]

let store_regions_disjoint i j = ()

#pop-options

let tls_store_server_cookie_region = List.Tot.index store_regions 0
let tls_store_server_ticket_region = List.Tot.index store_regions 1
let tls_store_wrap_psk_region = List.Tot.index store_regions 2
let tls_store_client_seal_region = List.Tot.index store_regions 3

let tls_store_regions (u: usage) : Tot Mem.substore =
  match u with
  | ServerCookie -> tls_store_server_cookie_region
  | ServerTicket -> tls_store_server_ticket_region
  | ClientSeal -> tls_store_client_seal_region
  | WrapPSK -> tls_store_wrap_psk_region

let loc_store_regions (u: usage) : GTot B.loc = B.loc_all_regions_from true (tls_store_regions u)

let loc_store_regions_disjoint' (u1 u2: usage) : Lemma
  (requires (u1 <> u2))
  (ensures (B.loc_disjoint (loc_store_regions u1) (loc_store_regions u2)))
  [SMTPat (B.loc_disjoint (loc_store_regions u1) (loc_store_regions u2))]
= ()

assume val server_cookie_phi : AE.plain_pred 
assume val server_ticket_phi : AE.plain_pred 

let phi (u: usage) : Tot AE.plain_pred =
  match u with
  | ServerCookie -> server_cookie_phi
  | ServerTicket -> server_ticket_phi
  | _ -> server_cookie_phi

inline_for_extraction
noextract
let ptr (u: usage) : Tot Type0 =
  (ptr: B.pointer (option (a: alg & (st: AE.state a (phi u) { B.loc_includes (loc_store_regions u) (AE.footprint st) }))) {
    B.recallable ptr /\
    B.frameOf ptr == tls_store_regions u
  })

let server_cookie_key : ptr ServerCookie =
  B.gcmalloc tls_store_server_cookie_region None 1ul

let server_ticket_key : ptr ServerTicket =
  B.gcmalloc tls_store_server_ticket_region None 1ul

let wrap_psk_key : ptr WrapPSK =
  B.gcmalloc tls_store_wrap_psk_region None 1ul

let client_seal_key : ptr ClientSeal =
  B.gcmalloc tls_store_client_seal_region None 1ul

inline_for_extraction
let keyptr (u: usage) : Tot (ptr u) =
  match u with
  | ServerCookie -> server_cookie_key
  | ServerTicket -> server_ticket_key
  | WrapPSK -> wrap_psk_key
  | ClientSeal -> client_seal_key

let keyptr_recallable (u: usage) : Lemma
  (B.recallable (keyptr u))
  [SMTPat (B.recallable (keyptr u))]
= ()

module HST = FStar.HyperStack.ST

let per_usage_inv (h: HS.mem) (u: usage) : Tot Type0 =
  B.live h (keyptr u) /\
  begin match B.deref h (keyptr u) with
  | None -> True
  | Some (| a, st |) ->
    B.loc_disjoint (AE.footprint st) (B.loc_buffer (keyptr u)) /\
    AE.invariant h st
  end

unfold
let inv' (h: HS.mem) : Tot Type0 =
  per_usage_inv h ServerCookie /\
  per_usage_inv h ServerTicket /\
  per_usage_inv h WrapPSK /\
  per_usage_inv h ClientSeal

let inv = inv'

let per_usage_frame'
  (u u': usage)
  (h: HS.mem)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    u <> u' /\
    per_usage_inv h u' /\
    B.modifies (loc_store_regions u `B.loc_union` l) h h' /\
    B.loc_disjoint l (Mem.loc_store_region ())
  ))
  (ensures (per_usage_inv h' u'))
= assert (Mem.loc_store_region () `B.loc_includes` B.loc_buffer (keyptr u));
  assert (Mem.loc_store_region () `B.loc_includes` B.loc_buffer (keyptr u'));
  begin match B.deref h (keyptr u') with
  | None -> ()
  | Some (| a, st |) ->
    assert (Mem.loc_store_region () `B.loc_includes` AE.footprint st);
    AE.frame_invariant h st (loc_store_regions u `B.loc_union` l) h'
  end

let per_usage_frame
  (u: usage)
  (h: HS.mem)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    inv h /\
    B.modifies (loc_store_regions u `B.loc_union` l) h h' /\
    B.loc_disjoint l (Mem.loc_store_region ()) /\
    per_usage_inv h' u
  ))
  (ensures (inv h'))
= match u with
  | ServerCookie ->
    per_usage_frame' ServerCookie WrapPSK h l h';
    per_usage_frame' ServerCookie ServerTicket h l h';
    per_usage_frame' ServerCookie ClientSeal h l h'
  | ServerTicket ->
    per_usage_frame' ServerTicket WrapPSK h l h';
    per_usage_frame' ServerTicket ServerCookie h l h';
    per_usage_frame' ServerTicket ClientSeal h l h'
  | WrapPSK ->
    per_usage_frame' WrapPSK ServerTicket h l h';
    per_usage_frame' WrapPSK ServerCookie h l h';
    per_usage_frame' WrapPSK ClientSeal h l h'
  | ClientSeal ->
    per_usage_frame' ClientSeal ServerTicket h l h';
    per_usage_frame' ClientSeal ServerCookie h l h';
    per_usage_frame' ClientSeal WrapPSK h l h'

let frame h l h' =
  per_usage_frame' ServerCookie WrapPSK h l h' ;
  per_usage_frame' WrapPSK ServerTicket h l h' ;
  per_usage_frame' ServerTicket ClientSeal h l h' ;
  per_usage_frame' ClientSeal ServerCookie h l h'

inline_for_extraction
noextract
let reset_key (u: usage) : HST.Stack unit
  (requires (fun _ -> True))
  (ensures (fun h _ h' ->
    B.modifies (loc_store_regions u) h h' /\
    per_usage_inv h' u
  ))
= let p = keyptr u in
  B.recall p;
  B.upd p 0ul None

let reset _ =
  let h0 = HST.get () in
  reset_key ServerCookie;
  let h1 = HST.get () in
  reset_key ClientSeal;
  let h2 = HST.get () in
  per_usage_frame' ClientSeal ServerCookie h1 B.loc_none h2;
  reset_key WrapPSK;
  let h3 = HST.get () in
  per_usage_frame' WrapPSK ClientSeal h2 B.loc_none h3;
  per_usage_frame' WrapPSK ServerCookie h2 B.loc_none h3;
  reset_key ServerTicket;
  let h4 = HST.get () in
  per_usage_frame' ServerTicket WrapPSK h3 B.loc_none h4;
  per_usage_frame' ServerTicket ClientSeal h3 B.loc_none h4;
  per_usage_frame' ServerTicket ServerCookie h3 B.loc_none h4;  
  Success

#push-options "--z3rlimit 32"

let set_key u a key =
  let h = HST.get () in
  match AE.coerce (tls_store_regions u) a key (phi u) with
    | None -> UnsupportedAlgorithm // TODO: refine error codes
    | Some st ->
      let p = keyptr u in
      let h1 = HST.get () in
      begin match B.index p 0ul with
      | None -> ()
      | Some (| a', st' |) ->
        AE.frame_invariant h st' B.loc_none h1;
        AE.free st';
        let h2 = HST.get () in
        AE.frame_invariant h1 st (AE.footprint st') h2
      end;
      let h2 = HST.get () in
      B.upd p 0ul (Some (| a, st |));
      let h' = HST.get () in
      AE.frame_invariant h2 st (B.loc_buffer p) h';
      per_usage_frame u h B.loc_none h';
      Success

#pop-options

#push-options "--z3rlimit 16"

let encrypt u plain plain_len cipher =
  let h = HST.get () in
  let p = keyptr u in
  match B.index p 0ul with
    | None -> InvalidKey
    | Some (| a, st |) ->
      assume (phi u (B.as_seq h plain));
      assert (Mem.loc_store_region () `B.loc_includes` AE.footprint st);
      AE.encrypt st plain plain_len cipher;
      let h' = HST.get () in
      assert (Mem.loc_store_region () `B.loc_includes` B.loc_buffer p);
      per_usage_frame u h (B.loc_buffer cipher) h';
      Success

let decrypt u plain plain_len cipher =
  Success

#pop-options

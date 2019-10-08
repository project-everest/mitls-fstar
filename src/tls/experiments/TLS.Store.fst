module TLS.Store

module B = LowStar.Buffer

module AE = Crypto.AE

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let store_regions : (l:list substore{List.Tot.length l == 4 /\ Mem.r_pairwise_disjoint l})
  = Mem.r_disjoint_alloc _ 4

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

let loc_store_regions_disjoint = ()

assume val server_cookie_phi : AE.plain_pred 

let server_cookie_key :
  (server_cookie_key: B.pointer (option (a: alg & (st: AE.state a server_cookie_phi { B.loc_includes (loc_store_server_cookie_region ()) (AE.footprint st) }))) {
    B.recallable server_cookie_key /\
    B.frameOf server_cookie_key == tls_store_server_cookie_region
  }) = B.gcmalloc tls_store_server_cookie_region None 1ul

assume val server_ticket_phi : AE.plain_pred 

let server_ticket_key :
  (server_ticket_key: B.pointer (option (a: alg & (st: AE.state a server_ticket_phi { B.loc_includes (loc_store_server_ticket_region ()) (AE.footprint st) }))) {
    B.recallable server_ticket_key /\
    B.frameOf server_ticket_key == tls_store_server_ticket_region
  }) = B.gcmalloc tls_store_server_ticket_region None 1ul

unfold
let inv' (h: HS.mem) : Tot Type0 =
  B.live h server_cookie_key /\
  begin match B.deref h server_cookie_key with
  | None -> True
  | Some (| a, st |) ->
    B.loc_disjoint (AE.footprint st) (B.loc_buffer server_cookie_key) /\
    AE.invariant h st
  end /\
  B.live h server_ticket_key /\
  begin match B.deref h server_ticket_key with
  | None -> True
  | Some (| a, st |) ->
    B.loc_disjoint (AE.footprint st) (B.loc_buffer server_ticket_key) /\
    AE.invariant h st
  end

let inv = inv'

let frame h l h' =
  assert (Mem.loc_store_region () `B.loc_includes` B.loc_buffer server_cookie_key);
  assert (Mem.loc_store_region () `B.loc_includes` B.loc_buffer server_ticket_key); 
  assert (B.live h' server_cookie_key);
  begin match B.deref h server_cookie_key with
  | None -> ()
  | Some (| a, st |) ->
    assert (Mem.loc_store_region () `B.loc_includes` AE.footprint st);
    AE.frame_invariant h st l h'
  end;
  assert (B.live h' server_ticket_key);
  begin match B.deref h server_ticket_key with
  | None -> ()
  | Some (| a, st |) ->
    assert (Mem.loc_store_region () `B.loc_includes` AE.footprint st);
    AE.frame_invariant h st l h'
  end

let reset _ =
  B.recall server_cookie_key;
  B.recall server_ticket_key;
  B.upd server_cookie_key 0ul None;
  B.upd server_ticket_key 0ul None;
  Success

#push-options "--z3rlimit 16"

let set_key u a key =
  let h = HST.get () in
  match u with
  | ServerCookie ->
    // TODO: free the extant one, if any; requires key to be disjoint from region
    begin match AE.coerce tls_store_server_cookie_region a key server_cookie_phi with
    | None -> UnsupportedAlgorithm // TODO: refine error codes
    | Some st ->
      let h1 = HST.get () in
      B.upd server_cookie_key 0ul (Some (| a, st |));
      let h' = HST.get () in
      AE.frame_invariant h1 st (B.loc_buffer server_cookie_key) h';
      let f () : Lemma (inv' h') =
        begin match B.deref h server_ticket_key with
        | None -> ()
        | Some (| a', st' |) ->
          AE.frame_invariant h st' (B.loc_buffer server_cookie_key) h'
        end;
        assert (inv' h')        
      in
      f ();
      Success
    end
  | _ -> Success

#pop-options

let encrypt u plain plain_len cipher =
  Success

let decrypt u plain plain_len cipher =
  Success

(*
let server_cookie_key :
  (server_cookie_key: B.pointer (option (a: alg & AE.state a server_cookie_phi)) { B.frameOf server_cookie_key == store_region }) = B.gcmalloc store_region None 1ul

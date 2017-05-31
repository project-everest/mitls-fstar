module ODH

open ODH.KEF

type kefalg
val keflen: a:kefalg -> Tot nat

type pskid

type kef_type =
  // PSK extraction, zero salt
  | PSK: pski:pskid -> ikm
  // DH extraction, constant salt
  | DH: g:DH.group -> ishare:DH.share g -> ikm
  // DH extraction, early secret salt
  | DH_PSK: esId:TLSInfo.esId -> g:DH.group -> ishare:DH.keyshare g -> ikm
  // Zero extraction, handshake secret salt
  | ZERO: hsId: TLSInfo.hsId -> ikm

// Instance indexing. TODO: check that there is no possible collision
// between DH and DH_PSK instances
type pre_id = {
  alg: kefalg;
  kef_type: kef_type;
}

let safety_table =
  (if Flags.ideal_kef then
    MM.alloc #kef_region #id #(fun i -> bool) #(fun _ -> True)
  else unit)

type registered (i:id) =
  (if Flags.ideal_kef then
    MR.witnessed (MM.defined safety_table i)
  else True)

type id = i:pre_id{registered i}

type safeId (i:id) =
  (if Flags.ideal_kef then
    MR.witnessed (MM.contains safety_table i true)
  else False)

let is_safe (i:id) : ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> modifies_none h0 h1 /\ b <==> safeId i))
  =
  Flags.ideal_KEF_PRF &&
  (match i.kef_type with
  | PSK pski -> PSK.safePSK pski
  | DH_PSK esId _ _ _ -> honest_esId esId)

type dhrole =
  | Initiator
  | Responder

type role (i:id) =
  (match i.kef_type with
  | DH _ _ | DH_PSK _ _ _ -> dhrole
  | _ -> unit)

type salt (i:id) =
  (match i.kef_type with
  | PSK _  | DH _ _ -> unit
  | DH_PSK esId _ _ ->
    expanded_secret (EarlySecretID esId)
  | ZERO hsId ->
    expanded_secret (HandshakeSecretID hsId))

// The type of the input key material to extract
type ikm (i:id) (ir:role i) =
  (match i.kef_type with
  | PSK pski -> PSK.psk pski
  | DH g si | DH_PSK _ g si ->
    if ir = Initiator then CommonDH.secret g
    else unit
  | ZERO _ -> unit)

type extracted_secret (i:id) =
  lbytes (keflen i.alg)

type extractor_instance (i:id) =
  (match i.kef_type with
  | PSK _ | ZERO _ -> KEF_PRF.state i
  | DH _ _ _ -> KEF_PRF_ODH.state i
  | DH_PSK esId _ _ _ ->
    if honest_esId esId then
      KEF_PRF.state i
    else
      KEF_PRF_ODH.state i)




module TLS13.Spec.StateMachine.KeyIdentifiers

(**
  Auxiliary: key-schedule and derivation identifier / checkpoint vocabulary
  (base-secret, labeled-traffic-epoch, traffic-update and derived-key
  identifiers, the key-derivation and transcript checkpoints, and the
  record-layer key/iv material record).  This vocabulary is not reachable from
  the core connection-state / step / legal roots; it is shared by the
  Correspondence and KeyMaterial auxiliary layers, so it lives in its own small
  module between the core state machine and those layers.  Depends only on the
  core traffic-epoch / traffic-label types.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec

open TLS13.Spec.StateMachine

type base_secret_id =
  | EarlySecret
  | HandshakeSecret
  | MasterSecret
type labeled_traffic_epoch = {
  traffic_id_epoch: traffic_epoch;
  traffic_id_label: traffic_label;
}
let traffic_id
  (epoch:traffic_epoch)
  (label:traffic_label)
  : labeled_traffic_epoch =
  { traffic_id_epoch = epoch; traffic_id_label = label }
type traffic_update_id = {
  traffic_update_label: traffic_label;
  traffic_update_generation: nat;
}
type derived_key_id =
  | BaseSecret of base_secret_id
  | TrafficSecret of labeled_traffic_epoch
  | TrafficKey of labeled_traffic_epoch
  | TrafficIV of labeled_traffic_epoch
  | FinishedKey of traffic_label
  | TrafficUpdateSecret of traffic_update_id
  | ExporterMasterSecret
  | ResumptionMasterSecret
type key_derivation_checkpoint =
  | DeriveHandshakeTraffic
  | DeriveApplicationTraffic
  | DeriveTrafficUpdate of traffic_update_id
type transcript_checkpoint =
  | TH_CH
  | TH_SH
  | TH_before_CV
  | TH_before_SF
  | TH_SF
  | TH_CF
type record_key_iv_material = {
  record_material_alg: C.aead_alg;
  record_material_key: B.bytes;
  record_material_iv: B.bytes;
}

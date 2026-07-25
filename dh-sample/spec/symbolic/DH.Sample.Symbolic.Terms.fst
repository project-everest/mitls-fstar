module DH.Sample.Symbolic.Terms

(**
  DH.Sample.Symbolic.Terms — the protocol-specific *symbolic vocabulary* of the
  DH sample, expressed with Dolev-Yao / DY* CORE terms, usages, labels and trace
  events.  This module is the abstraction dictionary that later relates the
  concrete integer-crypto state machine (DH.Sample.StateMachine) to a symbolic
  DY* model.

  It depends ONLY on the DY* CORE library (third_party/.../src/core) and on the
  standalone dh-sample pure specification.  It does NOT depend on, import, or
  reuse any DY* example (in particular nothing under the iso-DH example tree) and it
  never references any DY-example module.

  Design summary
  --------------
    * Cryptographic material is modelled with the DY* term algebra
      (DY.Core.Bytes.Type.bytes): ephemeral DH scalars are fresh random nonces
      (Rand), public DH shares are dh_pk of a scalar, shared secrets are dh, and
      signatures are genuine Sign terms.  Attacker-injected concrete blobs are
      embedded as public DY literals.  Honest deliveries instead reuse the exact
      structured term stored when the peer sent the packet; neither case invents
      or reclassifies an origin.

    * Every term builder is a TOTAL FUNCTION of its inputs, so the abstraction is
      canonical and functional: there are no ad-hoc, non-functional binding
      tables mapping concrete values to arbitrary symbolic witnesses.

    * The two protocol equations the sample relies on hold as DY* theorems:
      Diffie-Hellman agreement (lemma_dh_agreement) and signature correctness
      (lemma_sign_verifies).  Both are proved from DY* CORE reduction rules; no
      obligation is left open, and no equation is taken on faith.

    * Dynamic compromise is modelled with the DY* CORE state/corruption
      vocabulary: each role owns ONE `state_id`, and every secret it holds (its
      long-term signing key, its DH scalar, each signing nonce) is labelled with
      that role's `principal_state_label` (`role_label`), which DY* makes corrupt
      EXACTLY when a `Corrupt` entry points at one of that role's `SetState`
      entries.  `snapshot_term` is the layout of the material a role stores (and
      therefore of what a compromise of that role hands the attacker).

  Honest provenance
  -----------------
    The vocabulary is chosen so that the product model can attach an HONEST
    provenance to every term it creates and never has to invent one:
      - a locally generated ephemeral is a Rand nonce whose RandGen origin the
        product records on its trace;
      - a locally produced signature is a Sign term created only AFTER the
        endpoint records an authorization Event binding the signed transcript;
      - an attacker-injected share or signature is only a public literal, while
        an honestly delivered one is the sender's stored structured term; hence
        no forged origin is asserted and no origin is inferred from the
        (deliberately weak) concrete verification predicate.
*)

module B   = DY.Core.Bytes
module BT  = DY.Core.Bytes.Type
module L   = DY.Core.Label
module LT  = DY.Core.Label.Type
module T   = DY.Core.Trace.Type
module TB  = DY.Core.Trace.Base
module Seq = FStar.Seq
module U8  = FStar.UInt8

open DH.Sample.Types
open DH.Sample.Wire
open DH.Sample.System

(** ── Fixed, role-distinct DY principals and role state identifiers ───────────

    This is a fixed two-party sample.  DY event/key/state ownership is attributed
    to two constant, definitionally distinct principals, never to an unproved
    encoding of arbitrary concrete bytes.  Each role owns exactly ONE DY* session
    (state) identifier — its single live protocol state — so the "current state"
    of a role is a `SetState` entry for `(role_dy_principal who, role_state_id
    who)`, and corrupting the role means a DY* `Corrupt` entry pointing AT such an
    entry.  Concrete principal bytes are still embedded in messages and signed
    transcript terms below. *)
let init_dy_principal : T.principal = "DH.Sample.Initiator"
let resp_dy_principal : T.principal = "DH.Sample.Responder"

let lemma_role_principals_distinct ()
  : Lemma (ensures init_dy_principal =!= resp_dy_principal)
= ()

let role_dy_principal (who:endpoint_id) : T.principal =
  match who with
  | Init -> init_dy_principal
  | Resp -> resp_dy_principal

(** The single DY* session identifier each role's live state lives at.  Both roles
    use identifier 0 because the two OWNING PRINCIPALS already differ. *)
let role_state_id (who:endpoint_id) : T.state_id = { T.the_id = 0 }

let lemma_role_state_owners_distinct ()
  : Lemma (ensures role_dy_principal Init =!= role_dy_principal Resp)
= ()

(** ── Abstract symbolic lengths ─────────────────────────────────────────────

    The DY* term algebra tags random values with a positive length.  These are
    purely symbolic sizes for the three kinds of secret material the sample
    generates; their numeric values are irrelevant to the proofs beyond being
    non-zero. *)
let eph_len      : n:nat{ n <> 0 } = 32
let ltk_len      : n:nat{ n <> 0 } = 32
let signonce_len : n:nat{ n <> 0 } = 32

(** ── Usages ────────────────────────────────────────────────────────────────

    Usages keep key material for one primitive from being reused with another.
    The three secrets the sample generates are: an ephemeral DH key, a long-term
    signature key, and a per-signature nonce. *)
let empty_data : BT.bytes = B.literal_to_bytes (Seq.empty #U8.t)

let eph_usage      : BT.usage = BT.DhKey  "DH.Sample.ephemeral" empty_data
let ltk_usage      : BT.usage = BT.SigKey "DH.Sample.longterm"  empty_data
let signonce_usage : BT.usage = BT.SigNonce

(** ── Compromise-sensitive role/state labels ─────────────────────────────────

    Every long-lived or ephemeral SECRET of a role — its long-term signing key,
    its DH scalar, and each of its per-signature nonces — is labelled with that
    role's STATE label `L.principal_state_label (role_dy_principal who)
    (role_state_id who)`.  That DY* label is corrupt EXACTLY when some `SetState`
    entry of that role's state has been hit by a `Corrupt` entry
    (`L.is_corrupt_state_pred_label`), i.e. exactly when the attacker has
    dynamically compromised that role.

    This replaces the previous unconditional `L.secret` labelling, which asserted
    that role secrets are NEVER corrupt and therefore could not express dynamic
    compromise at all.  With the state label:

      * before any compromise, the label is not corrupt, so all the old secrecy
        consequences still hold (see `DH.Sample.Symbolic.Security`);
      * after `ActCorrupt who`, the label IS corrupt, DY* immediately allows the
        attacker to hold that role's key material, the signature `bytes_invariant`
        offers its ATTACKER branch (`get_label sk` flows to `public`), and every
        security statement degrades to "... OR that role is compromised".

    Because a role's signing key, scalar and signing nonces all carry the SAME
    label, the DY* `Sign` invariant's side condition "the signing key is at most
    as secret as the nonce" holds reflexively. *)
let role_label (who:endpoint_id) : LT.label =
  L.principal_state_label (role_dy_principal who) (role_state_id who)

let eph_label      (who:endpoint_id) : LT.label = role_label who
let ltk_label      (who:endpoint_id) : LT.label = role_label who
let signonce_label (who:endpoint_id) : LT.label = role_label who

(** A role's label is corrupt EXACTLY when one of that role's stored states has
    been corrupted on the trace.  This is the single bridge between DY* label
    corruption and the `SetState`/`Corrupt` trace entries the product records. *)
let lemma_role_label_corrupt_iff (tr:TB.trace) (who:endpoint_id)
  : Lemma
    (ensures
      L.is_corrupt tr (role_label who) <==>
      (exists (prin:T.principal) (sid:T.state_id) (content:BT.bytes).
         TB.state_was_corrupt tr prin sid content /\
         prin == role_dy_principal who /\ sid == role_state_id who))
= L.is_corrupt_state_pred_label tr
    (L.principal_state_label_input (role_dy_principal who) (role_state_id who))

(** The "compromised" direction, in the form the product uses: a `Corrupt` entry
    pointing at one of the role's `SetState` entries corrupts its label. *)
let lemma_state_corrupt_implies_label_corrupt
  (tr:TB.trace) (who:endpoint_id) (content:BT.bytes)
  : Lemma
    (requires
      TB.state_was_corrupt tr (role_dy_principal who) (role_state_id who) content)
    (ensures L.is_corrupt tr (role_label who))
= lemma_role_label_corrupt_iff tr who

(** ── Embedding of concrete public blobs ────────────────────────────────────

    Principal identifiers and ATTACKER-INJECTED DH shares/signatures become
    PUBLIC DY* literals.  Embedding injected material as a literal asserts no
    secret origin and no cryptographic structure.  Honest delivery does not use
    these blob embeddings: it reuses the exact structured `sym_msg` recorded by
    the sender in the network shadow. *)
let term_of_principal (p:principal) : BT.bytes = B.literal_to_bytes p
let term_of_blob      (b:bytes)     : BT.bytes = B.literal_to_bytes b

(** ── Structural term builders ──────────────────────────────────────────────

    Locally generated material is genuine DY* structure:
      * a scalar is a fresh Rand nonce at a given trace time,
      * a share is dh_pk of a scalar,
      * a shared secret is dh of a scalar and a peer share,
      * a signature is sign of a signing key, a fresh nonce, and a message. *)
let eph_term      (time:nat) : BT.bytes = BT.Rand eph_len      time
let ltk_term      (time:nat) : BT.bytes = BT.Rand ltk_len      time
let signonce_term (time:nat) : BT.bytes = BT.Rand signonce_len time

let share_term  (sk:BT.bytes)    : BT.bytes = B.dh_pk sk
let secret_term (sk pk:BT.bytes) : BT.bytes = B.dh sk pk
let vkey_term   (sk:BT.bytes)    : BT.bytes = B.vk sk

(** The signed transcript term: partner identity, then the two DH shares,
    concatenated left to right — mirroring the concrete transcript layout. *)
let transcript_term (partner gx gy:BT.bytes) : BT.bytes =
  B.concat partner (B.concat gx gy)

let sig_term (sk nonce msg:BT.bytes) : BT.bytes = B.sign sk nonce msg

(** ── Symbolic wire-message terms ───────────────────────────────────────────

    The DY* term recorded on the network (a MsgSent entry) for each of the three
    protocol messages, mirroring the concrete field layout
    (principal ++ share [++ signature]).  The tag byte of the concrete wire
    format is not modelled symbolically; message identity comes from the term
    structure and the trace position. *)
let msg1_term (initiator share:BT.bytes)         : BT.bytes = B.concat initiator share
let msg2_term (responder share signature:BT.bytes) : BT.bytes =
  B.concat responder (B.concat share signature)
let msg3_term (signature:BT.bytes)               : BT.bytes = signature

(** ── Structured symbolic wire messages ──────────────────────────────────────

    `sym_msg` is the STRUCTURED symbolic message put on the wire, mirroring the
    concrete `dh_message` field-by-field.  A network shadow stores exactly the
    `sym_msg` that the sender generated, so a receiver can recover the sender's
    OWN structured fields (its DH share `share_term`, its signature `sig_term`)
    rather than re-embedding them as literals.  This is the vehicle for
    "honest sent packet carries the exact structured symbolic term, and delivery
    reuses that same term".  `flatten` renders a `sym_msg` as the flat `bytes`
    term that appears in the `MsgSent` trace entry. *)
noeq
type sym_msg =
  | SMsg1 : a:BT.bytes -> gx:BT.bytes -> sym_msg
  | SMsg2 : b:BT.bytes -> gy:BT.bytes -> sg:BT.bytes -> sym_msg
  | SMsg3 : sg:BT.bytes -> sym_msg

let flatten (m:sym_msg) : BT.bytes =
  match m with
  | SMsg1 a gx    -> msg1_term a gx
  | SMsg2 b gy sg -> msg2_term b gy sg
  | SMsg3 sg      -> msg3_term sg

(** The all-literal STRUCTURED symbolic message an attacker injects: every field
    (identity, share AND signature) embedded as a PUBLIC literal.  This is the
    honest model of attacker traffic — it asserts no cryptographic origin, and a
    received signature is a `Literal`, NEVER a `Sign` term.  It is a TOTAL,
    CANONICAL function of the concrete message. *)
let inject_smsg (m:dh_message) : sym_msg =
  match m with
  | Msg1 a gx      -> SMsg1 (term_of_principal a) (term_of_blob gx)
  | Msg2 b gy sigB -> SMsg2 (term_of_principal b) (term_of_blob gy) (term_of_blob sigB)
  | Msg3 sigA      -> SMsg3 (term_of_blob sigA)

(** ── Canonical all-literal *delivery term* of a concrete wire message ────────

    The flat `bytes` term of an injected/attacker message: `flatten (inject_smsg m)`.
    EVERY field — identity, share AND signature alike — is embedded as a PUBLIC DY*
    literal via `term_of_principal` / `term_of_blob`.  It asserts no secret origin
    and no cryptographic structure: in particular a received signature is a
    `Literal`, NEVER a `Sign` term, so the product never infers a signature origin
    from the deliberately weak concrete verifier.  It is a TOTAL, CANONICAL function
    of the concrete message. *)
let delivery_term (m:dh_message) : BT.bytes = flatten (inject_smsg m)


(** ── The stored state snapshot of a role ────────────────────────────────────

    The DY* `SetState` content the product writes for a role.  It EXPLICITLY
    RETAINS every piece of material that role currently holds, in a fixed layout:

        ltk ++ (pending ++ (scalar ++ (peer_share ++ key)))

    A field that does not exist yet (or does not exist any more, in a model that
    erased it) is rendered as the public empty literal `no_material`.

    NO ERASURE IS MODELLED.  Once a role has drawn its ephemeral scalar or derived
    its session key, that material stays in every later snapshot of that role, so
    a compromise at ANY later time hands the attacker the CURRENT session key as
    well as the long-term key.  Consequently this model deliberately offers NO
    forward secrecy (see dh-sample/SYMBOLIC_SECURITY.md §"No erasure, no PFS"):
    a post-session compromise of a role is as damaging as a pre-session one. *)
let no_material : BT.bytes = empty_data

let opt_material (o:option BT.bytes) : BT.bytes =
  match o with
  | None   -> no_material
  | Some b -> b

let snapshot_term (ltk:BT.bytes) (pending scalar peer_share key:option BT.bytes)
  : BT.bytes =
  B.concat ltk
    (B.concat (opt_material pending)
      (B.concat (opt_material scalar)
        (B.concat (opt_material peer_share) (opt_material key))))

(** ── Protocol event vocabulary ─────────────────────────────────────────────

    Authorization / origin events recorded by an endpoint on its DY* trace.
    They are triggered BEFORE the corresponding cryptographic term is formed, so
    a later authentication invariant can be established without any circular
    dependency between an event and the term it authorizes.

      * tag_keygen           : an endpoint registered its long-term verification
                               key at setup, binding it to its own identity.
      * tag_initiate         : the initiator started a run towards a peer.
      * tag_initiator_finish : the initiator authorizes its message-3 signature.
      * tag_responder_respond: the responder authorizes its message-2 signature.
      * tag_responder_finish : the responder accepted message 3 and completed. *)
let tag_keygen            : string = "DH.Sample.KeyGen"
let tag_initiate          : string = "DH.Sample.Initiate"
let tag_initiator_finish  : string = "DH.Sample.InitiatorFinish"
let tag_responder_respond : string = "DH.Sample.ResponderRespond"
let tag_responder_finish  : string = "DH.Sample.ResponderFinish"

(** The content of a key-registration event: the endpoint's own identity bound to
    the PUBLIC verification key of its freshly generated long-term signing key.
    Recording this on the trace ties the long-term key material to the identity
    that owns it — the association a later authentication proof needs in order to
    attribute a verified signature to a named principal. *)
let keygen_content (me vkey:BT.bytes) : BT.bytes = B.concat me vkey

(** The content bound by an authorization event: the same partner-and-shares
    transcript that the authorized signature covers. *)
let auth_content (partner gx gy:BT.bytes) : BT.bytes = transcript_term partner gx gy

(** The content of the initiator's start event: its own identity, the intended
    peer, and the ephemeral share it just published.  No peer share exists yet. *)
let initiate_content (me peer share:BT.bytes) : BT.bytes =
  B.concat me (B.concat peer share)

(** The content of a completion event: the accepted peer and the derived key. *)
let session_content (peer key:BT.bytes) : BT.bytes = B.concat peer key

(** ── Coherence theorems ────────────────────────────────────────────────────

    The two protocol equations, proved from DY* CORE reduction rules. *)

(** Diffie-Hellman agreement: combining one scalar with the peer's share yields
    the same shared secret from either side.  This is the symbolic counterpart of
    DH.Sample.Crypto.lemma_dh_agree. *)
let lemma_dh_agreement (x y:BT.bytes)
  : Lemma (ensures secret_term x (share_term y) == secret_term y (share_term x))
= B.dh_shared_secret_lemma x y

(** Signature correctness: a signature produced by a signing key verifies under
    the matching verification key.  This is the symbolic counterpart of
    DH.Sample.Crypto.lemma_sign_verify. *)
let lemma_sign_verifies (sk nonce msg:BT.bytes)
  : Lemma (ensures B.verify (vkey_term sk) msg (sig_term sk nonce msg))
= B.verify_sign sk nonce msg

(** ── Supported-vocabulary inhabitation ─────────────────────────────────────

    The vocabulary is non-vacuous: an honestly generated ephemeral, its public
    share and the resulting shared secret all exist and satisfy the agreement
    equation.  This rules out the degenerate reading in which the symbolic layer
    would be built over an empty (uninhabited) term universe. *)
let lemma_vocabulary_inhabited (t0 t1:nat)
  : Lemma (ensures (
      let x  = eph_term t0 in
      let y  = eph_term t1 in
      secret_term x (share_term y) == secret_term y (share_term x)))
= lemma_dh_agreement (eph_term t0) (eph_term t1)

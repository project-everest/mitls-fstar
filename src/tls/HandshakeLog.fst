(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
module HandshakeLog
open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
 // for e.g. found
open FStar.Set
open Platform.Error
open Platform.Bytes

open TLSConstants
open TLSInfo
open HandshakeMessages
open Hashing.Spec

(* A flag for runtime debugging of handshakelog data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
inline_for_extraction let hsl_debug = false

abstract type hs_log = list hs_msg

let reveal_hs_log (hsl:hs_log) : GTot (list hs_msg) = hsl
let hide_hs_log (l:list hs_msg) : GTot hs_log = l

val validLog: hs_log -> Tot bool
let validLog hsl =
    match hsl with
    | [] -> true
    | [ClientHello ch] -> true
    | (ClientHello ch) :: (ServerHello sh) :: rest -> true
    | _ -> false

val getLogVersion: hsl:hs_log{validLog hsl} -> Tot (option protocolVersion)
let getLogVersion hsl =
    match hsl with
    | (ClientHello ch) :: (ServerHello sh) :: rest -> Some sh.sh_protocol_version
    | _ -> None

(* TODO: maybe hsl an erased bytes, see ulib/FStar.Ghost.fst *)
(* Here's a very rough sketch *)
(* er h = erased (b:bytes{h = hash b})) *)
(* update_hash (h:hash) (e:er h) (b:bytes) : (h':hash & er h') = *)
(*    (| upd_hb h b, elift1 (fun (bold:bytes) -> concat bold b) e |) *)
(*   let (|h, eb|) = !r in *)
(*   let next = update_hash h eb b in *)

(*
 * AR: changing logref from rref to HS?.ref, with region captured in the refinement.
 *)
noeq type log =
  | LOG: #region:rid ->
         logref:ref (
              pv: option protocolVersion
            & (hsl:hs_log{validLog hsl})
            &   b: bytes {getLogVersion hsl = pv /\ handshakeMessagesBytes pv (reveal_hs_log hsl) = b}
         ){logref.id = region} -> log

val create: #reg:rid -> ST log
  (requires (fun h -> True))
  (ensures (fun h0 out h1 ->
    let LOG #r lr = out in
    stronger_fresh_region r h0 h1 /\
    extends r reg /\
    modifies (Set.singleton r) h0 h1 /\
    modifies_rref r !{as_ref lr} h0.h h1.h))
let create #reg =
    let hsl: hs_log = [] in
    let r = new_region reg in
    let lr = ralloc r (| None, hsl, empty_bytes|) in
    LOG #r lr

val append_log: l:log -> hm:hs_msg -> ST bytes
    (requires (fun h ->
	       let (|pv,hsl,lb|) = sel h l.logref in
	       validLog (hide_hs_log (List.Tot.append (reveal_hs_log hsl) [hm]))))
    (ensures (fun h0 _ h1 ->
      let LOG #r lr = l in
      modifies (Set.singleton r) h0 h1
      /\ modifies_rref r !{as_ref lr} h0.h h1.h))
let append_log (LOG #reg lref) hm =
    let (| pv, hsl, lb |) = !lref in
    let hsl' = FStar.List.Tot.append hsl [hm] in
    let pv = getLogVersion hsl' in
    let mb = handshakeMessageBytes pv hm in
    let lb' = lb @| mb in
    lref := (| pv, hsl', lb' |);
    mb

let op_At_At l h = append_log l h

let print_log hs_log : Tot bool =
    let sl = List.Tot.map (HandshakeMessages.string_of_handshakeMessage) hs_log in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string("LOG : " ^ s ^ "\n")

val getMessages: log -> St hs_log
let getMessages (LOG #reg lref) =
    let (| pv, hsl, lb |) = !lref in hsl

val getBytes: log -> St bytes
let getBytes (LOG #reg lref) =
    let (| pv, hsl, lb |) = !lref in lb

val getHash: log -> h:hash_alg -> St (tag h)
let getHash (LOG #reg lref) h =
    let (| pv, hsl, lb|) = !lref in
    let b =
        if hsl_debug then
            print_log hsl
        else false in
    Hashing.compute h lb

type validLog_CH (l:hs_log) =
  (match l with
  | [ClientHello _] -> True
  | _ -> False)

let projectLog_CH (l:hs_log{validLog_CH l}) : logInfo_CH =
  match l with
  | [ClientHello ({
      ch_client_random = cr;
      ch_sessionID = sid;
      ch_extensions = Some el
    })] -> ({
      li_ch_cr = cr;
      li_ch_ed_psk = empty_bytes;
      li_ch_ed_ae = AEAD CoreCrypto.AES_128_GCM SHA256;
      li_ch_ed_hash = SHA256;
      li_ch_psk = [];
    })

val getHash_CH : l:log -> h:hash_alg ->
  ST ( li:logInfo{LogInfo_CH? li} & tag h )
    (requires (fun h0 ->
      let lref = l.logref in
      let (| _, hsl, _ |) = sel h0 lref in validLog_CH hsl))
    (ensures (fun h0 (| li, hash |) h1 ->
	h1 = h0 /\ log_info li hash))

let getHash_CH (LOG #reg lref) (h:hash_alg) =
  let (| _, hsl, lb |) = !lref in
  let loginfo = projectLog_CH hsl in
  let tag = Hashing.compute h lb in
  (| LogInfo_CH loginfo, tag |)

type validLog_SH (l:hs_log) =
  (match l with
  | (ClientHello _) :: r ->
    (match r with
    | _ -> False)
  | _ -> False)

assume val checkLogSessionHash: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> GTot bool
assume val checkLogClientFinished: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> GTot bool
assume val checkLogServerFinished: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> GTot bool

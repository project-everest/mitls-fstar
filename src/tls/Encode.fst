(*--build-config
    options:--lax --prims ../tls-ml/prims.fst --verify_module Encode --debug yes --admit_fsi Seq --admit_fsi SessionDB --admit_fsi UntrustedCert --admit_fsi CoreCrypto.ECDH --admit_fsi CoreCrypto.DHDB;
    other-files:../tls-ml/string.fst ../tls-ml/list.fst ../../../FStar/lib/ext.fst ../../../FStar/lib/classical.fst ../../../FStar/lib/set.fsi ../../../FStar/lib/set.fst ../../../FStar/lib/heap.fst ../../../FStar/lib/st.fst ../../../FStar/lib/seq.fsi ../../../FStar/lib/seqproperties.fst ../../libs/fst/Platform/Bytes.fst ../../libs/fst/Platform/Date.fst ../../libs/fst/Platform/Error.fst ../../libs/fst/Platform/Tcp.fst ../../libs/fst/CoreCrypto/Keys.fst ../../libs/fst/CoreCrypto/ACiphers.fst ../../libs/fst/CoreCrypto/HMac.fst ../../libs/fst/CoreCrypto/Random.fst ../../libs/fst/CoreCrypto/Ciphers.fst ../../libs/fst/CoreCrypto/Hash.fst ../../libs/fst/CoreCrypto/Sig.fst ../../libs/fst/CoreCrypto/DHDB.fst ../../libs/fst/CoreCrypto/DH.fst ../../libs/fst/CoreCrypto/ECDH.fsi ../../libs/fst/CoreCrypto/DER.fst ../../libs/fst/DHDBManager/DHDBManager.fst ../tls/TLSError.p.fst ../tls/Nonce.p.fst ../tls/TLSConstants.p.fst ../tls/RSAKey.p.fst ../tls/DHGroup.p.fst ../tls/ECGroup.p.fst ../tls/CommonDH.p.fst ../tls/PMS.p.fst ../tls/HASH.p.fst ../tls/HMAC.p.fst ../tls/SigLax.p.fst ../tls/UntrustedCert.p.fsti ../tls/Cert.p.fst ../tls/TLSInfo.p.fst ../tls/TLSExtensions.p.fst ../tls/TLSPRF.p.fst ../tls/RangeLax.p.fst ../tls/DataStream.p.fst ../tls/AppFragment.p.fst ../tls/HSFragment.p.fst ../tls/TLSFragment.p.fst ../tls/StatefulPlain.p.fst ../tls/LHAEPlain.p.fst ../tls/MAC_SHA256.p.fst ../tls/MAC_SHA1.p.fst ../tls/MAC.p.fst
 --*)
(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

// 2015-05-26 completely rewritten; pls someone review it!
module Encode

(* The "plain" file for CPA encryption (module ENC) *)
(* provided by LHAE,
   implementing LHAEPlain @| MAC @| padding when using MtE *)

open FStar.Seq
open Platform
open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo
open Range

(* Interface towards ENC (conditionally abstract) *)

// the result of decrypting & decoding, with an abstract type for secrecy
private type plain (i:id) (ad: LHAEPlain.adata i) (rg:range) =
    { plain: LHAEPlain.plain i ad rg;
      tag  : MAC.tag;
      ok   : b:bool { encAlg_of_id i = (Stream CoreCrypto.RC4_128, Fresh) ==> b = true }
      (* true iff decoding succeeded; always true with RC4. *) }

val plainLength: i:id -> clen: nat { clen >= ivSize i } -> Tot nat
let plainLength i clen = clen - ivSize i


(* Interface towards LHAE *)

private val zeros: r:range -> rbytes r
let zeros (rg:range) = createBytes (snd rg) 0uy

val payload: i:id -> r:range -> ad:LHAEPlain.adata i->
  LHAEPlain.plain i ad r -> Tot (rbytes r) //$ we had?: { SafeId e }

// the MACed bytes, i.e. ad @| 2-byte length of payload @| payload
//CF should ask some injectivity

let payload (e:id) (rg:range) ad f =
  // After applying CPA encryption for ENC,
  // we access the fragment bytes only at unsafe indexes, and otherwise use some zeros
  #if ideal
  if safeId e then zeros rg
  else
  #endif
    LHAEPlain.repr e ad rg f

val macPlain_bytes:
  i:id -> r:range -> LHAEPlain.adata i -> rbytes r -> Tot bytes

let macPlain_bytes (i:id) (rg:range) ad b = ad @| vlbytes 2 b

val macPlain: i:id -> r:range ->
  =ad:LHAEPlain.adata i ->
  =f:LHAEPlain.plain i ad r ->
  Tot (b:bytes{ safeId i })
let macPlain (i:id) (rg:range) ad f =
  macPlain_bytes i rg ad (payload i rg ad f)

(*
private ask !i,r,ad,b,p.
  B(ad) @| VLBytes(2,B(b)) = B(ad) @| VLBytes(2,LHAEPlain.Payload(i,B(ad),r,p)) ==>
  B(b) = LHAEPlain.Payload(i,B(ad),r,p)
 *)

// We define a MACOnly log exclusively for MACOnly ciphersuites
// that behaves like a bijection with what we learn from the MAC.Msg predicate. Hence,
// - Items are inserted only for honest macs, that is when AuthId && MAC.Msg hold
// - Items can be retrieved only for verified macs, that is, when AuthId holds,
//   and when we have learnt sufficient information from the MAC.Msg predicate
//   --- namely that an LHAEPlain.plain with the expected payload exists.

//$ in F*, it may be better to maintain a separate log for each MAC instance.

#if ideal
type maconly_entry =
    i:id * ad:LHAEPlain.adata i * rg:range * tlen:nat *
     payload:bytes * text:bytes * p:LHAEPlain.plain i ad rg * MAC.tag
  { authId i /\ //
    tlen <= max_TLSCipher_fragment_length /\ tlen = targetLength i rg /\ //
    is_MACOnly i.aeAlg /\ //
    MAC.Msg(i,text) /\ //
    text = MACPlain i rg ad p /\ //
    payload = LHAEPlain.Payload i ad rg p
  }

private val maconly_log: maconly_entry list ref
private val maconly_mem:
	i:id{AuthId(i) /\ (?mac. i.aeAlg = MACOnly(mac))} ->
	ad:(;i)LHAEPlain.adata -> tlen:nat{tlen <= max_TLSCipher_fragment_length} ->
	pl:bytes -> t:bytes{B(t) = B(ad) @| VLBytes(2,B(pl)) /\
		(?rg,p. B(pl) = LHAEPlain.Payload(i,B(ad),rg,p) )} ->
	(;i)MAC.tag -> xs:maconly_entry list ->
	((rg:range * p:(;i,ad,rg)LHAEPlain.plain){tlen = TargetLength(i,rg) /\ B(pl) = LHAEPlain.Payload(i,B(ad),rg,p)}) option

type maconly_entry = id * LHAEPlain.adata * range * nat * bytes * bytes * LHAEPlain.plain * MAC.tag
let maconly_log = ref ([]:list<maconly_entry>)
let rec maconly_mem i ad cl pl text tag (xs:list<maconly_entry>) =
    match xs with
    | (i', ad', rg', cl', pl', text', p', tag')::_
        when i=i' && ad=ad' && cl=cl' && pl=pl' && text=text' && tag=tag' -> let x = (rg',p') in Some x
    | _::xs -> maconly_mem i ad cl pl text tag xs
    | [] -> None
#endif

val mac: i:id -> k:MAC.key (*i*) -> ad:LHAEPlain.adata i -> rg:range -> p:LHAEPlain.plain i ad rg ->  (plain i ad rg)
let mac i k ad rg plain =
    let p = LHAEPlain.makeExtPad i ad rg plain in
    let text = macPlain i rg ad p in
    let tag  = MAC.mac i k text in
#if ideal
    (* For MACOnly ciphersuites where AuthId holds, we store the plain and
     * the tag in the MACOnly log *)
    let e_aealg = i.aeAlg in
    let auth = authId i in
    if auth = true then
      (match (e_aealg) with
       | MACOnly(_) ->
          let tlen = targetLength i rg in
          let pl = payload i rg ad p in
          maconly_log := (i,ad,rg,tlen,pl,text,p,tag)::!maconly_log
       | _ -> ())
     else ();
#endif
    {plain = p;
     tag = tag;
     ok = true
    }

(*MK 26/09/2015 restore at some point*)

(*val verify_MACOnly:
  e: id{ ~ (safeId e) /\ is_MACOnly e.aeAlg } ->
  k: MAC.key ->
  ad: LHAEPlain.adata e ->
  rg: range ->
  tlen: nat{
    tlen <= max_TLSCipher_fragment_length /\//
    rg = cipherRangeClass e tlen
    } ->
  b: rbytes rg ->
  t: MAC.tag ->
  result (LHAEPlain.plain e ad (cipherRangeClass e tlen))*)

let verify_MACOnly (e:id) k (ad:LHAEPlain.adata e) (rg:range) (cl:nat) b tag 
  (*: result (LHAEPlain.plain e ad rg)*)

  =
  let text = macPlain_bytes e rg ad b in
  if MAC.verify e k text tag then
  #if ideal
    if authId e then
      match maconly_mem e ad cl b text tag !maconly_log with
      | Some(x) ->
          let (rg',p') = x in
          let p = LHAEPlain.widen e ad rg' p' in
          let rg = rangeClass e rg' in
          Correct p
      | None ->
          Error(AD_bad_record_mac,perror __SOURCE_FILE__ __LINE__ "")
    else
  #endif
          let p = LHAEPlain.mk_plain e ad rg b in
          Correct p
  else
          Error(AD_bad_record_mac,perror __SOURCE_FILE__ __LINE__ "")

(*MK 26/09/2015 restore at some point*)

(*val verify:
  e:id ->
  k: MAC.key ->
  ad: LHAEPlain.adata e ->
  rg: range ->
  ps: plain e ad rg ->
  result (LHAEPlain.plain e ad rg)*)
let verify (e:id) k ad rg (plain:plain e ad rg) =
    let f = plain.plain in
    let text = macPlain e rg ad f in
    let tag  = plain.tag in
        (*@ We implement standard mitigation for padding oracles.
            Still, we note a small timing leak here:
            The time to verify the mac is linear in the plaintext length. *)
    if MAC.verify e k text tag && plain.ok then
        match LHAEPlain.parseExtPad e ad rg f with
        | Correct(f) -> correct f
        | Error(x) ->
            #if DEBUG
            Error(AD_bad_record_mac,perror __SOURCE_FILE__ __LINE__ "")
            #else
            Error(AD_bad_record_mac,"")
            #endif
      else
            #if DEBUG
            Error(AD_bad_record_mac,perror __SOURCE_FILE__ __LINE__ "")
            #else
            Error(AD_bad_record_mac,"")
            #endif

(* KB we need to add some refinement to ensure that verify
   will not fail for MACed values *)
(* CF we may need something like
   safeId e ==> Version(e) = TLS_1p1 \/ Version(e) = TLS_1p2 \/ ps.ok = true
*)


// padding in TLS: [| 0uy |], [| 1uy; 1uy |], ...

val pad: l:nat { 0 < l /\ l <= 256 } -> Tot(lbytes l)
// we may need a more precise refinement for the MEE proof:
// the last byte of padding determines the padding

let pad p  = createBytes p (Bytes.byte_of_int (p-1)) //TODO: NS REVIEW!


// plain record ---encode---> plaintext bytes

val encode:
      e:id{ ~ (safeId e) } ->
      tlen:nat {tlen <= max_TLSCipher_fragment_length} ->
      rg:range {tlen = targetLength e rg} ->
      ad: LHAEPlain.adata e ->
      pl: LHAEPlain.plain e ad rg ->
      tag: MAC.tag ->
      Tot (lbytes (plainLength e tlen))

let encode (e:id) (tlen:nat) (rg:range) (ad:LHAEPlain.adata e) pl tag =
    let b = payload e rg ad pl in
    match e.aeAlg with
    // no padding
    | MACOnly(mac)
    | MtE (Stream CoreCrypto.RC4_128) mac ->
        let (_,h) = rg in
        assert(length b = h);
        let payload = b @| tag in
        assert(length payload = tlen - ivSize e);
        payload
    // padding
    | MtE (Block alg) mac ->
        let plen = tlen - length b - length tag - ivSize e in
        assert(plen > 0 && plen <= 256);
        let payload = b @| tag @| pad plen in
        assert(length payload = tlen - ivSize e);
        payload

// plain record <---decode--- plaintext bytes

val decode:
      e:id{ ~ (authId e) }  ->
    	ad: LHAEPlain.adata e ->
	    rg: range ->
	    tlen: nat{
        tlen - ivSize(e) >= ( macKeySize(macAlg_of_id e) + fixedPadSize e ) &&
        rg = cipherRangeClass e tlen} ->
	    payload: lbytes (plainLength e tlen) ->
      p: plain e ad rg
      { p.ok <==> payload = encode e tlen rg ad p.plain p.tag }

let decode (e:id) (ad:LHAEPlain.adata e) (rg:range) (tlen:nat) payload =
    match e.aeAlg with
    // no padding
    | MACOnly(hashAlg)
    | MtE (Stream CoreCrypto.RC4_128) hashAlg ->
        assert(tlen = length payload + ivSize e);
        let (fragment, tag) = Bytes.split payload (length payload - macSize (macAlg_of_id e)) in
        { plain = LHAEPlain.mk_plain e ad rg fragment;
          tag   = tag;
          ok    = true; }

    // padding
    | MtE (Block(encAlg)) hashAlg ->
        let fp = fixedPadSize e in
        let pLen = length payload in
        let (tmpdata, padlenb) = Bytes.split payload (pLen - fp) in
        let padlen = int_of_bytes padlenb in
        let padstart = pLen - (padlen + fp) in
        let macstart = padstart - macSize (macAlg_of_id e) in
        if macstart < 0 then
            (*@ Evidently padding has been corrupted, or has been incorrectly generated;
                following TLS1.1 we fail later (see RFC5246 6.2.3.2 Implementation Note) *)
            let (fragment, tag) = split tmpdata (pLen - macSize (macAlg_of_id e) - fp) in
            { plain = LHAEPlain.mk_plain e ad rg fragment;
              tag   = tag;
              ok    = false; }
        else
            let (actual,pad) = split tmpdata padstart in
            let correctPadding =
              match pv_of_id e with
              | TLS_1p0 | TLS_1p1 | TLS_1p2 ->
                (*@ We note a small timing leak here: the run time of the following two
                    lines depends on padding length. We could mitigate it by implementing
                    constant time comparison up to maximum padding length.*)
                  let expected = createBytes padlen (Bytes.byte_of_int padlen) in
                  equalBytes expected pad

              | SSL_3p0 ->
                (*@ Padding is random in SSL_3p0, no check to be done on its content.
                    However, its length should be at most one bs
                    (See sec 5.2.3.2 of SSL 3 draft). *)
                  padlen + fp <= blockSize encAlg in

            if correctPadding then
                let (fragment, tag) = split actual macstart in
                { plain = LHAEPlain.mk_plain e ad rg fragment;
                  tag   = tag;
                  ok    = true; }
            else
                let (fragment, tag) = split tmpdata (pLen - macSize (macAlg_of_id e) - fp) in
                { plain = LHAEPlain.mk_plain e ad rg fragment;
                  tag   = tag;
                  ok    = false; }

// now almost as encode/decode... share?

// minimal cipher length for MEE
val minTlen: id -> Tot nat

let minTlen i =
  match i.aeAlg with
  | MACOnly hashAlg
  | MtE (Stream CoreCrypto.RC4_128) hashAlg -> macSize (macAlg_of_id i)
  | MtE (Block encAlg) hashAlg -> ivSize i + macSize (macAlg_of_id i) + fixedPadSize i

// This property should follow by case analysis on all
// enc/mac algorithms of TLS (see TLSConstants.fs7)
let test1 _ = assert (forall e h. blockSize e <= macSize h)

let test2 _ = assert (forall (i:id) enc mac.
    i.aeAlg = MtE (Block enc) mac ==> minTlen i >= blockSize enc)

val mk_plain:
  e:id{ ~ (authId e) } ->
  ad: LHAEPlain.adata e ->
  tlen:nat{
    tlen >= minTlen e &&
    tlen <= max_TLSCipher_fragment_length } ->
  lbytes (plainLength e tlen) ->
  plain e ad (cipherRangeClass e tlen)

let mk_plain (e:id) ad tlen b =
  decode e ad (cipherRangeClass e tlen) tlen b

val repr:
  e:id{ ~ (safeId e) } ->
  ad: LHAEPlain.adata e ->
  rg:range -> //AP {rg is fRange}
  plain e ad rg ->
  b: lbytes (plainLength e (targetLength e rg))
  { targetLength e rg <= max_TLSCipher_fragment_length }
  // should that be a property of targetLength?

let repr (e:id) ad rg pl =
  encode e (targetLength e rg) rg ad pl.plain pl.tag

module Encode

(* The "plain" file for CPA encryption (module ENC) *)
(* provided by LHAE,
   implementing LHAEPlain @| MAC @| padding when using MtE
   
   When safeId, substituting zeros for plaintexts

   16-01-04 verifies with temporary assumptions; TBC
 *)

open FStar.Seq
open Platform
open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo
open Range

// for now, we *exclude* MACOnly

type id = i:id { ID12? i /\ MtE? (aeAlg_of_id i) } 

// tmp
type tagt (i:id) = MAC.tag i

(* Interface towards ENC (conditionally abstract) *)

// the result of decrypting & decoding, with an abstract type for secrecy
private type plain (i:id) (ad: LHAEPlain.adata i) (rg:range) = | Plain:
  f: LHAEPlain.plain i ad rg ->
  tag: tagt i ->

  // did decoding succeed? stateful? always true with RC4.
  ok : bool { MACOnly? (aeAlg_of_id i) \/ (encAlg_of_id i = (Stream CoreCrypto.RC4_128, Fresh) ==> ok = true) } -> 
  plain i ad rg 

// should we index just by plaintext lengths, rather than ad & range?
type dplain (i:id) (l:nat {valid_clen i l}) = ( ad:LHAEPlain.adata i &  plain i ad (cipherRangeClass i l) )

val plainLength: i:id -> clen: nat { clen >= ivSize i } -> Tot nat
let plainLength i clen = clen - ivSize i


(* Interface towards LHAE *)

//private val zeros: r:range -> rbytes r
let zeros (rg:range) = createBytes (snd rg) 0z

val payload: i:id -> r:frange i -> ad:LHAEPlain.adata i->
  LHAEPlain.plain i ad r -> Tot (rbytes r) //$ we had?: { SafeId e }

// the MACed bytes, i.e. ad @| 2-byte length of payload @| payload
//CF should ask some injectivity

let payload (i:id) (rg:frange i) ad f =
  // After applying CPA encryption for ENC,
  // we access the fragment bytes only at unsafe indexes, and otherwise use some zeros
  if safeId i then zeros rg
  else LHAEPlain.repr i ad rg f

val macPlain_bytes:
  i:id -> r:frange i -> LHAEPlain.adata i -> rbytes r -> Tot bytes

let macPlain_bytes i rg ad b = 
  lemma_repr_bytes_values (length b); 
  ad @| vlbytes 2 b

val macPlain: i:id -> r:frange i ->
  $ad:LHAEPlain.adata i ->
  $f:LHAEPlain.plain i ad r ->
  Tot bytes // (tagt i) // ?(b:bytes{ safeId i })
let macPlain i rg ad f =
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

(*
//#if ideal
type maconly_entry =
    i:id * ad:LHAEPlain.adata i * rg:range * tlen:nat *
     payload:bytes * text:bytes * p:LHAEPlain.plain i ad rg * MAC.tag
  { authId i /\ //
    tlen <= max_TLSCiphertext_fragment_length /\ tlen = targetLength i rg /\ //
    MACOnly? (aeAlg_of_id i) /\ //
    MAC.Msg(i,text) /\ //
    text = MACPlain i rg ad p /\ //
    payload = LHAEPlain.Payload i ad rg p
  }

private val maconly_log: maconly_entry list ref
private val maconly_mem:
	i:id{AuthId(i) /\ (?mac. (aeAlg_of_id i) = MACOnly(mac))} ->
	ad:(;i)LHAEPlain.adata -> tlen:nat{tlen <= max_TLSCiphertext_fragment_length} ->
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
//#endif
*)

val mac: i:id -> k:MAC.key i (fun _ -> True) -> ad:LHAEPlain.adata i -> rg:frange i -> p:LHAEPlain.plain i ad rg -> plain i ad rg
let mac i k ad rg plain =
    let p = LHAEPlain.makeExtPad i ad rg plain in
    let text = macPlain i rg ad p in
    let tag  = MAC.mac k text in
(*
//#if ideal
    (* For MACOnly ciphersuites where AuthId holds, we store the plain and
     * the tag in the MACOnly log *)
    let e_aealg = (aeAlg_of_id i) in
    let auth = authId i in
    if auth = true then
      (match (e_aealg) with
       | MACOnly(_) ->
          let tlen = targetLength i rg in
          let pl = payload i rg ad p in
          maconly_log := (i,ad,rg,tlen,pl,text,p,tag)::!maconly_log
       | _ -> ())
     else ();
//#endif
*)
    Plain p tag true


// val verify_MACOnly:
//   e: id{ ~ (safeId e) /\ MACOnly? e.aeAlg } ->
//   k: MAC.key ->
//   ad: LHAEPlain.adata e ->
//   rg: range ->
//   tlen: nat{
//     tlen <= max_TLSCiphertext_fragment_length /\//
//     rg = cipherRangeClass e tlen
//     } ->
//   b: rbytes rg ->
//   t: MAC.tag ->
//   result (LHAEPlain.plain e ad (cipherRangeClass e tlen))
//
// let verify_MACOnly (e:id) k (ad:LHAEPlain.adata e) (rg:range) (cl:nat) b tag 
//   (*: result (LHAEPlain.plain e ad rg)*)
//   =
//   let text = macPlain_bytes e rg ad b in
//   if MAC.verify e k text tag then
//   #if ideal
//     if authId e then
//       match maconly_mem e ad cl b text tag !maconly_log with
//       | Some(x) ->
//           let (rg',p') = x in
//           let p = LHAEPlain.widen e ad rg' p' in
//           let rg = rangeClass e rg' in
//           Correct p
//       | None ->
//           Error(AD_bad_record_mac,perror __SOURCE_FILE__ __LINE__ "")
//     else
//   #endif
//           let p = LHAEPlain.mk_plain e ad rg b in
//           Correct p
//   else
//           Error(AD_bad_record_mac,perror __SOURCE_FILE__ __LINE__ "")

val verify:
  i:id ->
  k: MAC.key i (fun _ -> True) ->
  ad: LHAEPlain.adata i ->
  rg: frange i ->
  p: plain i ad rg ->
  result (LHAEPlain.plain i ad rg)

let verify (i:id) k ad rg p =
    let text = macPlain i rg ad p.f in
        (*@ We implement standard mitigation for padding oracles.
            Still, we note a small timing leak here:
            The time to verify the mac is linear in the plaintext length. *)
    let v = MAC.verify k text p.tag in
    if v && p.ok
    then Correct p.f 
    else Error(AD_bad_record_mac,"")

(* KB we need to add some refinement to ensure that verify
   will not fail for MACed values *)
(* CF we may need something like
   safeId e ==> Version(e) = TLS_1p1 \/ Version(e) = TLS_1p2 \/ ps.ok = true
*)


// padding in TLS: [| 0z |], [| 1z; 1z |], ...

val pad: l:nat { 0 < l /\ l <= 256 } -> Tot(lbytes l)
// we may need a more precise refinement for the MEE proof:
// the last byte of padding determines the padding

let pad p  = createBytes p (Bytes.byte_of_int (p-1)) //TODO: NS REVIEW!


// plain record ---encode---> plaintext bytes
val encode:
      i:id{ ~ (authId i) } -> // was not safeId i
      ad: LHAEPlain.adata i ->
      rg:range {
        snd rg <= max_TLSPlaintext_fragment_length /\ 
        snd rg - fst rg <= maxPadSize i - minimalPadding i (snd rg + macSize (macAlg_of_id i)) } ->
      pl: LHAEPlain.plain i ad rg ->
      tag: MAC.tag i ->
      Tot (lbytes (plainLength i (targetLength i rg)))
let encode i ad rg pl tag =
    let tlen = targetLength i rg in
    let b = payload i rg ad pl in
    match (aeAlg_of_id i) with
    // no padding
    | MACOnly(mac)
    | MtE (Stream CoreCrypto.RC4_128) mac ->
        let (_,h) = rg in
        assert(length b = h);
        let payload = b @| tag in
        assert(length payload = tlen - ivSize i);
        payload
    // padding
    | MtE (Block alg) mac ->
        let plen = tlen - length b - length tag - ivSize i in
        // assert(0 < plen && plen <= 256);
        let payload = b @| tag @| pad plen in
        // assert(length payload = tlen - ivSize i);
        payload
// plain record <---decode--- plaintext bytes


val decode:
      i:id{ ~ (authId i) }  ->
      ad: LHAEPlain.adata i ->
      tlen: nat{
        valid_clen i tlen /\
        tlen - ivSize i >= macKeySize(macAlg_of_id i) + fixedPadSize i /\
        ( let rg = cipherRangeClass i tlen in
//          StatefulPlain.wf_ad_rg i (LHAEPlain.parseAD ad) rg /\
          snd rg - fst rg <= maxPadSize i - minimalPadding i (snd rg + macSize (macAlg_of_id i))) } ->
      payload: lbytes (plainLength i tlen) ->
      p: plain i ad (cipherRangeClass i tlen)
      { pv_of_id i <> SSL_3p0 ==> (b2t (p.ok) <==> (payload == encode i ad (cipherRangeClass i tlen) p.f p.tag ))}


assume val lemma_pad: lx: nat { lx < 256 } ->
  Lemma ((createBytes lx (Bytes.byte_of_int lx) @| createBytes 1 (Bytes.byte_of_int lx)) = pad (lx+1))
  

let decode i ad tlen payload =
    let pv = pv_of_id i in
    let l = length payload in
    let lt = macSize (macAlg_of_id i) in
 
    let rg : frange i = cipherRangeClass i tlen in
    assume(StatefulPlain.wf_ad_rg i (LHAEPlain.parseAD ad) rg);
    match (aeAlg_of_id i) with
    // no padding: we expect l = lf + lt
    | MACOnly hashAlg
    | MtE (Stream CoreCrypto.RC4_128) hashAlg ->
        assert(tlen = l + ivSize i);
        let lf = l - lt in
        let (fragment, tag) = Bytes.split payload lf in
        lemma_split payload lf; // could be automated!
        let p = LHAEPlain.mk_plain i ad rg fragment in
        assume( ~ (safeId i)); // should follow from their definitions
        assert(payload = encode i ad rg p tag);
        Plain p tag true

    // padding: we expect l = lf + lt + lx + lp bytes and tlen = lf + lx
    | MtE (Block encAlg) hashAlg ->
        let lp = fixedPadSize i in
        assert(lp = 1);
        let (ftx,b) = Bytes.split payload (l - lp) in
        lemma_split payload (l - lp); // could be automated!
        let lx = int_of_bytes b in
        assert( lx >= 0 /\ lx < 256);
        let lft = l - (lx + lp) in
        let lf  = lft - lt in
        if lf < 0 then
            (*@ Evidently padding has been corrupted, or has been incorrectly generated;
                following TLS1.1 we fail later (see RFC5246 6.2.3.2 Implementation Note) *)
            let (f, tag) = split ftx (l - lt - lp) in
            lemma_split ftx (l - lt - lp);
            let p = LHAEPlain.mk_plain i ad rg f in
            assume(~(payload == encode i ad rg p tag ));
            Plain p tag false
        else
            let (ft,x) = split ftx lft in
            let correctPadding: c:bool { c /\ pv <> SSL_3p0 ==> (x @| b) = pad (lx+1) } =
              match pv with
              | SSL_3p0 ->
                (*@ Padding is random in SSL_3p0, no check to be done on its content.
                    However, its length should be at most one bs
                    (See sec 5.2.3.2 of SSL 3 draft). *)
                  lx + lp <= CoreCrypto.blockSize encAlg

              | TLS_1p0 | TLS_1p1 | TLS_1p2 ->
                (*@ We note a small timing leak here: the run time of the following two
                    lines depends on padding length. We could mitigate it by implementing
                    constant time comparison up to maximum padding length.*)
                  let expected = createBytes lx (Bytes.byte_of_int lx) in
                  if x = expected then
                    ( lemma_pad lx;
                      assume(b = createBytes 1 (Bytes.byte_of_int lx));
                      assert((x @| b) = pad (lx+1));
                      true )
                  else false

               | _ -> false in

            if correctPadding then (
                let (f, tag) = split ft lf in
                lemma_split ft lf;
                assume(within lf rg);
                let p = LHAEPlain.mk_plain i ad rg f in
                assume (safeId i ==> authId i);
                assume((pv <> SSL_3p0 /\
                  (x @| b = pad (lx+1))) ==>
                  (f @| tag @| (x @| b) = encode i ad rg p tag) /\
                  payload = encode i ad rg p tag);
                Plain p tag true )
            else (
                let lf = l - lt - lp in  // faking minimal padding (lx = 0)
                assume(within lf rg);
                let (f, tag) = split ftx lf in
                lemma_split ftx lf;
                let p = LHAEPlain.mk_plain i ad rg f in
                assume(payload <> encode i ad rg p tag );
                Plain p tag false )

(*
// now almost as encode/decode... share?

// minimal cipher length for MEE
let minTlen (i:id) =
  match (aeAlg_of_id i) with
  | MACOnly hashAlg
  | MtE (Stream CoreCrypto.RC4_128) hashAlg -> macSize (macAlg_of_id i)
  | MtE (Block encAlg) hashAlg -> ivSize i + macSize (macAlg_of_id i) + fixedPadSize i

(*
// This property should follow by case analysis on all
// enc/mac algorithms of TLS (see TLSConstants.fs7)
let test1 _ = assert (forall e h. blockSize e <= macSize h)

let test2 _ = assert (forall (i:id) enc mac.
    (aeAlg_of_id i) = MtE (Block enc) mac ==> minTlen i >= blockSize enc)
*)

val mk_plain:
  i:id{ ~ (authId i) } ->
  ad: LHAEPlain.adata i ->
  tlen:nat{
    tlen >= minTlen i /\
    tlen <= max_TLSCiphertext_fragment_length /\
    valid_clen i tlen
  } ->
  lbytes (plainLength i tlen) ->
  plain i ad (cipherRangeClass i tlen)

let mk_plain i ad tlen b =
  admit();
  decode i ad tlen b
*)

val repr:
  i:id{ ~ (authId i) } -> // was { ~ (safeId i) }
  ad: LHAEPlain.adata i ->
  rg:range { snd rg <= max_TLSPlaintext_fragment_length /\
             snd rg - fst rg <= maxPadSize i - minimalPadding i (snd rg + macSize (macAlg_of_id i)) } ->
  plain i ad rg ->
  b: lbytes (plainLength i (targetLength i rg))
  { targetLength i rg <= max_TLSCiphertext_fragment_length }
  // should that be a property of targetLength?

let repr i ad rg pl =
  encode i ad rg pl.f pl.tag

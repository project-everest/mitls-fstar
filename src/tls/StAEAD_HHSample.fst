(*--build-config
    options:--prims ../tls-ml/prims.fst --codegen-lib CoreCrypto --codegen-lib Platform --codegen-lib Classical --codegen-lib SeqProperties --verify_module StAEAD_HHSample --admit_fsi Seq --admit_fsi StatefulPlain --admit_fsi LHAEPlain --admit_fsi SessionDB --admit_fsi UntrustedCert --admit_fsi DHDB --admit_fsi CoreCrypto --admit_fsi Cert --admit_fsi Map --admit_fsi Seq --admit_fsi HyperHeap --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 10;
    other-files:../../../FStar/lib/string.fst ../../../FStar/lib/list.fst ../../../FStar/lib/FStar.FunctionalExtensionality.fst ../../../FStar/lib/classical.fst ../../../FStar/lib/FStar.Set.fsi ../../../FStar/lib/FStar.Set.fst ../../../FStar/lib/FStar.Heap.fst ../../../FStar/lib/FStar.ST.fst ../../../FStar/lib/map.fsi ../../../FStar/lib/hyperheap2.fsi ../../../FStar/lib/seq.fsi ../../../FStar/lib/seqproperties.fst ../../../FStar/lib/int64.fst ../../../FStar/contrib/Platform/fst/Bytes.fst ../../../FStar/contrib/Platform/fst/Date.fst ../../../FStar/contrib/Platform/fst/Error.fst ../../../FStar/contrib/Platform/fst/Tcp.fst ../../../FStar/contrib/CoreCrypto/fst/CoreCrypto.fst ../../../FStar/contrib/CoreCrypto/fst/DHDB.fst TLSError.p.fst Nonce.p.fst TLSConstants.p.fst RSAKey.p.fst DHGroup.p.fst ECGroup.p.fst CommonDH.p.fst PMS.p.fst HASH.p.fst HMAC.p.fst ../tls-lax/Sig.p.fst UntrustedCert.p.fsti Cert.p.fsti TLSInfo.p.fst TLSExtensions.p.fst TLSPRF.p.fst Range.p.fst DataStream.p.fst StatefulPlain.p.fsti LHAEPlain.p.fst AEAD_GCM.fst StatefulLHAE.fst
  --*)

module StAEAD_HHSample

// usability test: write code for encrypting/decrypting lists

// can we take adata and plain as type parameters?
// for now reusing StatefulLHAEPlain

open Platform.Bytes
open TLSError
open TLSInfo
open StatefulPlain
open AEAD_GCM
open StatefulLHAE
open Range
open FStar.HyperHeap


// keeping indexes constant for simplicity
assume val i: gid
assume val ad: adata i

// would be nicer to compute forward, e.g.

let rg =
  (1,10)

let clen = targetLength i (1,10)

(*assume val clen: n:nat { n <= max_TLSCipher_fragment_length }
assume val rg: r:range { r = Range.cipherRangeClass i clen }*)

let test () =
  assert False

assume val p: fragment i ad rg


type block = c:cipher { length c = clen }




//MK: I am declaring these as unit functions as otherwise I get a
//    "Effects STATE and ALL do not compose" error
//    clearly wrong, means that I generate fresh keys on every call
let both () =
  assert False;
  gen root i
// how to gracefully bind both keys at toplevel?

//val wr: writer i
let wr () = snd ( both () )

//val rd: reader i
let rd () = fst ( both () )

// Required to avoid unification failure?
val access: e: entry i { Entry.ad e = ad /\ length (Entry.c e) = clen } ->
  Tot (fragment i ad rg)
let access e =
  Entry.p e

(* we need our own invariant:
   the first n Entries are those we protected
   with matching ad, length c, and p *)

(* for now, this declaration is not even sufficient to encrypt without establishign that invariant *)

val protect: inputs: list (fragment i ad rg) ->
  ST (list block)
     (requires (fun h -> True
       (*/\ (forall (n:nat) . (n <= List.length (sel h (StWriter.log ( wr () ) )) + List.length inputs ==> is_seqn n))*)
      ))
     (ensures (fun h0 (cs:list block)  h1 -> True
       /\ HyperHeap.modifies (Set.singleton ( root )) h0 h1 //root was StWriter.region (wr () )
       // both still missing type annotations
       // /\ inputs = List.mapT
       //   #(e: entry i) // { Entry.ad e = ad /\ length (Entry.c e) = clen })
       //   #(fragment i ad rg)
       //   access
       //   (sel h1 (StWriter.log wr))
       // /\ cs = List.mapT #_ #block (fun e -> Entry.c e) (sel h1 (StWriter.log wr))
      ))


val tailT: l:list 'a { l <> [] } -> Tot (list 'a)
let tailT l =
  match l with _::l -> l

val cons_length: l: list 'a { l <> [] }-> Lemma
  (requires True)
  (ensures  (List.length l = List.length (tailT l) + 1))
let cons_length l = ()

let rec protect (inputs: list (fragment i ad rg)) =
  assert False;
  match inputs with
  | p::inputs' -> cons_length inputs;
                  let wr = wr () in
                  let b = encrypt #i #ad #rg wr p in
                  (*let n1 = Seq.length !(StWriter.log wr ) in*)
                  (*cons_length !(StWriter.log wr);*)
                  (*cut (forall (n:nat) . (n <= n1 + List.length inputs' ==> is_seqn n));*)
                  (*cut (exists fpe. List.mem fpe fp1 /\ FPEntry.i fpe = i /\ FPEntry.w fpe = wr);*)
                  let bs = protect inputs' in
                  (*admit(); *)
                  // otherwise ``Unknown assertion failed''
                  b :: bs
  | []         -> []

val unprotect: cs: list (c:cipher { length c = clen }) ->
  ST (option (list (fragment i ad rg)))
  (requires (fun h -> True ))
       (*fp_inv h
    /\ ReaderOk rd h
    /\ reader_in_fp rd h
    /\ (forall (n:nat) . (n <= sel h (StReader.seqn rd) + List.length cs ==> is_seqn n))
       ))*)
  (ensures (fun h0 inputs h1 -> True))

  // painful.
  (*(modifies (SomeRefs(Set.union (Set.singleton (Ref (StReader.seqn rd)))
                     (Set.union (Set.singleton (Ref (StReader.live rd)))
                                (Set.singleton (Ref (StReader.key rd).counter))))))*)

let rec unprotect cs =
  match cs with
  | c :: cs' ->
      (*cons_length cs;*)
      let rd = rd () in
      let n0 = !(StReader.seqn rd) in
      (match decrypt #i #ad rd c with
      | Some p ->
          let n1 = !(StReader.seqn rd) in
          (*admitP (b2t(n1 = n0 + 1));*)
          let ops = unprotect cs' in
          (match ops with
          | Some ps -> Some (p :: ps)
          | None    -> None)
      | None        -> None)
  | []              -> Some []


val test: unit -> ST unit
  (requires (fun h -> True))
  (ensures (fun _ _ _ -> True))

// could also use some cutST
assume val admitST: phi: (HyperHeap.t -> Type) -> ST (unit)
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1 /\ phi h1 ))

assume val cutST: phi: (HyperHeap.t -> Type) -> ST (unit)
  (requires phi)
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1 /\ phi h0 )) //MK: typo in StAEADSample.fst not quite sure what it should do.

// can we have an equivalent of admit for heaps

let test () =
  // not sure how to thread state between toplevel bindings...

  admitP(forall (n:nat).(n <= 5 ==> is_seqn n));
  let ps0 = [p;p] in
  let ps1 = [p;p;p] in
  admitP(b2t(List.length ps0 <= 2)); // fuel problem?
  admitP(b2t(List.length ps1 <= 3)); // fuel problem?
  let wr = wr () in
  admitST(fun h -> True
    (*/\ b2t (sel h (StWriter.log wr) = [])*)
    );
  let c0 = protect ps0 in
  let c1 = protect ps1 in // chaining is working fine
  admit();
  let d0 = unprotect c0 in
  let d1 = unprotect c1 in
  assert False //(b2t(d0 = Some ps0))

(* check_marker *)

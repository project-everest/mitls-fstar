(*--build-config
    options:--trace_error --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 100 --admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.Heap --admit_fsi FStar.HyperHeap --admit_fsi FStar.Seq.Base --admit_fsi FStar.Char --admit_fsi FStar.Seq.Properties --admit_fsi SessionDB --admit_fsi UntrustedCert --admit_fsi DHDB --admit_fsi CoreCrypto --admit_fsi Cert --admit_fsi StatefulLHAE --verify_module StAEADSample;

    variables: CONTRIB=../../FStar/contrib;
    other-files:FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.Base.fst FStar.HyperHeap.fsi stHyperHeap.fst allHyperHeap.fst char.fsi FStar.String.fst FStar.List.Tot.Properties.fst FStar.List.Tot.fst FStar.List.fst seq.fsi FStar.Seq.Properties.fst $CONTRIB/Platform/fst/Bytes.fst $CONTRIB/Platform/fst/Date.fst $CONTRIB/Platform/fst/Error.fst $CONTRIB/Platform/fst/Tcp.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst $CONTRIB/CoreCrypto/fst/DHDB.fst TLSError.fst Nonce.p.fst TLSConstants.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fst Cert.fst TLSInfo.fst Range.p.fst DataStream.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fst
--*)
module StAEADSample

// usability test: write code for encrypting/decrypting lists

// can we take adata and plain as type parameters?
// for now reusing StatefulLHAEPlain


open Platform

open Platform.Bytes
open TLSError
open TLSInfo
open StatefulPlain
open AEAD_GCM
open StatefulLHAE
open Range
open FStar.Heap
open FStar.HyperHeap

// dummies
type fp_inv h = True
type writer_in_fp wr h = True


// keeping indexes constant for simplicity
assume val i: gid

assume val ad: adata i

assume val clen: n:nat { valid_clen i n  }

assume val rg: rg:range { rg = Range.cipherRangeClass i clen }

assume val p: plain i ad rg

type block = c:cipher i{ length c = clen }
// would be nicer to compute forward, e.g.
// let clen = targetLength i rg

(* check_marker *)

let both =
(*
  let fp0 = !fp in
  assume(fp0 = []);
  recall fp;
  // these do not suffice to prove the precondition of gen
  // not sure how intermediate top-level bindings affect stateful invariants :(
  admit();
*)
  gen FStar.HyperHeap.root i
// how to gracefully bind both keys at toplevel?

// we also need to know that the keys are in fp_log to recall their invariant
// a good case for mref?

//val wr: writer i
let wr = snd both

//val rd: reader i
let rd = fst both

// Required to avoid unification failure?
val access: e: entry i { Entry?.ad e = ad /\ length (Entry?.c e) = clen } ->
  Tot (plain i ad rg)
let access e =
  Entry?.p e

(* not sure how to specify it...
val mapST: ('a -> Tot 'b) -> list 'a -> ST (list 'b)
let rec mapT f x = match x with
  | [] -> []
  | a::tl -> f a::mapT f tl
*)

(* we need our own invariant:
   the first n Entries are those we protected
   with matching ad, length c, and p *)

(* for now, this declaration is not even sufficient to encrypt without establishign that invariant *)

val protect: (inputs:list (plain i ad rg)) ->
  ST (list block)
     (requires (fun h ->
         fp_inv h
      /\ writer_in_fp wr h
//      /\ (exists fpe. List.mem fpe (Heap.sel h fp) /\ FPEntry?.i fpe = i /\ FPEntry?.w fpe = wr)
      /\ (forall (n:nat) . (n <= Seq.length (sel h (StWriter.log wr)) + List.length inputs ==> is_seqn n))
      ))
     (ensures (fun h0 (cs:list block) h1 ->
        fp_inv h1
      /\ writer_in_fp wr h1
//      /\ (exists fpe. List.mem fpe (Heap.sel h1 fp) /\ FPEntry?.i fpe = i /\ FPEntry?.w fpe = wr)
      // both still missing type annotations
      // /\ inputs = List.mapT
      //   #(e: entry i) // { Entry?.ad e = ad /\ length (Entry?.c e) = clen })
      //   #(plain i ad rg)
      //   access
      //   (sel h1 (StWriter.log wr))
      // /\ cs = List.mapT #_ #block (fun e -> Entry?.c e) (sel h1 (StWriter.log wr))
      /\ modifies (Set.singleton (StWriter.region wr)) h0 h1
      /\ modifies_rref (StWriter.region wr) (refs_in_e wr) h0 h1))

val tailT: l:list 'a { l <> [] } -> Tot (list 'a)
let tailT l =
  match l with _::l -> l

val cons_length: l: list 'a { l <> [] }-> Lemma
  (requires True)
  (ensures  (List.length l = List.length (tailT l) + 1))
let cons_length l = ()

let rec protect (inputs: list (plain i ad rg)) =
  match inputs with
  | p::inputs' -> cons_length inputs;
                 let b = encrypt #i #ad #rg wr p in
                 let n1 = Seq.length !(StWriter.log wr) in
                 cut (forall (n:nat) . (n <= n1 + List.length inputs' ==> is_seqn n));
                 let bs = protect inputs' in
                 admit(); // otherwise ``Unknown assertion failed''
                 b :: bs
  | []         -> []

let refs_in_d (#i:gid) (d:reader i) =
  !{ as_ref (StReader.seqn d), as_ref (State?.counter (StReader.key d)) }


val unprotect: cs:list (c:cipher i{length c = clen }) ->
  ST (option (list (plain i ad rg)))
  (requires (fun h ->
      fp_inv h
    // /\ ReaderOk rd h
    // /\ reader_in_fp rd h
    /\ (forall (n:nat) . (n <= sel h (StReader.seqn rd) + List.length cs ==> is_seqn n))
       ))
  (ensures (fun h0 inputs h1 -> 
      fp_inv h1
    /\ modifies (Set.singleton (StReader.region rd)) h0 h1
    /\ modifies_rref (StReader.region rd) (refs_in_d rd) h0 h1))

let rec unprotect cs =
  match cs with
  | c :: cs' ->
      cons_length cs;
      let n0 = !(StReader.seqn rd) in
      (match decrypt #i #ad rd c with
      | Some p ->
          let n1 = !(StReader.seqn rd) in
          admitP (b2t(n1 = n0 + 1));
          let ops = unprotect cs' in
          (match ops with
          | Some ps -> Some (p :: ps)
          | None    -> None)
      | None        -> None)
  | []              -> Some []

(*
val test: unit -> ST unit
  (requires (fun h -> True))
  (ensures (fun _ _ _ -> True))
  (modifies no_refs)
*)

(*
// could also use some cutST
assume val admitST: phi:(heap -> Type) -> ST unit
  (requires (fun _ -> True))
  (ensures  (fun _ _ h1 -> phi h1))
  (modifies Set.empty)

assume val cutST: phi: (heap -> Type) -> ST (unit)
  (requires phi)
  (ensures (fun h0 _ h1 -> phi h0))
  (modifies Set.empty)
*)

// can we have an equivalent of admit for heaps

let test =
  // not sure how to thread state between toplevel bindings...
  //let fp0 = !fp in
  // cut(b2t (List.length fp0 = 1));
  admitP(forall (n:nat).(n <= 5 ==> is_seqn n));
  let ps0 = [p;p] in
  let ps1 = [p;p;p] in
  admitP(b2t(List.length ps0 <= 2)); // fuel problem?
  admitP(b2t(List.length ps1 <= 3)); // fuel problem?
(*
  admitST(fun h ->
    fp_inv h /\
    // writer_in_fp wr h /\
    sel h (StWriter.log wr) = []
    );
*)
  let c0 = protect ps0 in
  let c1 = protect ps1 in // chaining is working fine
  admit();
  let d0 = unprotect c0 in
  let d1 = unprotect c1 in
  assert (b2t(d0 = Some ps0))

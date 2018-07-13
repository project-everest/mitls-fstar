(**
Provides authenticated encryption for a stream of variable-length plaintexts;
concretely, we use AES_GCM but any other AEAD algorithm would do.
*)
module StreamAE

module HST = FStar.HyperStack.ST //Added automatically

module HS = FStar.HyperStack 

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

open FStar.UInt32
//module Plain = Crypto.Plain

open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.Error
open FStar.Bytes

open FStar.Mul
open FStar.Bytes
open Mem
open Pkg
open TLSError
open TLSConstants
open TLSInfo

// plain i lmax: stream plaintext of length at most lmax
let plain i lmax = llbytes lmax

type counter = c:UInt32.t{UInt32.v c <= max_ctr}

let increases_u32 (x:U32.t) (y:U32.t)  = b2t (x <=^ y)

let ctr_ref (r:erid) (i:I.id) : Tot Type0 =
  m_rref r counter increases_u32

//aead_plain i l: aead plain of length exactly l
type aead_plain (i:I.id) (l:AEAD.plainLen) : t:Type0{hasEq t} = lbytes l

assume val pad: lmax:AEAD.plainLen -> p:llbytes lmax -> lbytes (lmax+1)
assume val unpad: #l:AEAD.plainLen{l>=1} -> p:lbytes l -> llbytes (l-1)

let plain_of_aead_plain
  (#i:I.id)
  (#l:AEAD.plainLen {l>=1})
 // (#l:AEAD.plainLen{l <= lmax})
  (p:aead_plain i l) : plain i (l-1) =
  unpad p

let cipher_of_aead_cipher
  (#i:I.id)
  (#l:AEAD.plainLen{l>=1})
  (c:AEAD.cipher i l) : cipher i (l-1) =
  c

let as_bytes (i:I.id) (l:AEAD.plainLen) (p:aead_plain i l) : GTot (lbytes l) = p

let repr (i:AEAD.unsafeid) (l:AEAD.plainLen) (p:aead_plain i l) : Tot (b:lbytes l{b == as_bytes i l p}) =
  p

//let f ($x: (I.id -> AEAD.plainLen -> t:Type0{hasEq t})) = True

//let _ = f (fun i l -> aead_plain i l)

//let _ = f aead_plain

let aead_plain_pkg = AEAD.PlainPkg aead_plain as_bytes repr

//let aead_plain_pkg = AEAD.PlainPkg (fun i l -> aead_plain i l) as_bytes repr

type aead_info (i:I.id) = u:(AEAD.info i){u.AEAD.plain == aead_plain_pkg}



noeq type stream_writer (i:I.id) =
  | Stream_writer:
    #region: rgn ->
    aead: AEAD.aead_writer i
      {(AEAD.wgetinfo aead).AEAD.plain == aead_plain_pkg /\
        ~ (Set.mem region (Set.union (AEAD.wfootprint aead) (AEAD.shared_footprint)))} ->
    iv: AEAD.iv (I.cipherAlg_of_id i) ->
    ctr: ctr_ref region i ->
    stream_writer i

noeq type stream_reader (#i:I.id) (w:stream_writer i) =
  | Stream_reader:
    #region: rgn ->
    aead: AEAD.aead_reader (Stream_writer?.aead w)
      {(AEAD.rgetinfo aead).AEAD.plain == aead_plain_pkg /\
      ~ (Set.mem region (Set.union (AEAD.rfootprint aead) (AEAD.shared_footprint)))} ->
    iv: AEAD.iv (I.cipherAlg_of_id i) ->
    ctr: ctr_ref region i ->
    stream_reader w

let uint32_to_uint128 (n:U32.t) : (m:U128.t{U32.v n == U128.v m /\ U128.v m <= pow2 32 - 1}) =
  U128.uint64_to_uint128 (Int.Cast.uint32_to_uint64 n)

assume val lem_xor :
  (n:nat) ->
  (x:U128.t{U128.v x <= pow2 n - 1}) ->
  (y:U128.t{U128.v y <= pow2 n - 1}) ->
  Lemma (requires True) (ensures U128.(v (x ^^ y)) <= pow2 n - 1)

val lem_powivlen : alg:I.cipherAlg -> Lemma (requires True) (ensures pow2 32 <= pow2 (8 * v (AEAD.ivlen alg)))
let lem_powivlen alg = Math.Lemmas.pow2_le_compat (8 * v (AEAD.ivlen alg)) 32

let create_nonce (#i:I.id) (iv: AEAD.iv (I.cipherAlg_of_id i)) (j:U32.t) : Tot (AEAD.nonce i) =
  lem_powivlen (I.cipherAlg_of_id i);
  lem_xor (8 * (v (AEAD.ivlen (I.cipherAlg_of_id i)))) iv (uint32_to_uint128 j);
  U128.(iv ^^ (uint32_to_uint128 j))


// ?? agility: cases AES and ChaCha20 (see AEADProvider)

let invariant (#i:I.id) (w:stream_writer i) (h:mem) =
  AEAD.winvariant (Stream_writer?.aead w) h /\
  (if safeId i then
    let wc = sel h (Stream_writer?.ctr w) in
    let wlg = AEAD.wlog (Stream_writer?.aead w) h in
    let iv = Stream_writer?.iv w in
    UInt32.v wc = Seq.length wlg /\
    (forall e. Seq.mem e wlg ==> AEAD.Entry?.l e >= 1) /\
    (forall (j:U32.t). (v j < v wc) ==> AEAD.Entry?.nonce (Seq.index wlg (v j)) = create_nonce iv j)
  else
    True)

let pref (#t:Type) (s:Seq.seq t) (k:nat{k <= Seq.length s}) =
  Seq.Base.slice s 0 k

let rinvariant (#i:I.id) (#w:stream_writer i) (r:stream_reader w) (h:mem) =
  let wc = sel h (Stream_writer?.ctr w) in
  let rc = sel h (Stream_reader?.ctr r) in
  AEAD.winvariant (Stream_writer?.aead w) h /\
  rc <=^ wc /\
  Stream_writer?.iv w = Stream_reader?.iv r (*/\
  (if safeId i then
    let wlg = AEAD.wlog (Stream_writer?.aead w) h in
    let rlg = AEAD.rlog (Stream_reader?.aead r) h in
    v wc == Seq.length wlg /\
    v rc == Seq.length rlg /\
    rlg == pref wlg (v rc)
  else
    True)*)

let wctrT (#i:I.id) (w:stream_writer i) (h:mem) =
  v (sel h (Stream_writer?.ctr w)) 

let wctr (#i:I.id) (w:stream_writer i) =
  !(Stream_writer?.ctr w)

let rctrT (#i:I.id) (#w:stream_writer i) (r:stream_reader w) (h:mem) =
  v (sel h (Stream_reader?.ctr r)) 

let rctr (#i:I.id) (#w:stream_writer i) (r:stream_reader w) =
  !(Stream_reader?.ctr r)


let stream_entry_of_aead_entry (#i:I.id) (#u:aead_info i) (e:AEAD.entry i u {AEAD.Entry?.l e >= 1}) =
  match e with
    | AEAD.Entry nonce ad #l p c ->
      Entry ad (plain_of_aead_plain p) (cipher_of_aead_cipher c)

let seqmap (#t:Type) (#t':Type) (f:(t -> t')) (s:seq t) : (s':seq t'{Seq.length s = Seq.length s'}) =
  Seq.init (Seq.length s) (fun j -> f (Seq.index s j))

let wlog (#i:safeid) (w:stream_writer i) (h:mem) =
  let wlg = AEAD.wlog (Stream_writer?.aead w) h in
//  seqmap stream_entry_of_aead_entry wlg
  magic()
  
let rlog (#i:safeid) (#w:stream_writer i) (r:stream_reader w) (h:mem) =
  let wlg = AEAD.wlog (Stream_writer?.aead w) h in
//  pref (seqmap stream_entry_of_aead_entry wlg) (rctrT r h)
  assume False; magic()


let shared_footprint #i w = AEAD.shared_footprint

let footprint #i w =
  magic()
//  Set.union (AEAD.wfootprint (Stream_writer?.aead w)) (Set.singleton (Stream_writer?.region w))

let rfootprint #i #w r =
  magic()//  Set.union (AEAD.rfootprint (Stream_reader?.aead r)) (Set.singleton (Stream_reader?.region r))

let frame_invariant #i w h0 ri h1 = admit()
let rframe_invariant #i #w r h0 ri h1 = admit()

let aead_info_of_info (#i:I.id) (u:info i) : AEAD.info i =
  {AEAD.alg= u.alg; AEAD.prf_rgn=u.shared; AEAD.log_rgn=u.local; AEAD.plain=aead_plain_pkg}
  
let create (parent:rgn) (i:I.id) (u:info i) =
  let w = AEAD.gen i (aead_info_of_info u) in
  Stream_writer w
  


(*type rid = HST.erid

type id = i:id { ID13? i } *)

(*let alg (i:id) =
  let AEAD ae _ = aeAlg_of_id i in ae

let ltag i : nat = CoreCrypto.aeadTagSize (alg i)
let cipherLen i (l:plainLen) : nat = l + ltag i
type cipher i (l:plainLen) = lbytes (cipherLen i l)
*)

// will require proving before decryption
(*let lenCipher i (c:bytes { ltag i <= length c }) : nat = length c - ltag i

// key materials (from the AEAD provider)
type key (i:id) = AEAD.key i
type iv  (i:id) = AEAD.salt i
 
let ideal_log (r:erid) (i:id) = log_t r (entry i)

let log_ref (r:erid) (i:id) : Tot Type0 =
  if authId i then ideal_log r i else unit

let ilog (#r:erid) (#i:id) (l:log_ref r i{authId i}) : Tot (ideal_log r i) =
  l

irreducible let max_ctr: n:nat{n = 18446744073709551615} =
  assert_norm (pow2 64 - 1 = 18446744073709551615);
  pow2 64 - 1

type counter = c:nat{c <= max_ctr}

let ideal_ctr (#l:erid) (r: erid) (i:id) (log:ideal_log l i) : Tot Type0 =
  FStar.Monotonic.Seq.seqn r log max_ctr
  // An increasing counter, at most min(length log, 2^64-1)

let concrete_ctr (r:erid) (i:id) : Tot Type0 =
  m_rref r counter increases

let ctr_ref (#l:erid) (r:erid) (i:id) (log:log_ref l i) : Tot Type0 =
  if authId i
  then ideal_ctr r i (log <: ideal_log l i)
  else m_rref r counter increases

let ctr (#l:erid) (#r:erid) (#i:id) (#log:log_ref l i) (c:ctr_ref r i log)
  : Tot (m_rref r (if authId i
		   then seqn_val #l #(entry i) r log max_ctr
		   else counter)
		increases) =
  c

// kept concrete for log and counter, but the key and iv should be private.
noeq type state (i:id) (rw:rw) =
  | State: #region: rgn
         -> #log_region: rgn{if rw = Writer then region = log_region else HS.disjoint region log_region}
         -> aead: AEAD.state i rw
         -> log: log_ref log_region i // ghost, subject to cryptographic assumption
         -> counter: ctr_ref region i log // types are sufficient to anti-alias log and counter
         -> state i rw

// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

type writer i = s:state i Writer
type reader i = s:state i Reader


// We generate first the writer, then the reader (possibly several of them)
let genPost (#i:id) parent h0 (w:writer i) h1 =
  modifies Set.empty h0 h1 /\
  HS.parent w.region = parent /\
  HS.fresh_region w.region h0 h1 /\
  color w.region = color parent /\
  extends (AEAD.region w.aead) parent /\
  HS.fresh_region (AEAD.region w.aead) h0 h1 /\
  color (AEAD.region w.aead) = color parent /\
  (authId i ==>
      (h1 `HS.contains` (ilog w.log) /\
       sel h1 (ilog w.log) == createEmpty)) /\
  h1 `HS.contains` (ctr w.counter) /\
  sel h1 (ctr w.counter) === 0
//16-04-30 how to share the whole ST ... instead of genPost?

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we might drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: parent:rgn -> i:id -> ST (writer i)
  (requires (fun h0 -> witnessed (region_contains_pred parent))) 
  (ensures (genPost parent))

#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let gen parent i =
  let writer_r = new_region parent in
  lemma_ID13 i;
  let aead = AEAD.gen i parent in
  let _ = cut (is_eternal_region writer_r) in
  if authId i then
    let log : ideal_log writer_r i = alloc_mref_seq writer_r Seq.createEmpty in
    let ectr: ideal_ctr #writer_r writer_r i log = new_seqn #(entry i) #writer_r #max_ctr writer_r 0 log in
    State #i #Writer #writer_r #writer_r aead log ectr
  else
    let ectr: concrete_ctr writer_r i = HST.ralloc writer_r 0 in
    State #i #Writer #writer_r #writer_r aead () ectr

#reset-options
val genReader: parent:rgn -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> 
    witnessed (region_contains_pred parent) /\ 
    disjoint parent w.region /\
    disjoint parent (AEAD.region w.aead))) //16-04-25  we may need w.region's parent instead
  (ensures  (fun h0 (r:reader i) h1 ->
         modifies Set.empty h0 h1 /\
         r.log_region = w.region /\
         HS.parent r.region = parent /\
	       color r.region = color parent /\
         HS.fresh_region r.region h0 h1 /\
         w.log == r.log /\
	 h1 `HS.contains` (ctr r.counter) /\
	 sel h1 (ctr r.counter) === 0))
// encryption (on concrete bytes), returns (cipher @| tag)
// Keeps seqn and nonce implicit; requires the counter not to overflow
// encryption of plaintexts; safe instances are idealized

#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let genReader parent #i w =
  let reader_r = new_region parent in
  let writer_r : rgn = w.region in
  assert(HS.disjoint writer_r reader_r);
  lemma_ID13 i;
  let raead = AEAD.genReader parent #i w.aead in
  if authId i then
    let log : ideal_log w.region i = w.log in
    let dctr: ideal_ctr reader_r i log = new_seqn reader_r 0 log in
    State #i #Reader #reader_r #writer_r raead w.log dctr
  else let dctr : concrete_ctr reader_r i = HST.ralloc reader_r 0 in
    State #i #Reader #reader_r #writer_r raead () dctr

// Coerce a writer with index i in a fresh subregion of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rgn -> i:id{~(authId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

let coerce parent i kv iv =
  assume false; // coerce missing post-condition
  let writer_r = new_region parent in
  let ectr: concrete_ctr writer_r i = HST.ralloc writer_r 0 in
  let aead = AEAD.coerce i parent kv iv in
  State #i #Writer #writer_r #writer_r aead () ectr

val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (key i * iv i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))

let leak #i #role s =
  lemma_ID13 i;
  AEAD.leak #i #role (State?.aead s)

val encrypt: #i:id -> e:writer i -> ad:bytes -> l:plainLen -> p:plain i l -> ST (cipher i l)
    (requires (fun h0 ->
      lemma_ID13 i;
      HS.disjoint e.region (AEAD.log_region #i e.aead) /\
      l <= max_TLSPlaintext_fragment_length /\
      sel h0 (ctr e.counter) < max_ctr))
    (ensures  (fun h0 c h1 ->
      lemma_ID13 i;
      modifies (Set.as_set [e.log_region; AEAD.log_region #i e.aead]) h0 h1 /\
      h1 `HS.contains` (ctr e.counter) /\
      sel h1 (ctr e.counter) === sel h0 (ctr e.counter) + 1 /\
	    (authId i ==>
		    (let log = ilog e.log in
		    let ent = Entry l c p in
		    let n = Seq.length (sel h0 log) in
		    h1 `HS.contains` log /\
		    witnessed (at_least n ent log) /\
		    sel h1 log == snoc (sel h0 log) ent))))

(* we primarily model the ideal functionality, the concrete code that actually
   runs on the network is what remains after dead code elimination when
   safeId i is fixed to false and after removal of the cryptographic ghost log,
   i.e. all idealization is turned off *)
#set-options "--z3rlimit 150 --max_ifuel 2 --initial_ifuel 0 --max_fuel 2 --initial_fuel 0 --admit_smt_queries true"
let encrypt #i e ad l p =
  let h0 = get() in
  let ctr = ctr e.counter in
  HST.recall ctr;
  let text = if safeId i then create_ l 0z else repr i l p in
  let n = HST.op_Bang ctr in
  lemma_repr_bytes_values n;
  let nb = bytes_of_int (AEAD.noncelen i) n in
  let iv = AEAD.create_nonce e.aead nb in
  lemma_repr_bytes_values (length text);
  assume(AEAD.st_inv e.aead h0); // TODO
  assume(authId i ==> (Flag.prf i /\ AEAD.fresh_iv #i e.aead iv h0)); // TODO
  let c = AEAD.encrypt #i #l e.aead iv ad text in
  if authId i then
    begin
    let ilog = ilog e.log in
    HST.recall ilog;
    let ictr: ideal_ctr e.region i ilog = e.counter in
    testify_seqn ictr;
    write_at_end ilog (Entry l c p); //need to extend the log first, before incrementing the counter for monotonicity; do this only if ideal
    HST.recall ictr;
    increment_seqn ictr;
    HST.recall ictr
    end
  else
    ctr := n + 1;
  c

(* val matches: #i:id -> l:plainLen -> cipher i l -> entry i -> Tot bool *)
let matches (#i:id) (l:plainLen) (c:cipher i l) (e:entry i) : Tot bool =
  let Entry l' c' _ = e in
  l = l' && c = c'

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
val decrypt: #i:id -> d:reader i -> ad:bytes -> l:plainLen -> c:cipher i l
  -> ST (option (plain i (min l (max_TLSPlaintext_fragment_length + 1))))
  (requires (fun h0 ->
     l <= max_TLSPlaintext_fragment_length /\ // FIXME ADL: why is plainLen <= max_TLSCiphertext_fragment_length_13 ?? Fix StreamPlain!
     sel h0 (ctr d.counter) < max_ctr))
  (ensures  (fun h0 res h1 ->
      let j : nat = sel h0 (ctr d.counter) in
      (authId i ==>
    	(let log = sel h0 (ilog d.log) in
    	 if j < Seq.length log && matches l c (Seq.index log j)
    	 then res = Some (Entry?.p (Seq.index log j))
    	 else res = None)) /\
      (match res with
       | None -> HS.modifies_transitively Set.empty h0 h1
       | _ -> let ctr_counter_as_hsref = ctr d.counter in
             HS.modifies_one d.region h0 h1 /\
             HS.modifies_ref d.region (Set.singleton (Heap.addr_of (as_ref ctr_counter_as_hsref))) h0 h1 /\
             sel h1 (ctr d.counter) === j + 1)))

val strip_refinement: #a:Type -> #p:(a -> Type0) -> o:option (x:a{p x}) -> option a
let strip_refinement #a #p = function
  | None -> None
  | Some x -> Some x

#set-options "--z3rlimit 100 --initial_fuel 0 --initial_ifuel 1 --max_fuel 0 --max_ifuel 1"
// decryption, idealized as a lookup of (c,ad) in the log for safe instances
let decrypt #i d ad l c =
  let ctr = ctr d.counter in
  HST.recall ctr;
  let j = HST.op_Bang ctr in
  if authId i
  then (
    let ilog = ilog d.log in
    let log  = HST.op_Bang ilog in
    let ictr: ideal_ctr d.region i ilog = d.counter in
    testify_seqn ictr; //now we know that j <= Seq.length log
    if j < Seq.length log && matches l c (Seq.index log j) then
      begin
      increment_seqn ictr;
      HST.recall ctr;
      Some (Entry?.p (Seq.index log j))
      end
    else None )
  else //concrete
   begin
   lemma_ID13 i;
   assert (AEAD.noncelen i = AEAD.iv_length i);
   lemma_repr_bytes_values j;
   let nb = bytes_of_int (AEAD.noncelen i) j in
   let iv = AEAD.create_nonce d.aead nb in
   match AEAD.decrypt #i #l d.aead iv ad c with
   | None -> None
   | Some pr ->
     begin
       assert (FStar.Bytes.length pr == l);
       let p = strip_refinement (mk_plain i l pr) in
       if Some? p then ctr := (j + 1);
       p
     end
   end

(* TODO

- Check that decrypt indeed must use authId and not safeId (like in the F7 code)
- Injective allocation table from i to refs

*)
*)

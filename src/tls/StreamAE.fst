module StreamAE

// Provides authenticated encryption for a stream of variable-length
// plaintexts; concretely, we use AES_GCM but any other AEAD algorithm
// would do.

// This implementations *assumes* "Stateful AE" security, then calls CoreCrypto
// Alternatively, we should go down to AEAD with noAD. 

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Monotonic.RRef
open FStar.Monotonic.Seq

open Platform.Error
open Platform.Bytes

open TLSError
open TLSConstants
open TLSInfo
open StreamPlain

let gen parent i = 
  let kv = CoreCrypto.random (CoreCrypto.aeadKeySize (alg i)) in
  let iv = CoreCrypto.random (iv_length i) in
  let writer_r = new_region parent in
  if authId i then 
    begin 
      let log : ideal_log writer_r i = alloc_mref_seq writer_r Seq.createEmpty in
      let h = ST.get() in
      assert(0 <= max_seqn); 
      assert(0 <= Seq.length (m_sel #writer_r #(s:seq (entry i){True}) h log));
      let ectr: ideal_seqn writer_r i log = new_seqn writer_r 0 max_seqn log in

      //16-09-13 can we avoid the coercion below?
      let log : maybe_log writer_r i = to_maybe_log log in 
      let w = State #i #Writer #writer_r #writer_r kv iv log ectr in

      //16-09-13 these are now needed to prove the (authID ==> ...) postcondition
      let h1 = ST.get() in 
      assert(m_contains #writer_r #(s:seq (entry i){True}) (ilog w.log) h1);
      assert(m_sel h1 (ilog w.log) == createEmpty);
      w
    end
  else 
    let ectr: concrete_seqn writer_r i = m_alloc writer_r 0 in
    State #i #Writer #writer_r #writer_r kv iv () ectr 


let genReader parent #i w =
  let reader_r = new_region parent in
  if authId i
  then
    let log : ideal_log w.region i = w.log in
    let h = ST.get() in
    assert(0 <= max_seqn); 
    assert(0 <= Seq.length (m_sel #w.region #(s:seq (entry i){True}) h log));
    let dctr: ideal_seqn reader_r i log = new_seqn reader_r 0 max_seqn log in
    State #i #Reader #reader_r #(w.region) w.key w.iv w.log dctr
  else let dctr : concrete_seqn reader_r i = m_alloc reader_r 0 in
    State #i #Reader #reader_r #(w.region) w.key w.iv () dctr

let coerce parent i kv iv =
  let writer_r = new_region parent in
  let ectr: concrete_seqn writer_r i = m_alloc writer_r 0 in
  State #i #Writer #writer_r #writer_r kv iv () ectr 

let leak #i #role s = State.key s, State.iv s


// The per-record nonce for the AEAD construction is formed as follows:
//
// 1. The 64-bit record sequence number is padded to the left with zeroes to iv_length.
//
// 2. The padded sequence number is XORed with the static client_write_iv or server_write_iv,
//    depending on the role.
//
// The XORing is a fixed, ad hoc, random permutation; not sure what is gained;
// we can reason about sequence-number collisions before applying it.
let aeIV i (seqn:seqnum) (staticIV:iv i) : lbytes (iv_length i) =
  lemma_repr_bytes_values seqn;
  max_seqn_value ();
  let extended = bytes_of_int (iv_length i) seqn in
  xor (iv_length i) extended staticIV

// we are not relying on additional data
let noAD = empty_bytes

(* we primarily model the ideal functionality, the concrete code that actually
   runs on the network is what remains after dead code elimination when
   safeId i is fixed to false and after removal of the cryptographic ghost log,
   i.e. all idealization is turned off *)
let encrypt #i e l p =
  let ctr = ctr e.seqn in 
  m_recall ctr;
  assume(safeId i <==> authId i); //TODO elsewhere
  let text = if safeId i then createBytes l 0z else repr i l p in
  let n = m_read ctr in
  let iv = aeIV i n e.iv in
  let c = CoreCrypto.aead_encrypt (alg i) e.key iv noAD text in
  if authId i then
    begin
    let ilog = ilog e.log in
    m_recall ilog;
    let ictr: ideal_seqn e.region i ilog = e.seqn in
    testify_seqn ictr; //now we know that j <= Seq.length log
    let h = ST.get() in 
    m_recall ilog;
    m_recall ictr;
    assert(m_sel h ictr <= Seq.length (m_sel h ilog)); 
    write_at_end ilog (Entry l c p); //need to extend the log first, before incrementing the seqn for monotonicity; do this only if ideal
    let h = ST.get() in
    assert (m_sel h ictr < Seq.length (m_sel h ilog)); 
    m_recall ictr;
    increment_seqn (fun _ -> True) ictr;
    m_recall ictr
    end
  else
    m_write ctr (n + 1);
  c

#set-options "--z3timeout 10000"
// decryption, idealized as a lookup at index d.seq# in the log for safe instances
let decrypt #i d l c =
  let ctr = ctr d.seqn in 
  m_recall ctr;
  let j = m_read ctr in
  if authId i 
  then 
    let ilog = ilog d.log in
    let log  = m_read ilog in
    let ictr: ideal_seqn d.region i ilog = d.seqn in
    let _ = testify_seqn ictr in //now we know that j <= Seq.length log
    if j < Seq.length log && matches l c (Seq.index log j) then
      begin
      increment_seqn (fun _ -> True) ictr;
      m_recall ctr;
      Some (Entry.p (Seq.index log j))
      end
    else None
  else //concrete
     let iv = aeIV i j d.iv in
     let o = CoreCrypto.aead_decrypt (alg i) d.key iv noAD c in 
     match o with
     | None -> None
     | Some pr ->
       begin
         let a = alg i in 
         //16-09-13  can't prove a precondition below, why?
         assert(c = CoreCrypto.aead_encryptT a d.key iv noAD pr);
         assert(length c = length pr + CoreCrypto.aeadTagSize a);
         match mk_plain i l pr with
         | Some p -> (m_write ctr (j + 1); Some p)
         | None   -> None
       end


(* TODO

- Check that decrypt indeed must use authId and not safeId (like in the F7 code)
- Injective allocation table from i to refs

*)

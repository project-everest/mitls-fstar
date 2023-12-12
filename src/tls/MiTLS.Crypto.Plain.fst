module MiTLS.Crypto.Plain
open MiTLS

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt32
open FStar.Ghost
open MiTLS.Buffer.Utils
open MiTLS.Crypto.Symmetric.Bytes

// Abstraction for secret plaintexts (heap- and stack-based)

// For now we assume public lengths and no padding
// For TLS, we will pass around instead 
// - a public maximal length
// - a private actual length
// - a buffer of maximal length (possibly + 1 for TLS CT)
// The need to pass two lengths is a small price to pay for length hiding. 
// It is yet unclear whether to use buffers or bytes values. 

// Type abstraction protects against aliasing inasmuch
// as it is enforced from allocation.

open MiTLS.Crypto.Indexing
open MiTLS.Flag 

// -----------------------------------------------------------------------------

let plain (i:id) (l:plainLen) = lbytes l

// ghost
let as_bytes #i #l p = p

// restricted
let repr #i #l p = p

let make #i l b = b


(*
val reveal: #i:id -> #l:plainLen -> p:plain i l -> GTot (lbytes l)
let reveal #i #l p = p

val repr_injective : i:id -> l:plainLen -> p:plain i l -> Lemma
  (requires True)
  (ensures (make #i l (as_bytes p) == p))
  [SMTPat (as_bytes p)]
let repr_injective i l p = ()
*)

let slice #i #l p s j = Seq.slice p s j


let plainBuffer (i:id) (l:plainLen) = b:lbuffer l

//usage?

// ghost (was named bufferT; no need to be live)
let as_buffer #i #l pb = pb

// for tests
let unsafe_hide_buffer i #l b = b

// usage?
let hide_buffer i #l b = b

let as_buffer_injective i l p = ()


let sel_plain h #i l buf = sel_bytes h l buf

let bufferRepr #i #l b = b


let create (i:id) (zero:UInt8.t) (len:UInt32.t) :
   StackInline (plainBuffer i (v len))
     (requires (fun h -> is_stack_region (get_tip h)))
     (ensures (fun (h0:mem) p h1 ->
       let p' = p in
       let b = as_buffer p in
       let open FStar.Buffer in
       let live = live' in (* to undo shadowing by FStar.Buffer.live *)
         (b `unused_in` h0)
       /\ live h1 p' /\ idx b = 0 /\ length b = v len
       /\ frameOf b = get_tip h0
       /\ Map.domain (get_hmap h1) == Map.domain (get_hmap h0)
       /\ modifies_0 h0 h1
       /\ as_seq h1 b == Seq.create (v len) zero
       ))
 = Buffer.create zero len

let sub #id #l (b:plainBuffer id l)
               (i:UInt32.t{FStar.Buffer.(v i + idx (as_buffer b)) < pow2 n})
               (len:UInt32.t{FStar.Buffer.(v len <= length (as_buffer b) /\ v i + v len <= length (as_buffer b))}) : Tot (b':plainBuffer id (v len))
  = Buffer.sub b i len
// ...



let load #i l buf = load_bytes l buf

let store #i l buf b = store_bytes l buf b


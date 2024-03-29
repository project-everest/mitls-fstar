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

type plainLen = nat // we'll need a tigher bound

val plain (i:id) (l:plainLen) : Type0

// ghost
noextract val as_bytes: #i:id -> #l:plainLen -> p:plain i l -> GTot (lbytes l)

// restricted
val repr: #i:id {~(safeId i)} -> #l:plainLen -> p:plain i l -> Tot (b:lbytes l {b = as_bytes p })

val make: #i:id {~(safeId i)}-> l:plainLen -> b:lbytes l -> Tot (p:plain i l {b = as_bytes p})


(*
val reveal: #i:id -> #l:plainLen -> p:plain i l -> GTot (lbytes l)
let reveal #i #l p = p

val repr_injective : i:id -> l:plainLen -> p:plain i l -> Lemma
  (requires True)
  (ensures (make #i l (as_bytes p) == p))
  [SMTPat (as_bytes p)]
let repr_injective i l p = ()
*)

noextract val slice: #i:id -> #l:plainLen -> p:plain i l -> s:nat -> j:nat{s <= j && j <= l} -> 
  Tot (q:plain i (j - s) {as_bytes q = Seq.slice (as_bytes p) s j})


val plainBuffer (i:id) (l:plainLen) : Type0

//usage?

// ghost (was named bufferT; no need to be live)
val as_buffer: #i:id -> #l:plainLen -> pb: plainBuffer i l -> GTot(lbuffer l)

// for tests
val unsafe_hide_buffer: i:id -> #l:plainLen -> b:lbuffer l -> Tot (plainBuffer i l)

// usage?
val hide_buffer: i:id -> #l:plainLen -> b:lbuffer l -> GTot (plainBuffer i l)

val as_buffer_injective : i:id -> l:plainLen -> p:plainBuffer i l -> Lemma
  (requires True)
  (ensures (hide_buffer i (as_buffer p) == p))
  [SMTPat (as_buffer p)]


let live #i #l h (p:plainBuffer i l) = Buffer.live h (as_buffer p)
private let live' #i #l = live #i #l (* live may be shadowed by Buffer.live in case of local open *)

// unconditional access in specs; rename to as_plain? 
noextract val sel_plain: h:mem -> #i:id -> l:UInt32.t -> buf:plainBuffer i (v l) -> GTot (plain i (v l))

// restricted 
val bufferRepr: #i:id {~(safeId i)} -> #l:plainLen -> b:plainBuffer i l -> Tot (b':lbuffer l{ b' == as_buffer b})


val create (i:id) (zero:UInt8.t) (len:UInt32.t) :
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

val sub (#id:_) (#l:_) (b:plainBuffer id l)
               (i:UInt32.t{FStar.Buffer.(v i + idx (as_buffer b)) < pow2 n})
               (len:UInt32.t{FStar.Buffer.(v len <= length (as_buffer b) /\ v i + v len <= length (as_buffer b))}) : Tot (b':plainBuffer id (v len))
// ...



val load: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> ST (plain i (v l))
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 buf /\ sel_plain h1 l buf == r))


val store: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> b:plain i (v l) -> ST unit
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 buf /\ Buffer.modifies_1 (as_buffer #i #(v l) buf) h0 h1 /\
    sel_plain h1 l buf == b
  ))


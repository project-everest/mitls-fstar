module Random

open FStar.Bytes
open FStar.Error

open Mem
open TLSError

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("RNG| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_KS then print else (fun _ -> ())

(*
RNG is provided by EverCrypt and must be seeded before use
This is done by FF_mitls_init and automatically in Evercrypt
when possible
*)

let init () : St UInt32.t =
//  let h0 = get() in
//  assume(EverCrypt.Specs.random_init_pre h0);
  assume false;
  EverCrypt.AutoConfig.(init Default);
  EverCrypt.random_init ()

let cleanup () : St unit =
  assume false; // Precondition of random_cleanup in EverCrypt
  EverCrypt.random_cleanup ()

let sample32 (len:UInt32.t) : St (lbytes (UInt32.v len)) =
  assume false; // Precondition of random_sample in EverCrypt
  push_frame ();
  let b = LowStar.Buffer.alloca 0uy len in
  EverCrypt.random_sample len b;
  let r = BufferBytes.to_bytes (UInt32.v len) (LowStar.ToFStarBuffer.new_to_old_st b) in
  trace ("Sampled: "^(hex_of_bytes r));
  pop_frame ();
  r

let sample (len:nat{len < pow2 32}) : St (lbytes len) =
  sample32 (UInt32.uint_to_t len)

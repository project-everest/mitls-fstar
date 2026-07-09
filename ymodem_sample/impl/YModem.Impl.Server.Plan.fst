module YModem.Impl.Server.Plan

(**
  Pure block-plan arithmetic for the YMODEM *server* endpoint.

  A padded file `file : Seq.seq U8.t` of `nblocks * 128` bytes is cut into
  `nblocks` consecutive 128-byte data blocks.  `block file i` is the i-th block;
  `blocks_of file lo hi` is the list `[block file lo; …; block file (hi-1)]`.

  The endpoint's coupling invariant `server_plan_ok` says the ghost ARQ state's
  `yss_sent == blocks_of file 0 cursor` and `yss_pending == blocks_of file cursor
  nblocks`.  This module proves the list/seq facts the endpoint needs:

    * `blocks_of_unfold`  (cons at the low end): `hd`/`tl` of `blocks_of lo hi`;
    * `blocks_of_snoc`    (append at the high end): the send-shift step;
    * `blocks_of_plan_wf` : every block is 128 bytes, so `plan_wf (blocks_of …)`;
    * `block_slice`       : in range, `block file i` is the concrete slice.

  Everything is ordinary total F*; the Pulse endpoint calls these lemmas
  explicitly (never relying on SMT to instantiate their quantifiers).

  `block` is TOTAL: out of range it returns a 128-byte constant, so every block
  is exactly 128 bytes (making `plan_wf` unconditional), while `block_slice`
  recovers the concrete slice whenever the index is in range.
**)

module Seq = FStar.Seq
module L = FStar.List.Tot
module U8 = FStar.UInt8
module TCP = Common.TCP
module Math = FStar.Math.Lemmas

module YP = YModem.Protocol

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* The i-th 128-byte block of a padded file (total: clamped out of range). *)
let block (file:Seq.seq U8.t) (i:nat) : TCP.bytes =
  if (i + 1) * 128 <= Seq.length file
  then Seq.slice file (i * 128) ((i + 1) * 128)
  else Seq.create 128 0uy

(* Every block is exactly 128 bytes. *)
let block_len (file:Seq.seq U8.t) (i:nat)
  : Lemma (Seq.length (block file i) == 128)
          [SMTPat (Seq.length (block file i))]
  = ()

(* In range, the block is the concrete slice. *)
let block_slice (file:Seq.seq U8.t) (i nblocks:nat)
  : Lemma (requires i < nblocks /\ Seq.length file == nblocks * 128)
          (ensures block file i == Seq.slice file (i * 128) ((i + 1) * 128))
  = Math.lemma_mult_le_right 128 (i + 1) nblocks

(* The blocks with indices [lo, hi), consed at the low end. *)
let rec blocks_of (file:Seq.seq U8.t) (lo:nat) (hi:nat)
  : Tot (list TCP.bytes) (decreases (hi - lo)) =
  if lo >= hi then []
  else block file lo :: blocks_of file (lo + 1) hi

(* Empty range. *)
let blocks_of_empty (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (requires hi <= lo) (ensures blocks_of file lo hi == [])
  = ()

(* L1 — cons-unfold at the low end: exposes head and tail. *)
let blocks_of_unfold (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (requires lo < hi)
          (ensures
            blocks_of file lo hi == block file lo :: blocks_of file (lo + 1) hi /\
            Cons? (blocks_of file lo hi) /\
            L.hd (blocks_of file lo hi) == block file lo /\
            L.tl (blocks_of file lo hi) == blocks_of file (lo + 1) hi)
  = ()

(* L2 — snoc at the high end (the send-shift step), by induction on hi - lo. *)
let rec blocks_of_snoc (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (requires lo <= hi)
          (ensures
            blocks_of file lo (hi + 1) ==
            L.append (blocks_of file lo hi) [block file hi])
          (decreases (hi - lo))
  = if lo = hi then begin
      blocks_of_unfold file lo (hi + 1);
      blocks_of_empty file (lo + 1) (hi + 1);
      blocks_of_empty file lo hi
    end
    else begin
      blocks_of_unfold file lo (hi + 1);
      blocks_of_unfold file lo hi;
      blocks_of_snoc file (lo + 1) hi
    end

(* L3 — every block is 128 bytes, so the plan is well-formed. *)
let rec blocks_of_plan_wf (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (ensures YP.plan_wf (blocks_of file lo hi))
          (decreases (hi - lo))
  = if lo >= hi then ()
    else blocks_of_plan_wf file (lo + 1) hi

(* L4 — the list length is exactly the size of the index range.  The endpoint
   uses this to turn the coupling `sent == blocks_of file 0 cursor` into the
   concrete fact `L.length sent == cursor`, so cursor-level scheduling guards
   (`cursor < nblocks`) become state-level facts (`L.length sent < nblocks`). *)
let rec blocks_of_length (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (ensures L.length (blocks_of file lo hi) == (if lo >= hi then 0 else hi - lo))
          (decreases (hi - lo))
  = if lo >= hi then () else blocks_of_length file (lo + 1) hi

(* ── the combined facts the endpoint discharges at each scheduling point ───── *)

(* Send-shift: moving the head of `pending` onto the tail of `sent` shifts the
   cursor by one while preserving the `blocks_of` split.  Used by
   `finish_local_action` (Server_send) to re-establish the coupling at cursor+1. *)
let lemma_send_shift (file:Seq.seq U8.t) (c nblocks:nat)
  : Lemma (requires c < nblocks)
          (ensures
            Cons? (blocks_of file c nblocks) /\
            L.hd (blocks_of file c nblocks) == block file c /\
            L.tl (blocks_of file c nblocks) == blocks_of file (c + 1) nblocks /\
            L.append (blocks_of file 0 c) [block file c] == blocks_of file 0 (c + 1))
  = blocks_of_unfold file c nblocks;
    blocks_of_snoc file 0 c

(* The whole plan is exactly `blocks_of file 0 nblocks`. *)
let plan_of_file (file:Seq.seq U8.t) (nblocks:nat) : list TCP.bytes =
  blocks_of file 0 nblocks

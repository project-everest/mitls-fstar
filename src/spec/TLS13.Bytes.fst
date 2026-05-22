module TLS13.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8

type byte = U8.t
type bytes = Seq.seq byte

let length (b:bytes) : nat = Seq.length b

let zero : byte = U8.uint_to_t 0

let empty : bytes = Seq.create 0 zero

let of_list (l:list byte) : bytes = Seq.seq_of_list l

let append (a:bytes) (b:bytes) : bytes = Seq.append a b

let zeros (n:nat) : bytes = Seq.create n zero

let singleton (b:byte) : bytes = Seq.create 1 b

let take (n:nat) (b:bytes{n <= length b}) : bytes = Seq.slice b 0 n

let drop (n:nat) (b:bytes{n <= length b}) : bytes = Seq.slice b n (length b)

let bytes_of_len (n:nat) = b:bytes{length b == n}

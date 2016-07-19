module FFI

// A thin layer on top of TLS, adapting a bit our main API:
// - for TCP send & receive, we use callbacks provided by the application
// - for output traffic, we send fragment and send the whole message at once
// - for client connects, we block until the connection is sucessfully established
//
// We rely on higher-order; to be reconsidered once we compile to C/C++.

// TODO: guarantee (by typing) that we don't do stdio, and don't throw
//       exceptions, notably for incomplete pattern matching

// TODO: add server-side 

open Platform.Bytes

open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS

private let fragment_1 i (b:bytes { length b <= max_TLSPlaintext_fragment_length }) : fragment i (point (length b)) = 
  let rg : frange i = point(length b) in 
  appFragment i rg b 

// move to Bytes
private let sub (buffer:bytes) (first:nat) (len:nat { first + len <= length buffer }) = 
  let before, now = split buffer first in 
  let now, after = split buffer len in 
  now 

private val write_all': c:Connection.connection -> i:id -> buffer:bytes -> sent:nat {sent <= length buffer} -> St ioresult_w 
let rec write_all' c i buffer sent =  
  if sent = length buffer then Written 
  else 
  let size = min (length buffer - sent) max_TLSPlaintext_fragment_length in
  let payload = sub buffer sent size in
  let rg : frange i = point(length payload) in
  let f : fragment i rg = fragment_1 i payload in
  match assume false; write c f with
  | Written -> write_all' c i buffer (sent+size)
  | r       -> r 

private let write_all c i b = write_all' c i b 0

// an integer carrying the fatal alert descriptor
// we could also write txt into the application error log 
private let errno description txt = 
  match description with 
  | Some ad -> Char.int_of_char (snd (cbyte2 (Alert.alertBytes ad)))
  | None    -> -1 

 
let connect send recv config_1 : int = 
  // we assume the configuration specifies the target SNI; 
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in 
  let c = TLS.connect here tcp config_1 in 
  let i_0 = currentId c Reader in 
  match read c i_0 with 
  | Complete -> 0
  | ReadError description txt -> errno description txt

type read_result = // is it convenient?
  | Received of bytes 
  | Errno of int

let read c = 
  let i = currentId c Reader in 
  match read c i with
  | Read (Data d)             -> Received (appBytes d)
  | Read Close                -> Errno 0 
  | ReadError description txt -> Errno(errno description txt) 
  | _                         -> failwith "unexpected FFI read result"

let write c msg : int =
  let i = currentId c Writer in 
  match write_all c i msg with
  | Written                    -> 0 
  | WriteError description txt -> errno description txt
  | _                          -> -1 

// sending "CLOSE_NOTIFY"; should be followed by a read to wait for
// the full shutdown (but many servers don't acknowledge).

let close c = writeCloseNotify c


module Simple.Internal

open FStar.UInt32

// A module with nested pattern matching similar to TLS13.Handshake/Record
type message_type =
  | TypeA
  | TypeB  
  | TypeC

type result =
  | Success
  | Failure

// Function with nested pattern matching
let process_message (msg_type: message_type) (value: t) : result =
  match msg_type with
  | TypeA ->
      if value >^ 10ul then
        Success
      else
        Failure
  | TypeB ->
      if value >^ 20ul then
        if value <^ 100ul then
          Success
        else
          Failure
      else
        Failure
  | TypeC ->
      if value =^ 42ul then
        Success
      else
        Failure

// Simpler function with pattern matching
let get_threshold (msg: message_type) : t =
  match msg with
  | TypeA -> 10ul
  | TypeB -> 20ul
  | TypeC -> 42ul

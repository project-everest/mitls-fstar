module Common.TCP.History

module Seq = FStar.Seq
module U8 = FStar.UInt8

type bytes = Seq.seq U8.t

noeq
type history = {
  tcp_received: bytes;
  tcp_sent: bytes;
}

let empty_history : history =
  {
    tcp_received = Seq.empty;
    tcp_sent = Seq.empty;
  }

let append_received (h:history) (chunk:bytes) : history =
  { h with tcp_received = Seq.append h.tcp_received chunk }

let append_sent (h:history) (chunk:bytes) : history =
  { h with tcp_sent = Seq.append h.tcp_sent chunk }

let history_equal (h0 h1:history) : prop =
  Seq.equal h0.tcp_received h1.tcp_received /\
  Seq.equal h0.tcp_sent h1.tcp_sent

let bytes_extends (old:bytes) (next:bytes) : prop =
  Seq.length old <= Seq.length next /\
  Seq.equal old (Seq.slice next 0 (Seq.length old))

let history_extends (old next:history) : prop =
  bytes_extends old.tcp_received next.tcp_received /\
  bytes_extends old.tcp_sent next.tcp_sent

let bytes_exact_prefix (prefix full:bytes) : prop =
  Seq.length prefix <= Seq.length full /\
  Seq.equal prefix (Seq.slice full 0 (Seq.length prefix))

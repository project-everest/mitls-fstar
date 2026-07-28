module TLS13.Record.Spec

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Seq = FStar.Seq
module T = TLS13.Types

include TLS13.Messages

type epoch =
  | Initial
  | Handshake
  | Application

type direction_state = {
  epoch: epoch;
  key: option B.bytes;
  static_iv: option B.bytes;
  seq: nat;
}

let initial_direction_state : direction_state =
  { epoch = Initial; key = None; static_iv = None; seq = 0 }

let install_keys
  (st:direction_state)
  (epoch:epoch)
  (key:B.bytes)
  (iv:B.bytes)
  : direction_state =
  { epoch = epoch; key = Some key; static_iv = Some iv; seq = 0 }

let next_seq (st:direction_state) : direction_state =
  { st with seq = st.seq + 1 }

let seal
  (st:direction_state)
  (aad:B.bytes)
  (pt:plaintext)
  : GTot (option (sealed_record & direction_state)) =
  match st.key, st.static_iv with
  | Some key, Some iv ->
    let nonce = C.tls13_record_nonce iv st.seq in
    Some (C.chacha20_poly1305_seal key nonce aad pt.fragment, next_seq st)
  | _, _ -> None

let open_record
  (st:direction_state)
  (aad:B.bytes)
  (ct:sealed_record)
  : GTot (option (B.bytes & direction_state)) =
  match st.key, st.static_iv with
  | Some key, Some iv ->
    if B.length ct >= 16 then
      let nonce = C.tls13_record_nonce iv st.seq in
      (match C.chacha20_poly1305_open key nonce aad ct with
       | Some pt -> Some (pt, next_seq st)
       | None -> None)
    else None
  | _, _ -> None

let lemma_open_record_after_seal
  (st:direction_state)
  (aad:B.bytes)
  (pt:plaintext)
  : Lemma
      (requires Some? st.key /\ Some? st.static_iv)
      (ensures (
        match seal st aad pt with
        | Some (ct, st') -> open_record st aad ct == Some (pt.fragment, st')
        | None -> False))
=
  match st.key, st.static_iv with
  | Some key, Some iv ->
    let nonce = C.tls13_record_nonce iv st.seq in
    let ct = C.chacha20_poly1305_seal key nonce aad pt.fragment in
    C.lemma_chacha20_poly1305_open_seal key nonce aad pt.fragment;
    assert (B.length ct == B.length pt.fragment + 16);
    assert (B.length ct >= 16)
  | _, _ ->
    assert False

let lemma_open_record_after_seal_peer
  (write_st:direction_state)
  (read_st:direction_state)
  (aad:B.bytes)
  (pt:plaintext)
  : Lemma
      (requires
        write_st.seq == read_st.seq /\
        (match
          write_st.key,
          write_st.static_iv,
          read_st.key,
          read_st.static_iv
        with
        | Some write_key, Some write_iv, Some read_key, Some read_iv ->
          Seq.equal write_key read_key /\
          Seq.equal write_iv read_iv
        | _, _, _, _ ->
          False))
      (ensures (
        match seal write_st aad pt with
        | Some (ct, _) -> open_record read_st aad ct == Some (pt.fragment, next_seq read_st)
        | None -> False))
=
  match
    write_st.key,
    write_st.static_iv,
    read_st.key,
    read_st.static_iv
  with
  | Some write_key, Some write_iv, Some read_key, Some read_iv ->
    Seq.lemma_eq_elim write_key read_key;
    Seq.lemma_eq_elim write_iv read_iv;
    assert (C.tls13_record_nonce write_iv write_st.seq ==
            C.tls13_record_nonce read_iv read_st.seq);
    C.lemma_chacha20_poly1305_open_seal
      write_key
      (C.tls13_record_nonce write_iv write_st.seq)
      aad
      pt.fragment;
    let ct =
      C.chacha20_poly1305_seal
        write_key
        (C.tls13_record_nonce write_iv write_st.seq)
        aad
        pt.fragment in
    assert (B.length ct == B.length pt.fragment + 16);
    assert (B.length ct >= 16)
  | _, _, _, _ ->
    assert False

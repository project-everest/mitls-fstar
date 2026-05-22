module TLS13.Record.Spec

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module T = TLS13.Types

type epoch =
  | Initial
  | Handshake
  | Application

type direction_state = {
  epoch: epoch;
  key: option C.aead_key;
  static_iv: option C.aead_nonce;
  seq: nat;
}

type plaintext = {
  content_type: T.content_type;
  fragment: B.bytes;
}

type sealed_record = B.bytes

let initial_direction_state : direction_state =
  { epoch = Initial; key = None; static_iv = None; seq = 0 }

let install_keys
  (st:direction_state)
  (epoch:epoch)
  (key:C.aead_key)
  (iv:C.aead_nonce)
  : direction_state =
  { epoch = epoch; key = Some key; static_iv = Some iv; seq = 0 }

let next_seq (st:direction_state) : direction_state =
  { st with seq = st.seq + 1 }

let seal
  (st:direction_state)
  (aad:B.bytes)
  (pt:plaintext)
  : option (sealed_record & direction_state) =
  match st.key, st.static_iv with
  | Some key, Some iv ->
    let nonce = C.tls13_record_nonce iv st.seq in
    Some (C.chacha20_poly1305_seal key nonce aad pt.fragment, next_seq st)
  | _, _ -> None

let open_record
  (st:direction_state)
  (aad:B.bytes)
  (ct:sealed_record)
  : option (B.bytes & direction_state) =
  match st.key, st.static_iv with
  | Some key, Some iv ->
    if B.length ct >= 16 then
      let nonce = C.tls13_record_nonce iv st.seq in
      (match C.chacha20_poly1305_open key nonce aad ct with
       | Some pt -> Some (pt, next_seq st)
       | None -> None)
    else None
  | _, _ -> None

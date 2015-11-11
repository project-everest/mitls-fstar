module Predicates

open FStar.Seq
open FStar.List

type byte = n:nat{ n < 256 }

type log = seq byte
type byte_string = seq byte

type tern =
  | Yes
  | No
  | Undefined

type contentType =
  | ChangeCipherSpec 
  | Alert 
  | Handshake 
  | ApplicationData 
  | UndefinedContentType

val readContentType: byte -> Tot contentType
let readContentType ct =
  match ct with
  | 20 (* 0x14 *) -> ChangeCipherSpec
  | 21 (* 0x15 *) -> Alert 
  | 22 (* 0x16 *) -> Handshake
  | 23 (* 0x17 *) -> ApplicationData
  | _ -> UndefinedContentType

type messageType =
  | HelloRequest
  | ClientHello
  | ServerHello
  | Certificate
  | ServerKeyExchange
  | ServerCertificateRequest
  | ServerHelloDone
  | ClientKeyExchange
  | ClientCertificateVerify
  | Finished
  | ServerNewSessionTicket
  | UndefinedMessageType
  | ServerCertificate
  | ClientCertificate
  | ServerFinished
  | ClientFinished
  | ServerCCS
  | ClientCCS

val readMessageType: byte -> Tot messageType
let readMessageType mt =
  match mt with
  | 0 -> HelloRequest
  | 1 -> ClientHello
  | 2 -> ServerHello
  | 11 -> Certificate
  | 12 -> ServerKeyExchange
  | 13  -> ServerCertificateRequest
  | 14 -> ServerHelloDone
  | 16 -> ClientKeyExchange
  | 15 -> ClientCertificateVerify
  | 20 -> Finished
  | 4 -> ServerNewSessionTicket
  | _ -> UndefinedMessageType

type role =
  | Server
  | Client
  | UndefinedRole

type pv =
  | SSL3
  | TLS1
  | TLS1_1
  | TLS1_2
  | Tickets
  | ALPN
  | DTLS    
  | UndefinedPV

val readProtocolVersion: msg:byte_string -> len:nat{ len <= Seq.length msg } -> Tot pv
let readProtocolVersion msg len =
  if len < 6 then UndefinedPV
  else 
    match index msg 4, index msg 5 with
    | 3, 0 (* 0x03, 0x00 *) -> SSL3
    | 3, 1 (* 0x03, 0x01 *) -> TLS1
    | 3, 2 (* 0x03, 0x02 *) -> TLS1_1
    | 3, 3 (* 0x03, 0x03 *) -> TLS1_2
    | _ -> UndefinedPV 

type kem =
  | Anonymous
  | DiffieHellman
  | DHE
  | DHE_export
  | DH_anonymous
  | ECDH
  | ECDHE
  | ECDH_anonymous
  | RSA
  | RSA_export
  | PSK
  | UndefinedKEM


val readKem: msg:byte_string -> len:nat{len <= Seq.length msg } -> Tot kem
let readKem msg len =
  if len < 39 then UndefinedKEM
  else 
    let offset = 38 in
    let offset = offset + 1 + (Seq.index msg offset) in
    if len < offset + 2 then UndefinedKEM
    else 
      match Seq.index msg offset with
      | 0 (* 0x00 *) -> 
	 (match Seq.index msg (offset + 1) with
	 | 1   (* 0x01 *) 
	 | 2   (* 0x02 *) 
	 | 59  (* 0x3B *) 
	 | 4   (* 0x04 *) 
	 | 5   (* 0x05 *) 
	 | 6   (* 0x07 *) 
	 | 9   (* 0x09 *) 
	 | 10  (* 0x0A *) 
	 | 47  (* 0x2F *) 
	 | 53  (* 0x35 *) 
	 | 60  (* 0x3C *) 
	 | 61  (* 0x3D *) 
	 | 132 (* 0x84 *) 
	 | 150 (* 0x96 *) 
	 | 156 (* 0x9C *) 
	 | 157 (* 0x9D *) 
	 | 186 (* 0xBA *) 
	 | 192 (* 0xC0 *) ->
	    RSA
	 | 3   (* 0x03 *) 
	 | 6   (* 0x06 *) 
	 | 8   (* 0x08 *) ->
	    RSA_export
	 | 12  (* 0x0C *) 
	 | 13  (* 0x0D *) 
	 | 15  (* 0x0F *) 
	 | 16  (* 0x10 *) 
	 | 48  (* 0x30 *) 
	 | 49  (* 0x31 *)
	 | 54  (* 0x36 *) 
         | 55  (* 0x37 *)
	 | 62	 (* 0x3E *)
	 | 63	 (* 0x3F *)
	 | 66	 (* 0x42 *)
	 | 67	 (* 0x43 *)
	 | 104 (* 0x68 *)
	 | 105 (* 0x69 *)
	 | 133 (* 0x85 *)
	 | 134 (* 0x86 *)
	 | 151 (* 0x97 *)
	 | 152 (* 0x98 *)
	 | 160 (* 0xA0 *)
	 | 161 (* 0xA1 *)
	 | 164 (* 0xA4 *)
	 | 165 (* 0xA5 *)
	 | 187 (* 0xBB *)
	 | 188 (* 0xBC *)
	 | 193 (* 0xC1 *)
	 | 194 (* 0xC2 *) ->
	    DiffieHellman
         | 18  (* 0x12 *)
	 | 19	 (* 0x13 *)
	 | 21	 (* 0x15 *)
	 | 22	 (* 0x16 *)
	 | 50	 (* 0x32 *)
	 | 51	 (* 0x33 *)
	 | 56	 (* 0x38 *)
	 | 57	 (* 0x39 *)
	 | 64	 (* 0x40 *)
	 | 68	 (* 0x44 *)
	 | 69	 (* 0x45 *)
	 | 103 (* 0x67 *)
	 | 106 (* 0x6A *)
	 | 107 (* 0x6B *)
	 | 135 (* 0x87 *)
	 | 136 (* 0x88 *)
	 | 153 (* 0x99 *)
	 | 154 (* 0x9A *)
	 | 158 (* 0x9E *)
	 | 159 (* 0x9F *)
	 | 162 (* 0xA2 *)
	 | 163 (* 0xA3 *)
	 | 189 (* 0xBD *)
	 | 190 (* 0xBE *)
	 | 195 (* 0xC3 *)
	 | 196 (* 0xC4 *) ->
	    DHE
	 | 17  (* 0x11 *) 
	 | 20  (* 0x14 *) ->
	    DHE_export
         | 24  (* 0x18 *)
	 | 26	 (* 0x1A *)
	 | 27	 (* 0x1B *)
	 | 52	 (* 0x34 *)
	 | 58	 (* 0x3A *)
	 | 70	 (* 0x46 *)
	 | 108 (* 0x6C *)
	 | 109 (* 0x6D *)
	 | 137 (* 0x89 *)
	 | 155 (* 0x9B *)
	 | 166 (* 0xA6 *)
	 | 167 (* 0xA7 *)
	 | 191 (* 0xBF *)
	 | 197 (* 0xC5 *) ->
	    DH_anonymous
	 | _ -> 
	    UndefinedKEM)
      | 192 (* 0xC0 *) ->
	  (match index msg (offset+1) with
           | 60  (* 0x3C *)
	   | 61  (* 0x3D *)
	   | 80  (* 0x50 *)
	   | 81  (* 0x51 *)
	   | 122 (* 0x7A *)
	   | 123 (* 0x7B *)
	   | 156 (* 0x9C *)
	   | 157 (* 0x9D *)
	   | 160 (* 0xA0 *)
           | 161 (* 0xA1 *) ->
	      RSA
           | 62  (* 0x3E *)
	   | 63  (* 0x3F *)
	   | 64  (* 0x40 *)
	   | 65  (* 0x41 *)
	   | 84  (* 0x54 *)
	   | 85  (* 0x55 *)
	   | 88  (* 0x58 *)
	   | 89  (* 0x59 *)
           | 126 (* 0x7E *)
           | 127 (* 0x7F *)
           | 130 (* 0x82 *)
           | 131 (* 0x83 *) ->
	      DiffieHellman
	   | 70  (* 0x46 *) 
	   | 71  (* 0x47 *)  
	   | 90  (* 0x5A *) 
	   | 91  (* 0x5B *) 
	   | 132 (* 0x84 *) 
	   | 133 (* 0x85 *) ->
	      DH_anonymous
           | 66  (* 0x42 *)
	   | 67  (* 0x43 *)
	   | 68  (* 0x44 *)
	   | 69  (* 0x45 *)
	   | 82  (* 0x52 *)
	   | 83  (* 0x53 *)
	   | 86  (* 0x56 *)
	   | 87  (* 0x57 *)
           | 124 (* 0x7C *)
	   | 125 (* 0x7D *)
	   | 128 (* 0x80 *)
	   | 129 (* 0x81 *)
	   | 158 (* 0x9E *)
	   | 159 (* 0x9F *)
	   | 162 (* 0xA2 *)
	   | 163 (* 0xA3 *) ->
	      DHE
           | 1   (* 0x01 *)
	   | 2   (* 0x02 *)
	   | 3   (* 0x03 *)
	   | 4   (* 0x04 *)
	   | 5   (* 0x05 *)
	   | 11  (* 0x0B *)
	   | 12  (* 0x0C *)
	   | 13  (* 0x0D *)
	   | 14  (* 0x0E *)
	   | 15  (* 0x0F *)
	   | 37  (* 0x25 *)
	   | 38  (* 0x26 *)
	   | 41  (* 0x29 *)
	   | 42  (* 0x2A *)
	   | 45  (* 0x2D *)
	   | 46  (* 0x2E *)
	   | 49  (* 0x31 *)
	   | 50  (* 0x32 *)
	   | 74  (* 0x4A *)
	   | 75  (* 0x4B *)
	   | 78  (* 0x4E *)
	   | 79  (* 0x4F *)
	   | 94  (* 0x5E *)
	   | 95  (* 0x5F *)
	   | 98  (* 0x62 *)
	   | 99  (* 0x63 *)
	   | 116 (* 0x74 *)
	   | 117 (* 0x75 *)
	   | 120 (* 0x78 *)
	   | 121 (* 0x79 *)
	   | 136 (* 0x88 *)
	   | 137 (* 0x89 *)
	   | 140 (* 0x8C *)
	   | 141 (* 0x8D *) ->
	      ECDH
	   | 6   (* 0x06 *)
	   | 7   (* 0x07 *)
	   | 8   (* 0x08 *)
	   | 9   (* 0x09 *)
           | 10  (* 0x0A *)
	   | 16  (* 0x10 *)
	   | 17  (* 0x11 *)
	   | 18  (* 0x12 *)
	   | 19  (* 0x13 *)
	   | 20  (* 0x14 *)
	   | 35  (* 0x23 *)
	   | 36  (* 0x24 *)
	   | 39  (* 0x27 *)
	   | 40  (* 0x28 *)
	   | 43  (* 0x2B *)
	   | 44  (* 0x2C *)
	   | 47  (* 0x2F *)
	   | 48  (* 0x30 *)
	   | 72  (* 0x48 *)
	   | 73  (* 0x49 *)
	   | 76  (* 0x4C *)
	   | 77  (* 0x4D *)
	   | 92  (* 0x5C *)
	   | 93  (* 0x5D *)
	   | 96  (* 0x60 *)
	   | 97  (* 0x61 *)
           | 114 (* 0x72 *)
	   | 115 (* 0x73 *)
	   | 118 (* 0x76 *)
	   | 119 (* 0x77 *)
	   | 138 (* 0x8A *)
	   | 139 (* 0x8B *)
	   | 172 (* 0xAc *)
	   | 173 (* 0xAD *)
	   | 174 (* 0xAE *)
	   | 175 (* 0xAF *) ->
               ECDHE
           | 21 (* 0x15 *) 
	   | 22 (* 0x16 *) 
	   | 23 (* 0x17 *) 
	   | 24 (* 0x18 *) 
	   | 25 (* 0x19 *) ->
	       ECDH_anonymous
	 | _  ->
	      UndefinedKEM)
      | _ ->	
	 UndefinedKEM

type auth =
  | Auth_requested
  | No_auth
  | Auth_not_provided
  | Auth_provided
  | Auth_with_fixed_DH
  | UndefinedAuth

type state_mon =  { 
    (* Protocol version *)
    pv:pv;
    (* Role : client or server *)
    role:role;
    (* Negotiated key exchange method *)
    kem:kem;
    (* Type of the last message received *)
    last_message:messageType;
    (* Authentication required for the client and server *)
    client_auth:auth;
    (* Resumption flag *)
    resumption:tern;
    (* Renegotiation flag *)
    renegotiation:tern;
    (* New session ticket flag *)
    ntick:tern;
    (* List of messages received up to the current state *)
    msg_list:list byte_string;
    (* Concatenation of the messages received up to the current state *)
    log:log;
    log_length:nat;
  }

let yes = true
let no = false

let sent = true
let received = false

let accept = yes
let reject = no

(* Predicates on who sent the message *)

type sentByClient (s:state_mon) (direction:bool) = 
	 (s.role == Server /\ direction == received)
       \/ (s.role == Client /\ direction == sent )

type sentByServer (s:state_mon) (direction:bool) = 
	 (s.role == Client /\ direction == received)
       \/ (s.role == Server /\ direction == sent)

(* Predicates on the nature of the message *)

type isMessageLength (msg:byte_string) (len:nat{ len <= Seq.length msg }) =
	 (len >= 4) /\ (len - 4 = 65536 * (index msg 1) + 256 * (index msg 2) + (index msg 3))

type isClientHello (msg:byte_string) (len:nat{ len <= Seq.length msg }) (contentType:contentType) =
 	 (contentType = Handshake)
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = ClientHello) 

type isServerHello (msg:byte_string) (len:nat{ len <= Seq.length msg }) (contentType:contentType) =
	 (isMessageLength msg len)
	 /\ (contentType = Handshake)
	 /\ (readMessageType (index msg 0) = ServerHello)
	    
type isServerCertificate (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = Handshake) 
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = Certificate) 
	 /\ (sentByServer s direction)  

  type isServerKeyExchange (msg:byte_string) (len:nat{ len <= Seq.length msg }) (contentType:contentType) =
	 (contentType = Handshake)
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = ServerKeyExchange)

  type isServerCertificateRequest (msg:byte_string) (len:nat{ len <= Seq.length msg }) (contentType:contentType) =
	 (contentType = Handshake)
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = ServerCertificateRequest)

  type isServerHelloDone (msg:byte_string) (len:nat{ len <= Seq.length msg }) (contentType:contentType) =
	 (contentType = Handshake)
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = ServerHelloDone)

  type isClientCertificate (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = Handshake) 
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = Certificate) 
	 /\ (sentByClient s direction)  

  type isClientKeyExchange (msg:byte_string) (len:nat{ len <= Seq.length msg }) (contentType:contentType) =
	 (contentType = Handshake)
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = ClientKeyExchange)

  type isClientCertificateVerify (msg:byte_string) (len:nat{ len <= Seq.length msg }) (contentType:contentType) =
	 (contentType = Handshake)
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = ClientCertificateVerify)

  type isServerChangeCipherSpecs (s:state_mon) (msg:byte_string) (len:pos{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = ChangeCipherSpec) 
	 /\ (index msg 0 = 1 (* 0x01 *)) 
	 /\ (sentByServer s direction)  
	 /\ (len = 1)

  type isServerFin (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = Handshake) 
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = Finished) 
	 /\ (sentByServer s direction)  

  type isClientChangeCipherSpecs (s:state_mon) (msg:byte_string) (len:pos{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = ChangeCipherSpec) 
	 /\ (index msg 0 = 1 (* 0x01 *)) 
	 /\ (sentByClient s direction)  
	 /\ (len = 1)

  type isClientFin (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = Handshake) 
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = Finished) 
	 /\ (sentByClient s direction)  

  type isServerNewSessionTicket (msg:byte_string) (len:nat{ len <= Seq.length msg}) (contentType:contentType) =
    (contentType = Handshake)
    /\ (isMessageLength msg len)
    /\ (readMessageType (index msg 0) = ServerNewSessionTicket )

  type isUndefinedMessage (s:state_mon) (msg:byte_string) (len:pos{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
	 ~ (isClientHello msg len contentType) 
	 /\ ~ (isServerHello msg len contentType)
	 /\ ~ (isServerCertificate s msg len direction contentType)
	 /\ ~ (isServerKeyExchange msg len contentType)
	 /\ ~ (isServerCertificateRequest msg len contentType ) 
	 /\ ~ (isServerHelloDone msg len contentType )
	 /\ ~ (isClientCertificate s msg len direction contentType)
	 /\ ~ (isClientKeyExchange msg len contentType)
	 /\ ~ (isClientCertificateVerify msg len contentType)
	 /\ ~ (isServerChangeCipherSpecs s msg len direction contentType)
	 /\ ~ (isServerFin s msg len direction contentType) 
	 /\ ~ (isClientChangeCipherSpecs s msg len direction contentType)
	 /\ ~ (isClientFin s msg len direction contentType)

  type isEmptyClientCertificate (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) (direction:bool) =
	 isClientCertificate s msg len direction Handshake /\ len = 4 (* 0x04 *)

  type isNonEmptyClientCertificate (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) (direction:bool) =
	 isClientCertificate s msg len direction Handshake /\ len > 4

(* Predicates on the protocol versions *)
  type isSSL3 (msg:byte_string) (len:nat{ len <= Seq.length msg })
  type isTLS1 (msg:byte_string) (len:nat{ len <= Seq.length msg })
  type isTLS1_1 (msg:byte_string) (len:nat{ len <= Seq.length msg })
  type isTLS1_2 (msg:byte_string) (len:nat{ len <= Seq.length msg })

  type isUndefinedPV (msg:byte_string) (len:nat{ len <= Seq.length msg}) =
	 ~ (isSSL3 msg len )
	 /\ ~ (isTLS1 msg len)
	 /\ ~ (isTLS1_1 msg len)
	 /\ ~ (isTLS1_2 msg len)

(* Predicates on the key exchange methods *)
   type isDH (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isDHE (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isDHEExport (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isDHanon (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isECDH (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isECDHE (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isECDHanon (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isRSA (msg:byte_string) (len:nat{ len <= Seq.length msg }) 
   type isRSAExport (msg:byte_string) (len:nat{ len <= Seq.length msg }) 

  type isUndefinedKEM (msg:byte_string) (len:nat{ len <= Seq.length msg}) =
	 ~ (isDH msg len)
	 /\ ~ (isDHE msg len)
	 /\ ~ (isDHEExport msg len)
	 /\ ~ (isDHanon msg len)
	 /\ ~ (isECDH msg len)
	 /\ ~ (isECDHanon msg len)
	 /\ ~ (isRSA msg len)
	 /\ ~ (isRSAExport msg len)

(* Lemmas relating the construction of the log and the construction of the log *) 
val build_log:
  msg_list:list byte_string ->
  Tot byte_string
let rec build_log msg_list =
  match msg_list with
  | [] -> Seq.create 0 0
  | msg::tail ->
     Seq.append (build_log tail) msg

val get_length:
  log:byte_string{ Seq.length log >= 4 } ->
  Tot nat
let get_length log =
  65536 * (index log 1) + 256 * (index log 2) + (index log 3) + 4

val get_first:
  #a:Type -> l:list a{ List.length l > 0 }  -> Tot a
let get_first l =
  match l with
  | hd::_ -> hd

val get_tail:
  #a:Type -> l:list a{ List.length l > 0 } -> Tot (list a)
let get_tail l =
  match l with
  | _::tl -> tl

val parse:
  log:byte_string ->
  Tot (option (list byte_string))
      (decreases (Seq.length log))
let rec parse log =
  let log_length = Seq.length log in
  if log_length = 0 then Some []
  else if log_length < 4 then None
  else 
    let len = get_length log in
    if log_length < len then None
    else
      let msg = Seq.slice log 0 len in
      let log' = Seq.slice log len log_length in
      let tmp = parse log' in
      match tmp with
      | None -> None
      | Some v -> Some (List.append v [msg])

val intermediate_lemma_2:
  msg:byte_string{ isMessageLength msg (Seq.length msg) } ->
  Lemma
    (requires (True))
    (ensures ((is_Some (parse msg))
	      /\ (Some.v (parse msg) = [msg])))
let intermediate_lemma_2 msg = 
  let log_length = Seq.length msg in
  cut (log_length >= 4 /\ True);
  let len = get_length msg in
  cut (len = log_length /\ True);
  let msg' = Seq.slice msg 0 len in
  cut ( Seq.Eq msg msg' /\ True );
  let log' = Seq.slice msg len log_length in
  cut ( Seq.length log' = 0 /\ True );
  cut ( is_Some (parse log') /\ parse log' = Some [] );
  cut ( parse msg = Some [msg] /\ True );
  ()

#reset-options

val intermediate_lemma_3:
  log:byte_string{ is_Some (parse log) } ->
  msg:byte_string{ isMessageLength msg (Seq.length msg) } ->
  Lemma
    (requires (True))
    (ensures (is_Some (parse (Seq.append msg log))
	      /\ (Some.v (parse (Seq.append msg log)) = List.append (Some.v (parse log)) [msg])))
let intermediate_lemma_3 log msg =
  let big_log = Seq.append msg log in
  let log_length = Seq.length big_log in
  cut ( log_length >= 4 /\ True );
  let len = get_length big_log in
  let msg' = Seq.slice big_log 0 len in
  let log' = Seq.slice big_log len log_length in
  cut (Seq.Eq msg msg' /\ True);
  cut (Seq.Eq log log' /\ True);
  cut (parse big_log = Some (List.append (Some.v (parse log)) [msg]) /\ True );
  ()

#reset-options

val intermediate_lemma_1:
  log:byte_string{ is_Some (parse log) } ->
  msg:byte_string{ isMessageLength msg (Seq.length msg) } ->
  Lemma
    (requires (True))
    (ensures (is_Some (parse (Seq.append log msg))
	      /\ (Some.v (parse (Seq.append log msg)) = msg::(Some.v (parse log)))))
    (decreases (Seq.length log))
let rec intermediate_lemma_1 log msg =
  let log_length = Seq.length log in
  if log_length = 0 then 
    begin
      cut ( Seq.Eq (Seq.append log msg) msg /\ True);
      cut ( msg::(Some.v (parse log)) = [msg] /\ True);
      intermediate_lemma_2 msg;
      cut ( parse msg = Some [msg] /\ True );
      ()
end
  else
    let len = get_length log in
    let msg' = Seq.slice log 0 len in
    let log' = Seq.slice log len log_length in
    intermediate_lemma_1 log' msg;
    cut (Some.v (parse (Seq.append log' msg)) = msg::(Some.v (parse log')) /\ True );
    cut ( List.append (msg::(Some.v (parse log'))) [msg'] = msg::(List.append (Some.v (parse log')) [msg']) /\ True );
    cut ( parse log = Some (List.append (Some.v (parse log')) [msg']) /\ True );
    cut ( Seq.Eq (Seq.append log msg) (Seq.append msg' (Seq.append log' msg)) /\ True);
    intermediate_lemma_3 (Seq.append log' msg) msg';
    cut ( parse (Seq.append msg' (Seq.append log' msg)) = Some (List.append (Some.v (parse (Seq.append log' msg))) [msg']) /\ True );
    ()

#reset-options


(* Is the log and the message list only contain well formatted messaged then build_log is the reciprocal of parse *)
val bijectivity_lemma:
  msg_list:list byte_string{ 
	     (forall (msg:byte_string).
	      mem msg msg_list ==> isMessageLength msg (Seq.length msg))
	   } ->
  Lemma
    (requires (True))
    (ensures (is_Some (parse (build_log msg_list))
	      /\ (Some.v (parse (build_log msg_list)) = msg_list) ))
let rec bijectivity_lemma msg_list =
  match msg_list with
  | [] -> 
     cut ( parse (build_log msg_list) = Some [] /\ True );
     ()
  | msg::tail ->
     bijectivity_lemma tail;
     cut (is_Some (parse (build_log tail)) /\ True);
     cut ( Seq.Eq (build_log msg_list) (Seq.append (build_log tail) msg) /\ True);
     intermediate_lemma_1 (build_log tail) msg;
     ()


(* Log related predicates *)
type MessageAddedToLog (new_state:state_mon) (old_state:state_mon) (msg:byte_string) (len:nat{ len = Seq.length msg}) =
         (* Maintaining the message list variable *)
	 (new_state.msg_list = msg::(old_state.msg_list))
	 (* Maintaining the real log *)
	 /\ (new_state.log = build_log new_state.msg_list)
	 /\ (new_state.log_length = Seq.length new_state.log )

(* State monitor update predicates *)
  type AgreeOnVersion (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) =
	 s.pv = readProtocolVersion msg len

  type AgreeOnKEM (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) =
	 s.kem = readKem msg len
		       
  type csRequiresServerCertificate (s:state_mon) =
	 (s.kem = DiffieHellman)
	 \/ (s.kem = DHE)
	 \/ (s.kem = DHE_export)
         \/ (s.kem = ECDHE)
	 \/ (s.kem = ECDH)
         \/ (s.kem = RSA_export)
	 \/ (s.kem = RSA)

  type csRequiresServerKeyExchange (s:state_mon) =
	 (s.kem = DHE)
	 \/ (s.kem = DHE_export)
         \/ (s.kem = ECDHE)
	 \/ (s.kem = DH_anonymous)
         \/ (s.kem = RSA_export)
	 \/ (s.kem = ECDH_anonymous)

  type HaveSameStateValuesAndRole (s1:state_mon) (s2:state_mon) =
	 (s1.pv = s2.pv)
	 /\ (s1.role = s2.role)
	 /\ (s1.kem = s2.kem)
	 /\ (s1.client_auth = s2.client_auth)
	 /\ (s1.resumption = s2.resumption)
	 /\ (s1.renegotiation = s2.renegotiation)
	 /\ (s1.ntick = s2.ntick)

  type HaveSameStateValuesButVersionAndCS (s1:state_mon) (s2:state_mon) =
	 (s1.role = s2.role)
	 /\ (s1.client_auth = s2.client_auth)
	 /\ (s1.resumption = s2.resumption)
	 /\ (s1.renegotiation = s2.renegotiation)
	 /\ (s1.ntick = s2.ntick)

  type HaveSameStateValuesButRole (s1:state_mon) (s2:state_mon) =
	 (s1.pv = s2.pv)
	 /\ (s1.kem = s2.kem)
	 /\ (s1.client_auth = s2.client_auth)
	 /\ (s1.resumption = s2.resumption)
	 /\ (s1.renegotiation = s2.renegotiation)
	 /\ (s1.ntick = s2.ntick)

  type HaveSameStateValuesButClientAuth (s1:state_mon) (s2:state_mon) =
	 (s1.pv = s2.pv)
	 /\ (s1.role = s2.role)
	 /\ (s1.kem = s2.kem)
	 /\ (s1.resumption = s2.resumption)
	 /\ (s1.renegotiation = s2.renegotiation)
	 /\ (s1.ntick = s2.ntick)

  type HaveSameStateValuesButResumption (s1:state_mon) (s2:state_mon) =
	 (s1.pv = s2.pv)
	 /\ (s1.role = s2.role)
	 /\ (s1.kem = s2.kem)
	 /\ (s1.client_auth = s2.client_auth)
	 /\ (s1.renegotiation = s2.renegotiation)
	 /\ (s1.ntick = s2.ntick)

  type HaveSameStateValuesButResumptionAndTicket (s1:state_mon) (s2:state_mon) =
	 (s1.pv = s2.pv)
	 /\ (s1.role = s2.role)
	 /\ (s1.kem = s2.kem)
	 /\ (s1.client_auth = s2.client_auth)
	 /\ (s1.renegotiation = s2.renegotiation)

  type HaveSameStateValuesButTicket (s1:state_mon) (s2:state_mon) =
	 (s1.pv = s2.pv)
	 /\ (s1.role = s2.role)
	 /\ (s1.kem = s2.kem)
	 /\ (s1.client_auth = s2.client_auth)
	 /\ (s1.resumption = s2.resumption)
	 /\ (s1.renegotiation = s2.renegotiation)

type StateAfterInitialState (s:state_mon) =
  (s.pv = UndefinedPV)
  /\ (s.role = UndefinedRole)
  /\ (s.kem = UndefinedKEM)
  /\ (s.last_message = UndefinedMessageType)
  /\ (s.client_auth = UndefinedAuth)
  /\ (s.resumption = Undefined)
  /\ (s.renegotiation = Undefined)
  /\ (s.ntick = Undefined)
  /\ (s.log = Seq.create 0 0)
  /\ (s.log_length = 0)
  /\ (s.msg_list = [])

type StateAfterClientHello (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{ len = Seq.length msg }).
   (state.last_message = ClientHello )
   /\ (HaveSameStateValuesButRole state old_state)
   /\ (state.role = Client \/ state.role = Server )
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientHello msg len Handshake)
   /\ (StateAfterInitialState old_state)
  )
  
type NextStateAfterClientHello (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{ len = Seq.length msg }).
   (state.last_message = ClientHello )
   /\ (HaveSameStateValuesButRole state old_state)
   /\ (state.role = Client \/ state.role = Server )
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientHello msg len Handshake)
   /\ (StateAfterInitialState old_state)
  )

type StateAfterServerHello (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerHello )
   /\ (HaveSameStateValuesButVersionAndCS state old_state)
   /\ (AgreeOnVersion state msg len)
   /\ (AgreeOnKEM state msg len)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerHello msg len Handshake)
   /\ (StateAfterClientHello old_state)
  )

type NextStateAfterServerHello (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerHello )
   /\ (HaveSameStateValuesButVersionAndCS state old_state)
   /\ (AgreeOnVersion state msg len)
   /\ (AgreeOnKEM state msg len)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerHello msg len Handshake)
   /\ (StateAfterClientHello old_state)
  )

type StateAfterServerCertificate (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCertificate )
   /\ (state.resumption = No)
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerCertificate state msg len direction Handshake)
   /\ (StateAfterServerHello old_state)
  )

type NextStateAfterServerCertificate (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCertificate )
   /\ (state.resumption = No)
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerCertificate state msg len direction Handshake)
   /\ (StateAfterServerHello old_state)
  )

type StateAfterServerKeyExchange (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerKeyExchange )
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerKeyExchange msg len Handshake)
   /\ (state.resumption = No) (* Check that this is correct *)
   /\ (
	( StateAfterServerCertificate old_state /\ (state.kem = DHE \/ state.kem = ECDHE \/ state.kem = DHE_export \/ state.kem = RSA_export))
	\/ ( StateAfterServerHello old_state /\ ( state.kem = DH_anonymous \/ state.kem = ECDH_anonymous))
      )
  )

type NextStateAfterServerKeyExchange (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerKeyExchange )
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerKeyExchange msg len Handshake)
   /\ (state.resumption = No) (* Check that this is correct *)
   /\ (
	( StateAfterServerCertificate old_state /\ (state.kem = DHE \/ state.kem = ECDHE \/ state.kem = DHE_export \/ state.kem = RSA_export))
	\/ ( StateAfterServerHello old_state /\ ( state.kem = DH_anonymous \/ state.kem = ECDH_anonymous))
      )
  )

type StateAfterServerCertificateRequest (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCertificateRequest )
   /\ (HaveSameStateValuesButClientAuth state old_state)
   /\ (state.client_auth = Auth_requested)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerCertificateRequest  msg len Handshake)
   /\ (
	(StateAfterServerCertificate old_state)
	  \/ ((StateAfterServerKeyExchange old_state) 
	      /\ (old_state.kem = DiffieHellman \/ old_state.kem = ECDH \/ old_state.kem = DHE
		   \/ old_state.kem = DHE_export \/ old_state.kem = ECDHE ))
      )
  )

type NextStateAfterServerCertificateRequest (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCertificateRequest )
   /\ (HaveSameStateValuesButClientAuth state old_state)
   /\ (state.client_auth = Auth_requested)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerCertificateRequest  msg len Handshake)
   /\ (
	(StateAfterServerCertificate old_state)
	  \/ ((StateAfterServerKeyExchange old_state) 
	      /\ (old_state.kem = DiffieHellman \/ old_state.kem = ECDH \/ old_state.kem = DHE
		   \/ old_state.kem = DHE_export \/ old_state.kem = ECDHE ))
      )
  )

type StateAfterServerHelloDone (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerHelloDone )
   /\ (HaveSameStateValuesButClientAuth state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerHelloDone msg len Handshake)
   /\ (
	((StateAfterServerCertificate old_state)
	 /\ ( 
	      (old_state.kem = ECDH) 
              \/ (old_state.kem = DiffieHellman) 
              \/ (old_state.kem = RSA) )
	 /\ (state.client_auth = No_auth))

	\/ (
	    (StateAfterServerKeyExchange old_state) 
	    /\ (
		 (old_state.kem = DH_anonymous) 
                 \/ (old_state.kem = ECDH_anonymous) 
                 \/ (old_state.kem = DHE) 
                 \/ (old_state.kem = DHE_export) 
                 \/ (old_state.kem = RSA_export) 
                 \/ (old_state.kem = ECDHE) 
	       )
	    /\ (state.client_auth = No_auth))

        \/ (
            (StateAfterServerCertificateRequest old_state)
	    /\ (
		 (old_state.kem = DiffieHellman)
                 \/ (old_state.kem = ECDH)
		 \/ (old_state.kem = RSA) 
                 \/ (old_state.kem = DHE) 
                 \/ (old_state.kem = DHE_export) 
                 \/ (old_state.kem = RSA_export) 
                 \/ (old_state.kem = ECDHE) )
	    /\ (state.client_auth = old_state.client_auth))
      )
  )

type NextStateAfterServerHelloDone (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerHelloDone )
   /\ (HaveSameStateValuesButClientAuth state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerHelloDone msg len Handshake)
   /\ (
	((StateAfterServerCertificate old_state)
	 /\ ( old_state.kem = ECDH \/ old_state.kem = DiffieHellman \/ old_state.kem = RSA )
	 /\ (state.client_auth = No_auth))

	\/ ((StateAfterServerKeyExchange old_state) 
	    /\ (old_state.kem = DH_anonymous \/ old_state.kem = ECDH_anonymous \/ old_state.kem = DHE \/ old_state.kem = DHE_export \/ old_state.kem = RSA_export \/ old_state.kem = ECDHE )
	    /\ (state.client_auth = No_auth))

        \/ ((StateAfterServerCertificateRequest old_state)
	    /\ (old_state.kem = DiffieHellman \/ old_state.kem = ECDH \/ old_state.kem = RSA \/ old_state.kem = DHE \/ old_state.kem = DHE_export \/ old_state.kem = RSA_export \/ old_state.kem = ECDHE )
	    /\ (state.client_auth = old_state.client_auth))
      )
  )


type StateAfterClientCertificate (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCertificate )
   /\ (HaveSameStateValuesButClientAuth state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientCertificate state msg len direction Handshake)
   /\ (StateAfterServerHelloDone old_state)
   /\ (old_state.client_auth = Auth_requested)
   /\ (
	((isEmptyClientCertificate old_state msg len direction)
	 /\ (state.client_auth = Auth_not_provided))

	\/ ((isNonEmptyClientCertificate old_state msg len direction)
	    /\ (state.client_auth = Auth_provided))
      )
  )

type NextStateAfterClientCertificate (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCertificate )
   /\ (HaveSameStateValuesButClientAuth state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientCertificate state msg len direction Handshake)
   /\ (StateAfterServerHelloDone old_state)
   /\ (old_state.client_auth = Auth_requested)
   /\ (
	((isEmptyClientCertificate old_state msg len direction)
	 /\ (state.client_auth = Auth_not_provided))

	\/ ((isNonEmptyClientCertificate old_state msg len direction)
	    /\ (state.client_auth = Auth_provided))
      )
  )

type StateAfterClientKeyExchange (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ClientKeyExchange )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientKeyExchange msg len Handshake)
   /\
      (
      ((StateAfterClientCertificate old_state)
       /\ ( (old_state.client_auth = Auth_provided) \/ (old_state.client_auth = Auth_not_provided) ))

      \/ ((StateAfterServerHelloDone old_state)
	  /\ (old_state.client_auth = No_auth ))
      )
  )


type NextStateAfterClientKeyExchange (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ClientKeyExchange )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientKeyExchange msg len Handshake)
   /\
      (
	((StateAfterClientCertificate old_state)
	 /\ ( (old_state.client_auth = Auth_provided) \/ (old_state.client_auth = Auth_not_provided) ))

         \/ ((StateAfterServerHelloDone old_state)
	     /\ (old_state.client_auth = No_auth ))
      )
  )

type StateAfterClientCertificateVerify (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCertificateVerify )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientCertificateVerify msg len Handshake)
   /\ (StateAfterClientKeyExchange old_state)
   /\ (old_state.client_auth = Auth_provided )
  )

type NextStateAfterClientCertificateVerify (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCertificateVerify )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientCertificateVerify msg len Handshake)
   /\ (StateAfterClientKeyExchange old_state)
   /\ (old_state.client_auth = Auth_provided )
  )

type StateAfterClientCCS (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCCS )
   /\ (state.resumption = No)
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (isClientChangeCipherSpecs state msg len direction Handshake)
   /\
      (
	(StateAfterClientCertificateVerify old_state)
	  
	  \/ ((StateAfterClientKeyExchange old_state)
	      /\ (old_state.client_auth = No_auth \/ old_state.client_auth = Auth_not_provided))
	       
          \/ ((StateAfterClientCertificate old_state) 
	      /\ (old_state.kem = DiffieHellman \/ old_state.kem = ECDH ))
      )
  )

type NextStateAfterClientCCS (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCCS )
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (isClientChangeCipherSpecs state msg len direction Handshake)
   /\
      (
	(StateAfterClientCertificateVerify old_state)
	  
	  \/ ((StateAfterClientKeyExchange old_state)
	      /\ (old_state.client_auth = No_auth \/ old_state.client_auth = Auth_not_provided))
	       
          \/ ((StateAfterClientCertificate old_state) 
	      /\ (old_state.kem = DiffieHellman \/ old_state.kem = ECDH ))
      )
  )

type StateAfterClientFin (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCS old_state)
  )

type NextStateAfterClientFin (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCS old_state)
  )

type StateAfterServerNewSessionTicket (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{ len = Seq.length msg}).
   (state.last_message = ServerNewSessionTicket )
   /\ (HaveSameStateValuesButResumptionAndTicket state old_state)
   /\ (MessageAddedToLog state old_state msg len )
   /\ (isServerNewSessionTicket msg len Handshake)
   /\ (state.ntick = Yes)
   /\ (
	((StateAfterServerHello old_state) /\ (state.resumption = Yes))
	  \/ ((StateAfterClientFin old_state) 
	      /\ (old_state.resumption = No) 
	      /\ (state.resumption = No))
      )
  )

type NextStateAfterServerNewSessionTicket (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{ len = Seq.length msg}).
   (state.last_message = ServerNewSessionTicket )
   /\ (HaveSameStateValuesButResumptionAndTicket state old_state)
   /\ (MessageAddedToLog state old_state msg len )
   /\ (isServerNewSessionTicket msg len Handshake)
   /\ (state.ntick = Yes)
   /\ (
	((StateAfterServerHello old_state) /\ (state.resumption = Yes))
	  \/ ((StateAfterClientFin old_state) 
	      /\ (old_state.resumption = No) 
	      /\ (state.resumption = No))
      )
  )

type StateAfterServerCCS (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCCS )
   /\ (HaveSameStateValuesButResumptionAndTicket state old_state)
   /\ (isServerChangeCipherSpecs state msg len direction Handshake)
   /\ 
      (
	((StateAfterServerHello old_state) 
	 /\ (state.resumption = Yes)
	 /\ (state.ntick = No))

	  \/ ((StateAfterClientFin old_state) 
	      /\ (old_state.resumption = No )
	      /\ (state.resumption = No)
	      /\ (old_state.ntick = Undefined))

	  \/ ((StateAfterServerNewSessionTicket old_state)
	      /\ (state.resumption = old_state.resumption)
	      /\ (state.ntick = old_state.ntick)) 
      )
  )

type NextStateAfterServerCCS (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCCS )
   /\ (HaveSameStateValuesButResumptionAndTicket state old_state)
   /\ (isServerChangeCipherSpecs state msg len direction Handshake)
   /\ 
      (
	((StateAfterServerHello old_state) 
	 /\ (state.resumption = Yes)
	 /\ (state.ntick = No))

	  \/ ((StateAfterClientFin old_state) 
	      /\ (old_state.resumption = No )
	      /\ (state.resumption = No)
	      /\ (old_state.ntick = Undefined))

	  \/ ((StateAfterServerNewSessionTicket old_state)
	      /\ (state.resumption = old_state.resumption)
	      /\ (state.ntick = old_state.ntick)) 
      )
  )

type StateAfterServerFin (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerFin state msg len direction Handshake)
   /\ (StateAfterServerCCS old_state)
  )

type NextStateAfterServerFin (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerFin state msg len direction Handshake)
   /\ (StateAfterServerCCS old_state)
  )

type StateAfterClientCCSLastMsg (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCCS )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientChangeCipherSpecs state msg len direction Handshake)
   /\ (state.resumption = Yes)
   /\ (StateAfterServerFin old_state)
  )

type NextStateAfterClientCCSLastMsg (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCCS )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientChangeCipherSpecs state msg len direction Handshake)
   /\ (state.resumption = Yes)
   /\ (StateAfterServerFin old_state)
  )

type StateAfterClientFinLastMsg (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCSLastMsg old_state)
  )

type NextStateAfterClientFinLastMsg (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCSLastMsg old_state)
  )

(* Key predicate representing an acceptable state during the handshake *)
type isValidState (state:state_mon) =
  (StateAfterInitialState state)
  \/ (StateAfterClientHello state)
  \/ (StateAfterServerHello state)
  \/ (StateAfterServerCertificate state)
  \/ (StateAfterServerKeyExchange state)
  \/ (StateAfterServerCertificateRequest state)
  \/ (StateAfterServerHelloDone state)
  \/ (StateAfterClientCertificate state)
  \/ (StateAfterClientKeyExchange state)
  \/ (StateAfterClientCertificateVerify state)
  \/ (StateAfterServerNewSessionTicket state)
  \/ (StateAfterServerCCS state)
  \/ (StateAfterServerFin state)
  \/ (StateAfterClientCCS state)
  \/ (StateAfterClientFin state)
  \/ (StateAfterClientCCSLastMsg state)
  \/ (StateAfterClientFinLastMsg state)

(* Key predicate stating that one valid state is the legitimate update of another *) 
type NextStateAfter (s1:state_mon) (s2:state_mon) =
  (NextStateAfterClientHello s1 s2)
  \/ (NextStateAfterServerHello s1 s2)
  \/ (NextStateAfterServerCertificate s1 s2)
  \/ (NextStateAfterServerKeyExchange s1 s2)
  \/ (NextStateAfterServerCertificateRequest s1 s2)
  \/ (NextStateAfterServerHelloDone s1 s2)
  \/ (NextStateAfterClientCertificate s1 s2)
  \/ (NextStateAfterClientKeyExchange s1 s2)
  \/ (NextStateAfterClientCertificateVerify s1 s2)
  \/ (NextStateAfterServerNewSessionTicket s1 s2)
  \/ (NextStateAfterServerCCS s1 s2)
  \/ (NextStateAfterServerFin s1 s2)
  \/ (NextStateAfterClientCCS s1 s2)
  \/ (NextStateAfterClientFin s1 s2)
  \/ (NextStateAfterClientCCSLastMsg s1 s2)
  \/ (NextStateAfterClientFinLastMsg s1 s2)

(* States that two states have the same negociated values *)
type HaveSameStateValues (s1:state_mon) (s2:state_mon) =
    (s1.pv = s2.pv)
  /\ (s1.kem = s2.kem)
  /\ (s1.client_auth = s2.client_auth)
  /\ (s1.resumption = s2.resumption)
  /\ (s1.renegotiation = s2.renegotiation)
  /\ (s1.ntick = s2.ntick)

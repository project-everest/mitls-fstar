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

type auth =
  | Auth_requested
  | No_auth
  | Auth_not_provided
  | Auth_provided
  | Auth_with_fixed_DH
  | UndefinedAuth

type state_mon =  { 
    pv:pv;
    role:role;
    kem:kem;
    last_message:messageType;
    client_auth:auth;
    resumption:tern;
    renegotiation:tern;
    ntick:tern;
    msg_list:list byte_string;
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
	 (s.role = Server /\ direction = received )
	   \/ (s.role = Client /\ direction = sent )

  type sentByServer (s:state_mon) (direction:bool) = 
	 (s.role = Client /\ direction = received )
	   \/ (s.role = Server /\ direction = sent )

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
	 /\ (index msg 0 = 1) 
	 /\ (sentByServer s direction)  
	 /\ (len = 1)

  type isServerFin (s:state_mon) (msg:byte_string) (len:nat{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = Handshake) 
	 /\ (isMessageLength msg len)
	 /\ (readMessageType (index msg 0) = Finished) 
	 /\ (sentByServer s direction)  

  type isClientChangeCipherSpecs (s:state_mon) (msg:byte_string) (len:pos{ len <= Seq.length msg }) (direction:bool) (contentType:contentType) =
 	 (contentType = ChangeCipherSpec) 
	 /\ (index msg 0 = 1) 
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
	 isClientCertificate s msg len direction Handshake /\ len = 4

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


(* Log / message list lemmas  *)				   
val build_log:
  msg_list:list byte_string ->
  Tot byte_string

val get_length:
  log:byte_string{ Seq.length log >= 4 } ->
  Tot nat

val get_first:
  #a:Type -> l:list a{ List.length l > 0 }  -> Tot a

val get_tail:
  #a:Type -> l:list a{ List.length l > 0 } -> Tot (list a)

val parse:
  log:byte_string ->
  Tot (option (list byte_string))
      (decreases (Seq.length log))

val intermediate_lemma_2:
  msg:byte_string{ isMessageLength msg (Seq.length msg) } ->
  Lemma
    (requires (True))
    (ensures ((is_Some (parse msg))
	      /\ (Some.v (parse msg) = [msg])))

#reset-options

val intermediate_lemma_3:
  log:byte_string{ is_Some (parse log) } ->
  msg:byte_string{ isMessageLength msg (Seq.length msg) } ->
  Lemma
    (requires (True))
    (ensures (is_Some (parse (Seq.append msg log))
	      /\ (Some.v (parse (Seq.append msg log)) = List.append (Some.v (parse log)) [msg])))

#reset-options

val intermediate_lemma_1:
  log:byte_string{ is_Some (parse log) } ->
  msg:byte_string{ isMessageLength msg (Seq.length msg) } ->
  Lemma
    (requires (True))
    (ensures (is_Some (parse (Seq.append log msg))
	      /\ (Some.v (parse (Seq.append log msg)) = msg::(Some.v (parse log)))))
    (decreases (Seq.length log))

#reset-options

(* Bijectivity lemma between parse and build_log given well formatted messages *)
val bijectivity_lemma:
  msg_list:list byte_string{ 
	     (forall (msg:byte_string).
	      mem msg msg_list ==> isMessageLength msg (Seq.length msg))
	   } ->
  Lemma
    (requires (True))
    (ensures (is_Some (parse (build_log msg_list))
	      /\ (Some.v (parse (build_log msg_list)) = msg_list) ))

(* Log predicates *)
type MessageAddedToLog (new_state:state_mon) (old_state:state_mon) (msg:byte_string) (len:nat{ len = Seq.length msg}) =
	 (new_state.msg_list = msg::(old_state.msg_list))
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

(* Valid state predicates *)
opaque type StateAfterInitialState (s:state_mon) =
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

opaque type StateAfterClientHello (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{ len = Seq.length msg }).
   (state.last_message = ClientHello )
   /\ (HaveSameStateValuesButRole state old_state)
   /\ (state.role = Client \/ state.role = Server )
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientHello msg len Handshake)
   /\ (StateAfterInitialState old_state)
  )
  
opaque type NextStateAfterClientHello (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{ len = Seq.length msg }).
   (state.last_message = ClientHello )
   /\ (HaveSameStateValuesButRole state old_state)
   /\ (state.role = Client \/ state.role = Server )
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientHello msg len Handshake)
   /\ (StateAfterInitialState old_state)
  )

opaque type StateAfterServerHello (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerHello )
   /\ (HaveSameStateValuesButVersionAndCS state old_state)
   /\ (AgreeOnVersion state msg len)
   /\ (AgreeOnKEM state msg len)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerHello msg len Handshake)
   /\ (StateAfterClientHello old_state)
  )

opaque type NextStateAfterServerHello (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerHello )
   /\ (HaveSameStateValuesButVersionAndCS state old_state)
   /\ (AgreeOnVersion state msg len)
   /\ (AgreeOnKEM state msg len)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerHello msg len Handshake)
   /\ (StateAfterClientHello old_state)
  )

opaque type StateAfterServerCertificate (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCertificate )
   /\ (state.resumption = No)
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerCertificate state msg len direction Handshake)
   /\ (StateAfterServerHello old_state)
  )

opaque type NextStateAfterServerCertificate (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerCertificate )
   /\ (state.resumption = No)
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerCertificate state msg len direction Handshake)
   /\ (StateAfterServerHello old_state)
  )

opaque type StateAfterServerKeyExchange (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerKeyExchange )
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerKeyExchange msg len Handshake)
   /\ (state.resumption = No)
   /\ (
	( StateAfterServerCertificate old_state /\ (state.kem = DHE \/ state.kem = ECDHE \/ state.kem = DHE_export \/ state.kem = RSA_export))
	\/ ( StateAfterServerHello old_state /\ ( state.kem = DH_anonymous \/ state.kem = ECDH_anonymous))
      )
  )

opaque type NextStateAfterServerKeyExchange (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }).
   (state.last_message = ServerKeyExchange )
   /\ (HaveSameStateValuesButResumption state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerKeyExchange msg len Handshake)
   /\ (state.resumption = No) 
   /\ (
	( StateAfterServerCertificate old_state /\ (state.kem = DHE \/ state.kem = ECDHE \/ state.kem = DHE_export \/ state.kem = RSA_export))
	\/ ( StateAfterServerHello old_state /\ ( state.kem = DH_anonymous \/ state.kem = ECDH_anonymous))
      )
  )

opaque type StateAfterServerCertificateRequest (state:state_mon) =
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

opaque type NextStateAfterServerCertificateRequest (state:state_mon) (old_state:state_mon) =
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

opaque type StateAfterServerHelloDone (state:state_mon) =
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


opaque type NextStateAfterServerHelloDone (state:state_mon) (old_state:state_mon) =
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


opaque type StateAfterClientCertificate (state:state_mon) =
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


opaque type NextStateAfterClientCertificate (state:state_mon) (old_state:state_mon) =
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

opaque type StateAfterClientKeyExchange (state:state_mon) =
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


opaque type NextStateAfterClientKeyExchange (state:state_mon) (old_state:state_mon) =
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

opaque type StateAfterClientCertificateVerify (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCertificateVerify )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientCertificateVerify msg len Handshake)
   /\ (StateAfterClientKeyExchange old_state)
   /\ (old_state.client_auth = Auth_provided )
  )

opaque type NextStateAfterClientCertificateVerify (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCertificateVerify )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientCertificateVerify msg len Handshake)
   /\ (StateAfterClientKeyExchange old_state)
   /\ (old_state.client_auth = Auth_provided )
  )

opaque type StateAfterClientCCS (state:state_mon) =
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

opaque type NextStateAfterClientCCS (state:state_mon) (old_state:state_mon) =
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

opaque type StateAfterClientFin (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCS old_state)
  )

opaque type NextStateAfterClientFin (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCS old_state)
  )

opaque type StateAfterServerNewSessionTicket (state:state_mon) =
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

opaque type NextStateAfterServerNewSessionTicket (state:state_mon) (old_state:state_mon) =
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

opaque type StateAfterServerCCS (state:state_mon) =
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

opaque type NextStateAfterServerCCS (state:state_mon) (old_state:state_mon) =
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

opaque type StateAfterServerFin (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerFin state msg len direction Handshake)
   /\ (StateAfterServerCCS old_state)
  )

opaque type NextStateAfterServerFin (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ServerFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (MessageAddedToLog state old_state msg len)
   /\ (isServerFin state msg len direction Handshake)
   /\ (StateAfterServerCCS old_state)
  )

opaque type StateAfterClientCCSLastMsg (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCCS )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientChangeCipherSpecs state msg len direction Handshake)
   /\ (state.resumption = Yes)
   /\ (StateAfterServerFin old_state)
  )

opaque type NextStateAfterClientCCSLastMsg (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientCCS )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientChangeCipherSpecs state msg len direction Handshake)
   /\ (state.resumption = Yes)
   /\ (StateAfterServerFin old_state)
  )

opaque type StateAfterClientFinLastMsg (state:state_mon) =
  (exists (old_state:state_mon) (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCSLastMsg old_state)
  )

opaque type NextStateAfterClientFinLastMsg (state:state_mon) (old_state:state_mon) =
  (exists (msg:byte_string) (len:pos{len = Seq.length msg }) (direction:bool).
   (state.last_message = ClientFinished )
   /\ (HaveSameStateValuesAndRole state old_state)
   /\ (isClientFin state msg len direction Handshake)
   /\ (StateAfterClientCCSLastMsg old_state)
  )

(* Global validity predicate *)
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

type HaveSameStateValues (s1:state_mon) (s2:state_mon) =
	 (s1.pv = s2.pv)
	 /\ (s1.kem = s2.kem)
	 /\ (s1.client_auth = s2.client_auth)
	 /\ (s1.resumption = s2.resumption)
	 /\ (s1.renegotiation = s2.renegotiation)
	 /\ (s1.ntick = s2.ntick)

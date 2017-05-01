(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

(* Handshake protocol messages *)
module HandshakeMessages
open FStar.Seq
open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open Extensions
open TLSInfo
open Range
open CommonDH

//#set-options "--lax"

(* JK: for verification purposes the "--lax" flag is set throughout the file in order to
   skip the already verified part of it.
   Just comment out '#set-options "--lax"' *)
//#set-options "--lax"

(* External functions, locally annotated for speed *)
(*
assume val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:bytes{lSize <= length vlb}
  -> Tot (result (b:(bytes * bytes){
                      repr_bytes (length (fst b)) <= lSize
                  /\  Seq.equal vlb (vlbytes lSize (fst b) @| (snd b))}))

assume val split: b:bytes -> n:nat{length b >= n} -> Tot (x:(bytes*bytes){Seq.equal b ((fst x) @| (snd x)) /\ length (fst x) = n})

assume val split2: b:bytes -> n1:nat -> n2:nat{length b >= n1 + n2} -> Tot (x:(lbytes n1 * lbytes n2 * bytes){forall x1. forall x2. forall x3. x = (x1,x2,x3) ==> Seq.equal b (x1 @| x2 @| x3)})
*)

(*** Following RFC5246 A.4 *)

(* let injective_bytes (#a:Type) (f:a -> Tot bytes) : GTot Type0 = (forall v1 v2. f v1 = f v2 ==> v1 = v2) *)

val lbyte_eq_lemma: a:byte -> b:byte -> Lemma (requires (True)) (ensures (a <> b ==> abyte a <> abyte b))
  [SMTPat (abyte a); SMTPat (abyte b)]
let lbyte_eq_lemma a b = if a <> b then cut (Seq.index (abyte a) 0 <> Seq.index (abyte b) 0) else ()

(* TODO: move to TLSConstants *)
type handshakeType =
  | HT_hello_request
  | HT_client_hello
  | HT_server_hello
  | HT_session_ticket
  | HT_hello_retry_request
  | HT_encrypted_extensions
  | HT_certificate
  | HT_server_key_exchange
  | HT_certificate_request
  | HT_server_hello_done
  | HT_certificate_verify
  | HT_client_key_exchange
  | HT_server_configuration
  | HT_finished
  | HT_key_update
  | HT_next_protocol

val htBytes: handshakeType -> Tot (lbytes 1)
let htBytes t =
  match t with
  | HT_hello_request        -> abyte  0z
  | HT_client_hello         -> abyte  1z
  | HT_server_hello         -> abyte  2z
  | HT_session_ticket       -> abyte  4z
  | HT_hello_retry_request  -> abyte  6z
  | HT_encrypted_extensions -> abyte  8z
  | HT_certificate          -> abyte 11z
  | HT_server_key_exchange  -> abyte 12z
  | HT_certificate_request  -> abyte 13z
  | HT_server_hello_done    -> abyte 14z
  | HT_certificate_verify   -> abyte 15z
  | HT_client_key_exchange  -> abyte 16z
  | HT_server_configuration -> abyte 17z
  | HT_finished             -> abyte 20z
  | HT_key_update           -> abyte 24z
  | HT_next_protocol        -> abyte 67z

#reset-options "--z3rlimit 100"
val htBytes_is_injective: ht1:handshakeType -> ht2:handshakeType -> Lemma (requires (True)) (ensures (htBytes ht1 = htBytes ht2 ==> ht1 = ht2))
  [SMTPat (htBytes ht1); SMTPat (htBytes ht2)]
let htBytes_is_injective ht1 ht2 = ()

val parseHt: pinverse_t htBytes
let parseHt b =
  match cbyte b with
  |  0z -> Correct HT_hello_request
  |  1z -> Correct HT_client_hello
  |  2z -> Correct HT_server_hello
  |  4z -> Correct HT_session_ticket
  |  6z -> Correct HT_hello_retry_request
  |  8z -> Correct HT_encrypted_extensions
  | 11z -> Correct HT_certificate
  | 12z -> Correct HT_server_key_exchange
  | 13z -> Correct HT_certificate_request
  | 14z -> Correct HT_server_hello_done
  | 15z -> Correct HT_certificate_verify
  | 16z -> Correct HT_client_key_exchange
  | 17z -> Correct HT_server_configuration
  | 20z -> Correct HT_finished
  | 67z -> Correct HT_next_protocol
  | _   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

#reset-options "--z3rlimit 600 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val inverse_ht: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f htBytes parseHt x)
  [SMTPat (parseHt (htBytes x))]
let inverse_ht x = admit ()

val pinverse_ht: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal htBytes parseHt x))
  [SMTPat (htBytes (Correct?._0 (parseHt x)))]
let pinverse_ht x = ()

/// Messages

//  https://tlswg.github.io/tls13-spec/#rfc.section.4.1.2 
noeq type ch = {
  ch_protocol_version: protocolVersion;  // max supported version up to TLS_1p2 (TLS 1.3 uses the supported_versions extension)
  ch_client_random: TLSInfo.random; 
  ch_sessionID:sessionID;
  ch_cipher_suites:(k:valid_cipher_suites{List.Tot.length k < 256});
  ch_raw_cipher_suites:option bytes;
  ch_compressions:(cl:list compression{List.Tot.length cl > 0 /\ List.Tot.length cl < 256});
  ch_extensions:option (ce:list extension{List.Tot.length ce < 256});
}

let ch_is_resumption { ch_sessionID = sid } = length sid > 0

// ServerHello: supporting two different syntaxes
// https://tools.ietf.org/html/rfc5246#section-7.4.1.2 
// https://tlswg.github.io/tls13-spec/#rfc.section.4.1.3
noeq type sh = {
  sh_protocol_version:protocolVersion; 
  sh_server_random:TLSInfo.random;
  sh_sessionID:option sessionID;  // omitted in TLS 1.3
  sh_cipher_suite:valid_cipher_suite;
  sh_compression:option compression; // omitted in TLS 1.3
  sh_extensions:option (se:list extension{List.Tot.length se < 256});
}

(* Hello retry request *)
noeq type hrr = {
  hrr_protocol_version:protocolVersion;
  hrr_cipher_suite:valid_cipher_suite;
  hrr_named_group:namedGroup; // JK : is it the expected type here ?
  hrr_extensions:(he:list extension{List.Tot.length he < 256});
}

type sticket = {
  sticket_ticket_lifetime_hint:(b:bytes{length b = 4});
  sticket_ticket:(b:bytes{length b < 16777212});
}

noeq type ee = {
  ee_extensions:(ee:list extension{List.Tot.length ee < 256});
}

type crt = {
  crt_chain: Cert.chain
}

type cr = {
  cr_cert_types: (cl:list certType{List.Tot.length cl < 256});
  cr_sig_hash_algs: option (shs:list sigHashAlg{List.Tot.length shs < 256});
  cr_distinguished_names: (dl:list dn{List.Tot.length dl < 128});
}

noeq type kex_s =
| KEX_S_DHE of (g:CommonDH.group & CommonDH.pre_share g)
| KEX_S_RSA of (pk:CoreCrypto.rsa_key{False}) // Unimplemented

noeq type kex_s_priv =
| KEX_S_PRIV_DHE of (g:CommonDH.group & CommonDH.keyshare g)
| KEX_S_PRIV_RSA of CoreCrypto.rsa_key

noeq type ske = {
  ske_kex_s: kex_s;
//  ske_sigval: option bytes;
  ske_sig : (b:bytes{length b < 65536})
}

type kex_c =
| KEX_C_DHE of (b:bytes{length b < 65536})
| KEX_C_ECDHE of (b:bytes{length b < 256})
| KEX_C_RSA of (b:bytes{length b < 4096})
| KEX_C_DH

noeq type cke = {
  cke_kex_c: kex_c
}

type cv = {
  cv_sig: (l:bytes{length l < 65536});
}

noeq type sc = {
  sc_configuration_id:configurationId;
  sc_expiration_date:uint32;
  sc_named_group:namedGroup;
  sc_server_key:kex_c; // JK : use another type ?
  sc_early_data_type:earlyDataType;
  sc_configuration_extensions:(l:list configurationExtension{List.Tot.length l < 65536});
}

//17-03-11 Finished payload, carrying a fixed-length MAC; share with binders?
type fin = {
  fin_vd: (l:bytes{length l < 65536});
}

// Next protocol message, see https://tools.ietf.org/id/draft-agl-tls-nextprotoneg-03.html
// TODO: replace shallow implementation by more precise one
type np = {
  np_selected_protocol: (b:bytes{length b < 256}); // JK: set length bounds according to
  np_padding: (b:bytes{length b < 256});           // the serialization functions (vlbytes 1 ...)
}

// TODO: unify, either keep separate finished messages for client and servers or
// merge them into single "finished" as it is the case for certificates
noeq type hs_msg =
  | ClientHello of ch
  | ServerHello of sh
  | EncryptedExtensions of ee // TLS 1.3 server

  // up to TLS 1.2
  | ClientKeyExchange of cke
  | ServerKeyExchange of ske
  | ServerHelloDone 

  | CertificateRequest of cr
  | Certificate of crt
  | CertificateVerify of cv
  | Finished of fin
  
  | NextProtocol of np // ?? 

  | HelloRequest // up to TLS 1.2
  | HelloRetryRequest of hrr // TLS 1.3 server

  // Post-Handshake (TLS 1.3) also including late CertificateRequest
  | SessionTicket of sticket //17-03-11  --> NewSessionTicket ? 

//  | ClientBinders of List Hashing.Spec.anyTag // with a 2-byte formatted length in 33..2^16-1 
//17-03-11 missing
//  | EndOfEarlyData  
//  | KeyUpdateRequest of bool  // true -> the falg indicates whether this is a "first" request (to be responded)

/// Handshake message format

val messageBytes : ht:handshakeType -> data:bytes{ repr_bytes (length data) <= 3 }
  -> Tot (lbytes (4+(length data)))
let messageBytes ht data =
  let htb = htBytes ht in
  let vldata = vlbytes 3 data in
  htb @| vldata

let hs_msg_bytes (ht:handshakeType) (b:bytes) =
  length b >= 4
  /\ (let b' = snd (split b 4) in
    repr_bytes (length b') <= 3
    /\ b = messageBytes ht b')

val messageBytes_is_injective:
  ht1:handshakeType -> data1:bytes{ repr_bytes (length data1) <= 3 } ->
  ht2:handshakeType -> data2:bytes{ repr_bytes (length data2) <= 3 } ->
  Lemma (requires (True))
	(ensures (Seq.equal (messageBytes ht1 data1) (messageBytes ht2 data2) ==> (ht1 = ht2 /\ Seq.equal data1 data2)))
  [SMTPat (messageBytes ht1 data1); SMTPat (messageBytes ht2 data2)]
let messageBytes_is_injective ht1 data1 ht2 data2 =
  if messageBytes ht1 data1 = messageBytes ht2 data2 then
    begin
      assert(Seq.equal (messageBytes ht1 data1) (messageBytes ht2 data2));
      lemma_append_inj (htBytes ht1) (vlbytes 3 data1) (htBytes ht2) (vlbytes 3 data2);
      lemma_vlbytes_inj 3 data1 data2
    end
  else ()

val parseMessage: buf:bytes
  -> Tot (result (option
		  (rem:bytes &
		   hstype:handshakeType &
		   payload:bytes{ repr_bytes (length payload) <= 3 } &
		   to_log:bytes{ to_log = messageBytes hstype payload /\
		                 Seq.equal buf (to_log @| rem) })))
(*
 Somewhat inefficient implementation:
 - Repeatedly parse the first 4 bytes of the incoming buffer until we have a complete message;
 - Then remove that message from the incoming buffer.
*)
let parseMessage buf =
  if length buf < 4 then
    Correct None // not enough data to start parsing
  else
    let hstypeb,rem = split buf 1 in
    match parseHt hstypeb with
    | Error z -> Error z
    | Correct ht ->
      match vlsplit 3 rem with
      | Error z -> Correct None // not enough payload, try next time
      | Correct(payload,rem') ->
        //assert (Seq.equal buf (htBytes ht @| rem));
        //assert (Seq.equal rem (vlbytes 3 payload @| rem'));
        let to_log = messageBytes ht payload in
        Correct (Some (| rem', ht, payload, to_log |))

(** A.4.1 Hello Messages *)

val list_valid_to_valid_list: l:valid_cipher_suites -> Tot (l':list (c:cipherSuite{validCipherSuite c}){List.Tot.length l = List.Tot.length l'})
let rec list_valid_to_valid_list l =
  match l with
  | [] -> []
  | hd::tl -> hd::(list_valid_to_valid_list tl)

val valid_list_to_list_valid: l':list (c:cipherSuite{validCipherSuite c}) -> Tot (l:valid_cipher_suites{List.Tot.length l = List.Tot.length l'})
let rec valid_list_to_list_valid l =
  match l with
  | [] -> []
  | hd::tl -> hd::(valid_list_to_list_valid tl)

(* JK: changed the serialization of the compression methods to match the spec *)
val clientHelloBytes: ch -> Tot (b:bytes{length b >= 41 /\ hs_msg_bytes HT_client_hello b}) // JK: used to be 42 but cannot prove it with current specs. Is there a minimal length of 1 for the session ID maybe ?
let clientHelloBytes ch =
  //17-04-26 this is likely to break injectivity, now conditional on an extension.
  let legacyVersion = minPV TLS_1p2 ch.ch_protocol_version in 
  let verB = versionBytes legacyVersion in
  lemma_repr_bytes_values (length ch.ch_sessionID);
  let sidB = vlbytes 1 ch.ch_sessionID in
  let csb:bytes = cipherSuitesBytes (list_valid_to_valid_list ch.ch_cipher_suites) in
  lemma_repr_bytes_values (length csb);
  let csB = vlbytes 2 csb in
  lemma_repr_bytes_values (List.Tot.length ch.ch_compressions);
  (* let cmB = match ch.ch_compressions with *)
  (*   | [] -> empty_bytes  *)
  (*   | cl -> vlbytes 1 (compressionMethodsBytes cl) in *)
  let cmB = vlbytes 1 (compressionMethodsBytes ch.ch_compressions) in
  let extB =
    match ch.ch_extensions with
    | Some ext -> extensionsBytes Client ext
    | None -> empty_bytes in
  let data = verB @| (ch.ch_client_random @| (sidB @| (csB @| (cmB @| extB)))) in
  lemma_repr_bytes_values (length data);
  messageBytes HT_client_hello data

val versionBytes_is_injective: pv1:protocolVersion -> pv2:protocolVersion ->
  Lemma (requires (True))
	(ensures (versionBytes pv1 = versionBytes pv2 ==> pv1 = pv2))
let versionBytes_is_injective pv1 pv2 =
  cut (pv1 <> pv2 ==> (Seq.index (versionBytes pv1) 0 <> Seq.index (versionBytes pv2) 0
		     \/ Seq.index (versionBytes pv1) 1 <> Seq.index (versionBytes pv2) 1))

(* JK: additional conditions are required on the size of the extensions after serialization *)
val optionExtensionsBytes: r:role -> exts:option (ce:list extension{List.Tot.length ce < 256}) -> Tot (b:bytes{length b <= 2 + 65535})
let optionExtensionsBytes r exts =
  match exts with
  | Some ext -> extensionsBytes r ext
  | None -> empty_bytes

val list_valid_to_valid_list_lemma: cs1:valid_cipher_suites{List.Tot.length cs1 < 256} ->
  cs2:valid_cipher_suites{List.Tot.length cs2 < 256} ->
  Lemma (requires (True))
	(ensures (list_valid_to_valid_list cs1 = list_valid_to_valid_list cs2 ==> cs1 = cs2))
let rec list_valid_to_valid_list_lemma cs1 cs2 =
  match cs1, cs2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' -> list_valid_to_valid_list_lemma tl tl'
  | _ -> ()

val cipherSuiteBytes_is_injective: cs:valid_cipher_suite -> cs':valid_cipher_suite ->
  Lemma (requires (True))
	(ensures (Seq.equal (cipherSuiteBytes cs) (cipherSuiteBytes cs') ==> cs = cs'))
let cipherSuiteBytes_is_injective cs cs' =
  admit(); // JK: TODO: list the issue in cipherSuiteBytes where there are possible
	   // collisions between the serialization of unknown cipher suites and known ones
  cut(Some? (cipherSuiteBytesOpt cs) /\ Some? (cipherSuiteBytesOpt cs'));
  if cs <> cs' then (
    match cipherSuiteBytesOpt cs, cipherSuiteBytesOpt cs' with
    | Some a, Some b -> assert((Seq.index a 0 <> Seq.index b 0) \/ Seq.index a 1 <> Seq.index b 1)
    | _, _ -> ()
    );
  ()

val cipherSuitesBytes_is_injective_aux: css1:list (c:cipherSuite{validCipherSuite c}) -> css2:list (c:cipherSuite{validCipherSuite c}) ->
  Lemma (requires (True))
	(ensures (Seq.equal (cipherSuitesBytes css1) (cipherSuitesBytes css2) ==> css1 = css2))
let rec cipherSuitesBytes_is_injective_aux css1 css2 =
  match css1, css2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' -> (
      if cipherSuitesBytes css1 = cipherSuitesBytes css2 then (
	assert(cipherSuitesBytes css1 = ((cipherSuiteBytes hd) @| (cipherSuitesBytes tl)));
	assert(cipherSuitesBytes css2 = ((cipherSuiteBytes hd') @| (cipherSuitesBytes tl')));
	assert(length (cipherSuiteBytes hd) = length (cipherSuiteBytes hd'));
	lemma_append_inj (cipherSuiteBytes hd) (cipherSuitesBytes tl) (cipherSuiteBytes hd') (cipherSuitesBytes tl');
	cipherSuitesBytes_is_injective_aux tl tl';
	cipherSuiteBytes_is_injective hd hd'
	)
      else ()
      )
  | _ -> ()

val cipherSuitesBytes_is_injective: cs1:valid_cipher_suites{List.Tot.length cs1 < 256} ->
  cs2:valid_cipher_suites{List.Tot.length cs2 < 256} ->
  Lemma (requires (True))
	(ensures (Seq.equal (cipherSuitesBytes (list_valid_to_valid_list cs1))
			    (cipherSuitesBytes (list_valid_to_valid_list cs2)) ==> cs1 = cs2))
let cipherSuitesBytes_is_injective cs1 cs2 =
  let l1 = list_valid_to_valid_list cs1 in
  let l2 = list_valid_to_valid_list cs2 in
  if cipherSuitesBytes l1 = cipherSuitesBytes l2
  then
    begin
      cipherSuitesBytes_is_injective_aux l1 l2;
      list_valid_to_valid_list_lemma cs1 cs2;
      ()
    end
  else ()

val compressionMethodsBytes_is_injective: l1:list compression -> l2:list compression ->
  Lemma (requires (True))
	(ensures (Seq.equal (compressionMethodsBytes l1) (compressionMethodsBytes l2) ==> l1 = l2))
let rec compressionMethodsBytes_is_injective l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if compressionMethodsBytes l1 = compressionMethodsBytes l2 then (
      compressionMethodsBytes_is_injective tl tl';
      lemma_append_inj (compressionBytes hd) (compressionMethodsBytes tl) (compressionBytes hd') (compressionMethodsBytes tl');
      assert (compressionBytes hd = compressionBytes hd' ==> hd = hd'))
  | _ -> ()

(* JK: TODO *)
assume val extensionsBytes_is_injective: r:role -> ext1:list extension{List.Tot.length ext1 < 256} -> ext2:list extension{List.Tot.length ext2 < 256} ->
  Lemma (requires (True))
	(ensures (Seq.equal (extensionsBytes r ext1) (extensionsBytes r ext2) ==> ext1 == ext2))

val optionExtensionsBytes_is_injective: r:role -> ext1:option (ce:list extension{List.Tot.length ce < 256}) ->
  ext2:option (ce2:list extension{List.Tot.length ce2 < 256}) ->
  Lemma (requires (True))
	(ensures (Seq.equal (optionExtensionsBytes r ext1) (optionExtensionsBytes r ext2) ==> ext1 == ext2))
let optionExtensionsBytes_is_injective r ext1 ext2 =
  (* JK: TODO: make the assumes part of the specifications *)
  assume (Some? ext1 ==> repr_bytes (length (List.Tot.fold_left (fun l s -> l @| extensionBytes r s) empty_bytes (Some?.v ext1))) <= 2);
  assume (Some? ext2 ==> repr_bytes (length (List.Tot.fold_left (fun l s -> l @| extensionBytes r s) empty_bytes (Some?.v ext2))) <= 2);
  match ext1, ext2 with
  | Some e1, Some e2 ->
      extensionsBytes_is_injective r e1 e2
  | None, None -> ()
  | _, _ -> ()

val clientHelloBytes_is_injective: msg1:ch -> msg2:ch ->
  Lemma (requires (True))
	(ensures (Seq.equal (clientHelloBytes msg1) (clientHelloBytes msg2) ==> (msg1 == msg2)))
  [SMTPat (clientHelloBytes msg1); SMTPat (clientHelloBytes msg2)]
let clientHelloBytes_is_injective msg1 msg2 =
  if clientHelloBytes msg1 = clientHelloBytes msg2 then
    begin
      let verB1 = versionBytes msg1.ch_protocol_version in
      lemma_repr_bytes_values (length msg1.ch_sessionID);
      let sidB1 = vlbytes 1 msg1.ch_sessionID in
      let csb1:bytes = cipherSuitesBytes (list_valid_to_valid_list msg1.ch_cipher_suites) in
      lemma_repr_bytes_values (length csb1);
      let csB1 = vlbytes 2 csb1 in
      lemma_repr_bytes_values (List.Tot.length msg1.ch_compressions);
      let cmB1 = vlbytes 1 (compressionMethodsBytes msg1.ch_compressions) in
      let extB1 =
	(match msg1.ch_extensions with
	| Some ext -> extensionsBytes Client ext
	| None -> empty_bytes) in
      let data1 = verB1 @| (msg1.ch_client_random @| (sidB1 @| (csB1 @| (cmB1 @| extB1)))) in
      lemma_repr_bytes_values (length data1);
      let verB2 = versionBytes msg2.ch_protocol_version in
      lemma_repr_bytes_values (length msg2.ch_sessionID);
      let sidB2 = vlbytes 1 msg2.ch_sessionID in
      let csb2:bytes = cipherSuitesBytes (list_valid_to_valid_list msg2.ch_cipher_suites) in
      lemma_repr_bytes_values (length csb2);
      let csB2 = vlbytes 2 csb2 in
      lemma_repr_bytes_values (List.Tot.length msg2.ch_compressions);
      let cmB2 = vlbytes 1 (compressionMethodsBytes msg2.ch_compressions) in
      let (extB2:bytes) =
	(match msg2.ch_extensions with
	| Some ext2 -> extensionsBytes Client ext2
	| None -> empty_bytes) in
      let data2 = verB2 @| (msg2.ch_client_random @| (sidB2 @| (csB2 @| (cmB2 @| extB2)))) in
      lemma_repr_bytes_values (length data2);
      messageBytes_is_injective HT_client_hello data1 HT_client_hello data2;
      lemma_append_inj verB1 (msg1.ch_client_random @| (sidB1 @| (csB1 @| (cmB1 @| extB1)))) verB2 (msg2.ch_client_random @| (sidB2 @| (csB2 @| (cmB2 @| extB2))));
      versionBytes_is_injective msg1.ch_protocol_version msg2.ch_protocol_version;
      cut(msg1.ch_protocol_version = msg2.ch_protocol_version);
      lemma_append_inj msg1.ch_client_random (sidB1 @| (csB1 @| (cmB1 @| extB1))) msg2.ch_client_random (sidB2 @| (csB2 @| (cmB2 @| extB2)));
      cut(msg1.ch_client_random = msg2.ch_client_random);
      let l1 = (sidB1 @| (csB1 @| (cmB1 @| extB1))) in
      let l2 = (sidB2 @| (csB2 @| (cmB2 @| extB2))) in
      cut(Seq.equal l1 l2);
      cut(length sidB2 >= 1 /\ length sidB1 >= 1);
      cut(Seq.index sidB1 0 = Seq.index l1 0);
      cut(Seq.index sidB2 0 = Seq.index l2 0);
      cut(Seq.index sidB1 0 = Seq.index sidB2 0);
      vlbytes_length_lemma 1 msg1.ch_sessionID msg2.ch_sessionID;
      cut(length sidB1 = length sidB2);
      lemma_append_inj sidB1 (csB1 @| (cmB1 @| extB1)) sidB2 (csB2 @| (cmB2 @| extB2));
      lemma_vlbytes_inj 1 msg1.ch_sessionID msg2.ch_sessionID;
      let l1 = (csB1 @| (cmB1 @| extB1)) in
      let l2 = (csB2 @| (cmB2 @| extB2)) in
      cut(Seq.equal l1 l2);
      cut(length csB1 >= 2 /\ length csB2 >= 2);
      cut(Seq.index csB1 0 = Seq.index l1 0 /\ Seq.index csB1 1 = Seq.index l1 1);
      cut(Seq.index csB2 0 = Seq.index l2 0 /\ Seq.index csB2 1 = Seq.index l2 1);
      vlbytes_length_lemma 2 csb1 csb2;
      cut(length csB1 = length csB2);
      lemma_append_inj csB1 (cmB1 @| extB1) csB2 (cmB2 @| extB2);
      lemma_vlbytes_inj 2 csb1 csb2;
      let l1 = (cmB1 @| extB1) in
      let l2 = (cmB2 @| extB2) in
      cut(Seq.equal l1 l2);
      cut(length cmB1 >= 1 /\ length cmB2 >= 1);
      cut(Seq.index cmB1 0 = Seq.index l1 0);
      cut(Seq.index cmB2 0 = Seq.index l2 0);
      vlbytes_length_lemma 1 (compressionMethodsBytes msg1.ch_compressions) (compressionMethodsBytes msg2.ch_compressions);
      cut(length cmB1 = length cmB2);
      lemma_append_inj cmB1 extB1 cmB2 extB2;
      lemma_vlbytes_inj 1 (compressionMethodsBytes msg1.ch_compressions) (compressionMethodsBytes msg2.ch_compressions);
      cut(msg1.ch_protocol_version = msg2.ch_protocol_version);
      cut(msg1.ch_client_random = msg2.ch_client_random);
      cut(msg1.ch_sessionID = msg2.ch_sessionID);
      cipherSuitesBytes_is_injective msg1.ch_cipher_suites msg2.ch_cipher_suites;
      compressionMethodsBytes_is_injective msg1.ch_compressions msg2.ch_compressions;
      optionExtensionsBytes_is_injective Client msg1.ch_extensions msg2.ch_extensions;
      cut(msg1.ch_cipher_suites = msg2.ch_cipher_suites);
      cut(msg1.ch_compressions = msg2.ch_compressions);
      cut(msg1.ch_extensions == msg2.ch_extensions);
      ()
   end
  else ()

(* JK: to work around a subtyping difficulty in parseClientHello *)
val coercion_helper: o:option (list extension){Some? o ==> List.Tot.length (Some?.v o) < 256} ->
  Tot (x:option (l:list extension{List.Tot.length l < 256}))
let coercion_helper o =
  match o with
  | None -> None
  | Some li -> (cut (List.Tot.length li < 256); Some li)

(* This function adds a "first connection" renegotiation info *)
(*    extension to the client hello when parsing it. The cipher suite *)
(*    parsing ignores some of them. For these two reasons, the *)
(*    serialization function is not an inverse of the parsing function as *)
(*    it is now *)
(* JK: Do we want the specification to be that precise ? I weakened it for now *)
(* val parseClientHello : data:bytes{repr_bytes(length data) <= 3} *)
(*   -> Tot  (result (x:ch{exists (x':ch). Seq.equal (clientHelloBytes x') (messageBytes HT_client_hello data) *)
(*                                  /\ x.ch_protocol_version = x'.ch_protocol_version *)
(*                                  /\ x.ch_client_random = x'.ch_client_random *)
(*                                  /\ x.ch_sessionID = x'.ch_sessionID })) *)
val parseClientHello: data:bytes{repr_bytes(length data) <= 3} -> Tot (result ch)
let parseClientHello data =
  if length data < 35 then
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  else
    let (clVerBytes,cr,data) = split2 data 2 32 in
    match parseVersion clVerBytes with
    | Error z -> Error z
    | Correct cv ->
      match vlsplit 1 data with
      | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse session id")
      | Correct (sid,data) ->
        if length sid <= 32 then
	  (if length data >= 2 then
	    (match vlsplit 2 data with
	     | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse cipher suite bytes")
	     | Correct (clCiphsuitesBytes,data) ->
	       if length clCiphsuitesBytes < 512 then
	       (match parseCipherSuites clCiphsuitesBytes with
	        | Error z -> Error z
	        | Correct clientCipherSuites ->
                  (* ADL More relaxed parsing for old ClientHello messages with *)
                  (* no compression and no extensions *)
                  let compExts =
  	            if length data >= 1 && List.Tot.length clientCipherSuites < 256 then
		    (match vlsplit 1 data with
		     | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse compression bytes")
		     | Correct (cmBytes,extensions) ->
		       let cm = parseCompressions cmBytes in
		       (match parseOptExtensions Client extensions with
		        | Error z -> Error z
		        | Correct exts ->
			  if (match exts with
			      | None -> true
			      | Some l -> List.Tot.length l < 256)
			     && List.Tot.length cm < 256
			     && List.Tot.length cm > 0
			  then (
			    let exts = coercion_helper exts in
			    Correct (cm, exts)
			    )
 			  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")))
                     (* else Correct ([], None) in *) // JK: there has to be a compression method
						      // according to the spec
                     else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "") in
                     (match compExts with
                     | Correct (cm, exts) -> (
			 cut (List.Tot.length clientCipherSuites < 256);
			 let cCS = valid_list_to_list_valid clientCipherSuites in
                            Correct ({
                              ch_protocol_version = cv;
                              ch_client_random = cr;
                              ch_sessionID = sid;
                              ch_cipher_suites = cCS;
                              ch_raw_cipher_suites = Some clCiphsuitesBytes;
                              ch_compressions = cm;
                              ch_extensions = exts;
                          })
			)
                      | Error e -> Error e))
//		  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
	       else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
	   else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
	else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val serverHelloBytes: sh -> Tot (b:bytes{length b >= 34 /\ hs_msg_bytes HT_server_hello b})
let serverHelloBytes sh =
  // signalling the current draft version
  let verB = versionBytes_draft sh.sh_protocol_version in
  let sidB =
    match sh.sh_sessionID with
    | Some sid ->
      lemma_repr_bytes_values (length sid);
      vlbytes 1 sid
    | _ -> empty_bytes
  in
  let csB = cipherSuiteBytes sh.sh_cipher_suite in
  let cmB =
    match sh.sh_compression with
    | Some compression -> compressionBytes compression
    | _ -> empty_bytes
  in
  let extB =
    match sh.sh_extensions with
    | Some ext -> extensionsBytes Server ext
    | None -> empty_bytes  // JK: in TLS1.3 case should be vlbytes 2 empty_bytes
  in
  let data:bytes =
    match sh.sh_protocol_version with
    | TLS_1p3 -> verB @| (sh.sh_server_random @| (csB @| extB))
    | _       -> verB @| (sh.sh_server_random @| (sidB @| (csB @| (cmB @| extB))))
  in
  lemma_repr_bytes_values (length data);
  messageBytes HT_server_hello data

let valid_sh : Type0 = s:sh{
  (s.sh_protocol_version = TLS_1p3 ==> (None? s.sh_sessionID /\ None? s.sh_compression))
  /\ (s.sh_protocol_version <> TLS_1p3 ==> (Some? s.sh_sessionID /\ Some? s.sh_compression)) }

#reset-options "--z3rlimit 50"
//#set-options "--lax"

val serverHelloBytes_is_injective: msg1:valid_sh -> msg2:valid_sh ->
  Lemma (requires (True))
	(ensures (Seq.equal (serverHelloBytes msg1) (serverHelloBytes msg2) ==> msg1 == msg2))
let serverHelloBytes_is_injective msg1 msg2 =
  if serverHelloBytes msg1 = serverHelloBytes msg2 then
  begin
    let verB1 = versionBytes_draft msg1.sh_protocol_version in
    let sidB1 = match msg1.sh_sessionID with
      | Some sid -> lemma_repr_bytes_values (length sid); vlbytes 1 sid
      | _ -> empty_bytes in
      let csB1 = cipherSuiteBytes msg1.sh_cipher_suite in
      let cmB1 =  match msg1.sh_compression with
      | Some compression -> compressionBytes compression
      | _ -> empty_bytes in
      let extB1 = match msg1.sh_extensions with
      | Some ext -> extensionsBytes Server ext
      | None -> empty_bytes in
      let data1:bytes = match msg1.sh_protocol_version with
      | TLS_1p3 -> verB1 @| (msg1.sh_server_random @| (csB1 @| extB1))
      | _       -> verB1 @| (msg1.sh_server_random @| (sidB1 @| (csB1 @| (cmB1 @| extB1)))) in
      lemma_repr_bytes_values (length data1);
      let verB2 = versionBytes_draft msg2.sh_protocol_version in
      let sidB2 = match msg2.sh_sessionID with
      | Some sid -> lemma_repr_bytes_values (length sid); vlbytes 1 sid
      | _ -> empty_bytes in
      let csB2 = cipherSuiteBytes msg2.sh_cipher_suite in
      let cmB2 =  match msg2.sh_compression with
      | Some compression -> compressionBytes compression
      | _ -> empty_bytes in
      let extB2:bytes = match msg2.sh_extensions with
      | Some ext -> extensionsBytes Server ext
      | None -> empty_bytes in
      let data2:bytes = match msg2.sh_protocol_version with
      | TLS_1p3 -> verB2 @| (msg2.sh_server_random @| (csB2 @| extB2))
      | _       -> verB2 @| (msg2.sh_server_random @| (sidB2 @| (csB2 @| (cmB2 @| extB2)))) in
      lemma_repr_bytes_values (length data2);
      messageBytes_is_injective HT_server_hello data1 HT_server_hello data2;
      cut(Seq.equal data1 data2);
      let s1 = split data1 2 in
      let s2 = split data2 2 in
      cut(Seq.equal verB1 (fst s1) /\ Seq.equal verB2 (fst s2));
      lemma_append_inj verB1 (snd s1) verB2 (snd s2);
      versionBytes_is_injective msg1.sh_protocol_version msg2.sh_protocol_version;
      cut(msg1.sh_protocol_version = msg2.sh_protocol_version);
      if msg1.sh_protocol_version = TLS_1p3 then (
	cut (Seq.equal (snd s1) (snd s2));
	cut (Seq.equal (snd s1) (msg1.sh_server_random @| (csB1 @| extB1)));
	cut (Seq.equal (snd s2) (msg2.sh_server_random @| (csB2 @| extB2)));
	cut (length msg1.sh_server_random = length msg2.sh_server_random);
	lemma_append_inj msg1.sh_server_random (csB1 @| extB1) msg2.sh_server_random (csB2 @| extB2);
	assert(msg1.sh_server_random = msg2.sh_server_random);
	let l1 = (csB1 @| extB1) in
	let l2 = (csB2 @| extB2) in
	cut(length csB1 >= 2 /\ length csB2 >= 2);
	cut(Seq.index csB1 0 = Seq.index l1 0 /\ Seq.index csB1 1 = Seq.index l1 1);
	cut(Seq.index csB2 0 = Seq.index l2 0 /\ Seq.index csB2 1 = Seq.index l2 1);
	cut(length (cipherSuiteBytes msg1.sh_cipher_suite) = length (cipherSuiteBytes msg2.sh_cipher_suite));
	lemma_append_inj csB1 extB1 csB2 extB2;
	cipherSuiteBytes_is_injective msg1.sh_cipher_suite msg2.sh_cipher_suite;
	optionExtensionsBytes_is_injective Server msg1.sh_extensions msg2.sh_extensions;
	())
      else (
	cut (Seq.equal (snd s1) (snd s2));
	cut (Seq.equal (snd s1) (msg1.sh_server_random @| (sidB1 @| (csB1 @| (cmB1 @| extB1)))));
	cut (Seq.equal (snd s2) (msg2.sh_server_random @| (sidB2 @| (csB2 @| (cmB2 @| extB2)))));
	cut (length msg1.sh_server_random = length msg2.sh_server_random);
	lemma_append_inj msg1.sh_server_random (sidB1 @| (csB1 @| (cmB1 @| extB1)))
			 msg2.sh_server_random (sidB2 @| (csB2 @| (cmB2 @| extB2)));
	let l1 = (sidB1 @| (csB1 @| (cmB1 @| extB1))) in
	let l2 = (sidB2 @| (csB2 @| (cmB2 @| extB2))) in
	cut(length sidB1 >= 1);
	cut(length sidB2 >= 1);
	cut(Seq.equal l1 l2);
	cut(Seq.index sidB1 0 = Seq.index l1 0 /\ Seq.index sidB2 0 = Seq.index l2 0);
	cut(Seq.index sidB1 0 = Seq.index sidB2 0);
	vlbytes_length_lemma 1 (Some?.v msg1.sh_sessionID) (Some?.v msg2.sh_sessionID);
	cut (length sidB1 = length sidB2);
	lemma_append_inj sidB1 (csB1 @| (cmB1 @| extB1)) sidB2 (csB2 @| (cmB2 @| extB2));
	cut(length csB1 >= 2 /\ length csB2 >= 2);
	let l1 = (csB1 @| (cmB1 @| extB1)) in
	let l2 = (csB2 @| (cmB2 @| extB2)) in
	cut(Seq.index csB1 0 = Seq.index l1 0 /\ Seq.index csB1 1 = Seq.index l1 1);
	cut(Seq.index csB2 0 = Seq.index l2 0 /\ Seq.index csB2 1 = Seq.index l2 1);
	cut(length (cipherSuiteBytes msg1.sh_cipher_suite) = length (cipherSuiteBytes msg2.sh_cipher_suite));
	lemma_append_inj csB1 (cmB1 @| extB1) csB2 (cmB2 @| extB2);
	cut (length cmB1 = length cmB2);
	lemma_append_inj cmB1 extB1 cmB2 extB2;
	cipherSuiteBytes_is_injective msg1.sh_cipher_suite msg2.sh_cipher_suite;
	optionExtensionsBytes_is_injective Server msg1.sh_extensions msg2.sh_extensions;
	cut(msg1.sh_protocol_version = msg2.sh_protocol_version);
	cut(msg1.sh_server_random = msg2.sh_server_random);
	cut(Seq.equal sidB1 sidB2);
	lemma_vlbytes_inj 1 (Some?.v msg1.sh_sessionID) (Some?.v msg2.sh_sessionID);
	()
      )
    end

#reset-options
//#set-options "--lax"

(* JK: should return a valid_sh to match the serialization function *)
(* JK: same as parseClientHello, weakening spec to get verification *)
val parseServerHello: data:bytes{repr_bytes(length data) <= 3}
  -> Tot (result (x:valid_sh))
(* val parseServerHello: data:bytes{repr_bytes(length data) <= 3}   *)
(*   -> Tot (result (x:sh{Seq.equal (serverHelloBytes x) (messageBytes HT_server_hello data)})) *)
let parseServerHello data =
  if length data < 34 then
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  else
    let (serverVerBytes,serverRandomBytes,data) = split2 data 2 32 in
    match parseVersion_draft serverVerBytes with
    | Error z -> Error z
    | Correct serverVer ->
      (match serverVer with
       | TLS_1p3 ->
 	 if length data >= 2 then
	   let (csBytes, data) = split data 2 in
	   (match parseCipherSuite csBytes with
	    | Error z -> Error z
	    | Correct cs ->
	      (match parseOptExtensions Server data with
	       | Error z -> Error z
	       | Correct exts ->
		 if (match exts with
		     | None -> false // JK: check how to handle the no extension case (empty variable
				    // length vector according to the spec
		     | Some l -> List.Tot.length l < 256)
		 then
		   let exts = coercion_helper exts in
		   correct ({
		     sh_protocol_version = serverVer;
		     sh_server_random = serverRandomBytes;
		     sh_sessionID = None;
		     sh_cipher_suite = cs;
		     sh_compression = None;
		     sh_extensions = exts})
		 else
 		   Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")))
	else
	  Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
       | _ ->
         (
	   if length data >= 1 then
	   match vlsplit 1 data with
          | Error z -> Error z
          | Correct (sid,data) ->
            if length sid <= 32 then
              if length data >= 3 then
                let (csBytes,cmBytes,data) = split2 data 2 1 in
                (match parseCipherSuite csBytes with
	         | Error z -> Error z
	         | Correct cs ->
    		   let cm = parseCompression cmBytes in
		   (match cm with
		    | UnknownCompression _ ->
		      Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "server selected a compression mode")
		    | NullCompression ->
		      (match parseOptExtensions Server data with
		       | Error z -> Error z
		       | Correct exts ->
			 if (match exts with
			     | None -> true
			     | Some l -> List.Tot.length l < 256)
			 then
			   let exts = coercion_helper exts in
		           correct ({
		             sh_protocol_version = serverVer;
		             sh_server_random = serverRandomBytes;
		             sh_sessionID = Some sid;
		             sh_cipher_suite = cs;
		             sh_compression = Some NullCompression;
		             sh_extensions = exts})
			 else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))))
	      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
	      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
            else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")))

val helloRequestBytes: b:lbytes 4{hs_msg_bytes HT_hello_request b}
let helloRequestBytes =
  lemma_repr_bytes_values 0;
  messageBytes HT_hello_request empty_bytes

val ccsBytes: lbytes 1
let ccsBytes = abyte 1z

val serverHelloDoneBytes: b:lbytes 4{hs_msg_bytes HT_server_hello_done b}
let serverHelloDoneBytes =
  lemma_repr_bytes_values 0;
  messageBytes HT_server_hello_done empty_bytes

(** A.4.2 Server Authentication and Key Exchange Messages *)

let valid_crt: Type0 = c:crt{length (Cert.certificateListBytes c.crt_chain) < 16777212}

val certificateBytes: protocolVersion ->  valid_crt -> Tot (b:bytes{hs_msg_bytes HT_certificate b})
let certificateBytes pv crt =
  let cb = Cert.certificateListBytes crt.crt_chain in
  lemma_repr_bytes_values (length cb);
  if (pv = TLS_1p3) then (
    lemma_repr_bytes_values (length empty_bytes);
    cut (length ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb)) < 16777216);
    lemma_repr_bytes_values (length ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb)));
    messageBytes HT_certificate ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb))
  )
  else (
    lemma_repr_bytes_values (length (vlbytes 3 cb));
    messageBytes HT_certificate (vlbytes 3 cb)
  )

val certificateBytes_is_injective: pv:protocolVersion -> c1:valid_crt -> c2:valid_crt ->
  Lemma (requires (True))
        (ensures (Seq.equal (certificateBytes pv c1) (certificateBytes pv c2) ==> c1 = c2))
let certificateBytes_is_injective pv c1 c2 =
  if certificateBytes pv c1 = certificateBytes pv c2 && pv = TLS_1p3 then (
    let cb1 = Cert.certificateListBytes c1.crt_chain in
    let cb2 = Cert.certificateListBytes c2.crt_chain in
    lemma_repr_bytes_values (length cb1);
    lemma_repr_bytes_values (length cb2);
    lemma_repr_bytes_values (length empty_bytes);
    lemma_vlbytes_len 1 empty_bytes;
    lemma_vlbytes_len 3 cb1;
    lemma_vlbytes_len 3 cb2;
    cut (length ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb1)) < 16777216);
    cut (length ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb2)) < 16777216);
    lemma_repr_bytes_values (length ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb1)));
    lemma_repr_bytes_values (length ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb2)));
    cut (Seq.equal (certificateBytes pv c1) (messageBytes HT_certificate ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb1))));
    cut (Seq.equal (certificateBytes pv c2) (messageBytes HT_certificate ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb2))));
    messageBytes_is_injective HT_certificate ((vlbytes 1 empty_bytes) @| vlbytes 3 cb1)
			      HT_certificate ((vlbytes 1 empty_bytes) @| vlbytes 3 cb2);
    lemma_append_inj (vlbytes 1 empty_bytes) (vlbytes 3 cb1) (vlbytes 1 empty_bytes) (vlbytes 3 cb2);
    lemma_vlbytes_inj 3 cb1 cb2;
    Cert.certificateListBytes_is_injective c1.crt_chain c2.crt_chain;
    ()
  )
  else if certificateBytes pv c1 = certificateBytes pv c2 then (
    let cb1 = Cert.certificateListBytes c1.crt_chain in
    let cb2 = Cert.certificateListBytes c2.crt_chain in
    lemma_repr_bytes_values (length cb1);
    lemma_repr_bytes_values (length cb2);
    lemma_vlbytes_len 3 cb1;
    lemma_vlbytes_len 3 cb2;
    cut (length (vlbytes 3 cb1) < 16777216);
    cut (length (vlbytes 3 cb2) < 16777216);
    lemma_repr_bytes_values (length (vlbytes 3 cb1));
    lemma_repr_bytes_values (length (vlbytes 3 cb2));
    cut (Seq.equal (certificateBytes pv c1) (messageBytes HT_certificate ((vlbytes 3 cb1))));
    cut (Seq.equal (certificateBytes pv c2) (messageBytes HT_certificate ((vlbytes 3 cb2))));
    messageBytes_is_injective HT_certificate (vlbytes 3 cb1)
			      HT_certificate (vlbytes 3 cb2);
    lemma_vlbytes_inj 3 cb1 cb2;
    Cert.certificateListBytes_is_injective c1.crt_chain c2.crt_chain;
    ()
  ) else ()

// SZ: I think this should be
// val parseCertificate: pv:protocolVersion -> data:bytes{3 <= length data /\ repr_bytes (length data - 3) <= 3}
//  -> Tot (result (r:crt{Seq.equal (certificateBytes r) (messageBytes HT_certificate data)}))
(* val parseCertificate: pv:protocolVersion -> data:bytes{repr_bytes (length data) <= 3}  *)
(*   -> Tot (result (r:valid_crt{Seq.equal (certificateBytes pv r) (messageBytes HT_certificate data)})) *)
val parseCertificate: pv:protocolVersion -> data:bytes{repr_bytes (length data) <= 3}
  -> Tot (result (r:valid_crt))
let parseCertificate pv data =
    let data = (
      if (pv = TLS_1p3) then (
	if length data >= 1 then Correct (snd (split data 1)) else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
      else Correct data
      ) in (* TODO: check that the header byte is 0x00 *)
    match data with
    | Correct data -> (
      if length data >= 3 then
        match vlparse 3 data with
        | Error z -> let (x,y) = z in Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ y)
	| Correct (certList) ->
	    (match Cert.parseCertificateList certList with
	    | Correct(l) ->
		if length certList < 16777212 then (
		  Cert.lemma_parseCertificateList_length certList;
		  Correct ({crt_chain = l})
		 )
		else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
            | Error z -> let (x,y) = z in Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ y))
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    )
   | Error z -> Error z

(* JK: TODO: rewrite taking the protocol version as an extra parameter, otherwise not injective *)
val certificateRequestBytes: cr -> Tot (b:bytes{hs_msg_bytes HT_certificate_request b})
let certificateRequestBytes cr =
    let ctb = certificateTypeListBytes cr.cr_cert_types in
    lemma_repr_bytes_values (length ctb);
    let ctB = vlbytes 1 ctb in
    let saB = match cr.cr_sig_hash_algs with
              | None -> empty_bytes
              | Some sal -> sigHashAlgsBytes sal in
    let dnb = distinguishedNameListBytes cr.cr_distinguished_names in
    lemma_repr_bytes_values (length dnb);
    let dnB = vlbytes 2 dnb in
    let data = ctB @| saB @| dnB in
    lemma_repr_bytes_values (length data);
    messageBytes HT_certificate_request data

val certificateTypeListBytes_is_injective: ctl1:list certType -> ctl2:list certType ->
  Lemma (requires (True))
	(ensures  (Seq.equal (certificateTypeListBytes ctl1) (certificateTypeListBytes ctl2) ==> ctl1 = ctl2))
let rec certificateTypeListBytes_is_injective ctl1 ctl2 =
  match ctl1, ctl2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if certificateTypeListBytes ctl1 = certificateTypeListBytes ctl2 then (
      cut (Seq.equal (certTypeBytes hd @| certificateTypeListBytes tl) (certTypeBytes hd' @| certificateTypeListBytes tl'));
      lemma_append_inj (certTypeBytes hd) (certificateTypeListBytes tl) (certTypeBytes hd') (certificateTypeListBytes tl');
      cut(hd = hd');
      certificateTypeListBytes_is_injective tl tl'
    )
  | _, _ -> ()

#reset-options

let lemma_distinguishedNameListBytes_def (n:list dn{Cons? n /\ repr_bytes (length (utf8 (Cons?.hd n))) <= 2}) : Lemma
  (distinguishedNameListBytes n = (vlbytes 2 (utf8 (Cons?.hd n)) @| distinguishedNameListBytes (Cons?.tl n))) = ()

let lemma_distinguishedNameListBytes_def2 (n:list dn{Nil? n}) : Lemma (distinguishedNameListBytes n = empty_bytes) = ()

(* TODO: port to Platform.Bytes *)
assume val utf8_is_injective: s:string -> s':string ->
  Lemma (requires (True))
	(ensures (Seq.equal (utf8 s) (utf8 s') ==> s = s'))

val distinguishedNameListBytes_is_injective: n1:list dn -> n2:list dn ->
  Lemma (requires (True))
	(ensures (Seq.equal (distinguishedNameListBytes n1) (distinguishedNameListBytes n2) ==> n1 = n2))
let rec distinguishedNameListBytes_is_injective n1 n2 =
  match n1, n2 with
  | [],[] -> ()
  | hd::tl, hd'::tl' ->
      let payload1 = distinguishedNameListBytes n1 in
      let payload2 = distinguishedNameListBytes n2 in
      if payload1 = payload2 then (
	lemma_repr_bytes_values (length (utf8 hd'));
	lemma_repr_bytes_values (length (utf8 hd));
	lemma_distinguishedNameListBytes_def n1;
	lemma_distinguishedNameListBytes_def n2;
	cut (forall b b'. {:pattern (b@|b')} (b@|b') = Seq.append b b');
	Seq.lemma_eq_refl payload1 payload2;
	cut (Seq.equal ((vlbytes 2 (utf8 hd)) @| (distinguishedNameListBytes tl))
		       ((vlbytes 2 (utf8 hd')) @| (distinguishedNameListBytes tl')));
	cut (Seq.equal (Seq.append (vlbytes 2 (utf8 hd)) (distinguishedNameListBytes tl))
		       (Seq.append (vlbytes 2 (utf8 hd')) (distinguishedNameListBytes tl')));
        cut (Seq.index (vlbytes 2 (utf8 hd)) 0 = Seq.index payload1 0);
        cut (Seq.index (vlbytes 2 (utf8 hd)) 1 = Seq.index payload1 1);
        cut (Seq.index (vlbytes 2 (utf8 hd')) 0 = Seq.index payload2 0);
        cut (Seq.index (vlbytes 2 (utf8 hd')) 1 = Seq.index payload2 1);
	cut (Seq.index payload1 0 = Seq.index payload2 0);
        cut (Seq.index payload1 1 = Seq.index payload2 1);
	vlbytes_length_lemma 2 (utf8 hd) (utf8 hd');
	lemma_append_inj (vlbytes 2 (utf8 hd)) (distinguishedNameListBytes tl) (vlbytes 2 (utf8 hd')) (distinguishedNameListBytes tl');
	distinguishedNameListBytes_is_injective tl tl';
	lemma_vlbytes_inj 2 (utf8 hd) (utf8 hd');
	utf8_is_injective hd hd'
      )
  | [],hd::tl -> (
      lemma_repr_bytes_values (length (utf8 hd));
      lemma_distinguishedNameListBytes_def n2;
      lemma_distinguishedNameListBytes_def2 n1;
      cut (forall b b'. {:pattern (b@|b')} (b@|b') = Seq.append b b');
      cut (length (distinguishedNameListBytes n2) >= 2);
      cut (length (distinguishedNameListBytes n1) = 0)
      )
  | hd::tl,[] -> (
      lemma_repr_bytes_values (length (utf8 hd));
      lemma_distinguishedNameListBytes_def n1;
      lemma_distinguishedNameListBytes_def2 n2;
      cut (forall b b'. {:pattern (b@|b')} (b@|b') = Seq.append b b');
      cut (length (distinguishedNameListBytes n1) >= 2);
      cut (length (distinguishedNameListBytes n2) = 0)
      )

//#set-options "--lax"

val certificateRequestBytes_is_injective: c1:cr -> c2:cr ->
  Lemma (requires (True))
	(ensures (Seq.equal (certificateRequestBytes c1) (certificateRequestBytes c2) ==> c1 = c2))
let certificateRequestBytes_is_injective c1 c2 =
  admit(); // JK: TODO
  if certificateRequestBytes c1 = certificateRequestBytes c2 then (
    let ctb1 = certificateTypeListBytes c1.cr_cert_types in
    lemma_repr_bytes_values (length ctb1);
    let ctB1 = vlbytes 1 ctb1 in
    let saB1 = match c1.cr_sig_hash_algs with
              | None -> empty_bytes
              | Some sal -> sigHashAlgsBytes sal in
    let dnb1 = distinguishedNameListBytes c1.cr_distinguished_names in
    lemma_repr_bytes_values (length dnb1);
    let dnB1 = vlbytes 2 dnb1 in
    let data1 = ctB1 @| saB1 @| dnB1 in
    let ctb2 = certificateTypeListBytes c2.cr_cert_types in
    lemma_repr_bytes_values (length ctb2);
    let ctB2 = vlbytes 1 ctb2 in
    let saB2 = match c2.cr_sig_hash_algs with
              | None -> empty_bytes
              | Some sal -> sigHashAlgsBytes sal in
    let dnb2 = distinguishedNameListBytes c2.cr_distinguished_names in
    lemma_repr_bytes_values (length dnb2);
    let dnB2 = vlbytes 2 dnb2 in
    let data2 = ctB2 @| saB2 @| dnB2 in
    lemma_repr_bytes_values (length data2);
    lemma_repr_bytes_values (length data1);
    messageBytes_is_injective HT_certificate_request data1 HT_certificate_request data2;
    assume (Seq.equal (Seq.slice data1 0 1) (Seq.slice data2 0 1));
    assume (Seq.equal (Seq.slice data1 0 1) (Seq.slice ctB1 0 1));
    assume (Seq.equal (Seq.slice data2 0 1) (Seq.slice ctB2 0 1));
    vlbytes_length_lemma 1 ctb1 ctb2;
    lemma_append_inj ctB1 (saB1 @| dnB1) ctB2 (saB2 @| dnB2)
  )

val parseCertificateRequest: pv:protocolVersion -> data:bytes{repr_bytes(length data) <= 3} ->
                             Tot (result cr)
let parseCertificateRequest version data =
    if length data >= 1 then
        match vlsplit 1 data with
        | Error(z) -> Error(z)
        | Correct (res) ->
        let (certTypeListBytes,data) = res in
        let certTypeList = parseCertificateTypeList certTypeListBytes in
	if List.Tot.length certTypeList < 256 then (
        if length data >= 2 then
            match version with
            | TLS_1p2 ->
            (match vlsplit 2 data with
            | Error(z) -> Error(z)
            | Correct  (x,y) ->
            if length y >= 2 then begin
	       lemma_repr_bytes_values (length x);
               match parseSigHashAlgs (vlbytes 2 x) with
               | Error(z) -> Error(z)
               | Correct (sigAlgs) ->
	       match vlparse 2 y with
	       | Error(z) -> Error(z)
	       | Correct(y) ->
               match parseDistinguishedNameList y [] with
               | Error(z) -> Error(z)
               | Correct (distNamesList) ->
		 if List.Tot.length distNamesList < 128 && List.Tot.length sigAlgs < 256 then
                 correct (
                 {cr_cert_types = certTypeList;
                  cr_sig_hash_algs = Some sigAlgs;
                  cr_distinguished_names = distNamesList})
		 else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
	    end
            else
               Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
            | _ ->
               match parseDistinguishedNameList data [] with
               | Error(z) -> Error(z)
               | Correct (distNamesList) ->
		 if List.Tot.length distNamesList < 128 then
                 correct (
                 {cr_cert_types = certTypeList;
                  cr_sig_hash_algs = None;
                  cr_distinguished_names = distNamesList})
		 else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "") )
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let mk_certificateRequestBytes sign cs version =
    certificateRequestBytes (
    {cr_cert_types = defaultCertTypes sign cs;
     cr_sig_hash_algs = (match version with
                         | TLS_1p2 -> Some (default_sigHashAlg version cs)
                         | _ -> None);
     cr_distinguished_names = []})

(** A.4.3 Client Authentication and Key Exchange Messages *)

open CoreCrypto
val kex_c_of_dh_key: #g:CommonDH.group -> CommonDH.pre_share g -> Tot kex_c
let kex_c_of_dh_key #g kex =
  match g with
  | CommonDH.FFDH g' -> KEX_C_DHE (CommonDH.serialize_raw #g kex)
  | CommonDH.ECDH g' -> KEX_C_ECDHE (CommonDH.serialize_raw #g kex)

(* JK: TODO: add the kex as an extra parameter, otherwise not injective *)
val clientKeyExchangeBytes: protocolVersion -> cke -> Tot (b:bytes{hs_msg_bytes HT_client_key_exchange b})
let clientKeyExchangeBytes pv cke =
  let kexB =
    match pv,cke.cke_kex_c with
    | _,KEX_C_DHE b -> (
      lemma_repr_bytes_values (length b);
      lemma_vlbytes_len 2 b;
      lemma_repr_bytes_values (length (vlbytes 2 b));
      vlbytes 2 b )
    | _,KEX_C_ECDHE b -> (
      lemma_repr_bytes_values (length b);
      lemma_vlbytes_len 1 b;
      lemma_repr_bytes_values (length (vlbytes 1 b));
      vlbytes 1 b)
    | SSL_3p0,KEX_C_RSA(encpms) -> (lemma_repr_bytes_values (length encpms); encpms)
    | _,KEX_C_RSA(encpms) -> (
      lemma_repr_bytes_values (length encpms);
      lemma_vlbytes_len 2 encpms;
      lemma_repr_bytes_values (length (vlbytes 2 encpms));
      vlbytes 2 encpms )
    | _,KEX_C_DH -> (
      lemma_repr_bytes_values (length empty_bytes);
      empty_bytes) in
  lemma_repr_bytes_values (length kexB);
  messageBytes HT_client_key_exchange kexB

val clientKeyExchangeBytes_is_injective: pv:protocolVersion -> cke1:cke -> cke2:cke ->
  Lemma (requires (True))
	(ensures (Seq.equal (clientKeyExchangeBytes pv cke1) (clientKeyExchangeBytes pv cke2) ==> cke1 = cke2))
let clientKeyExchangeBytes_is_injective pv cke1 cke2 =
  admit(); // JK: TODO, see comment above
  if clientKeyExchangeBytes pv cke1 = clientKeyExchangeBytes pv cke2 && pv = SSL_3p0 then (
    ()
  )
  else if clientKeyExchangeBytes pv cke1 = clientKeyExchangeBytes pv cke2 then (
    ()
  ) else ()

(* val parseClientKeyExchange: p:protocolVersion -> kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} ->  *)
(*     Tot (result (cke:cke{Seq.equal (clientKeyExchangeBytes p cke) (messageBytes HT_client_key_exchange b)})) *)
val parseClientKeyExchange: p:protocolVersion -> kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} ->
    Tot (result cke)
let parseClientKeyExchange pv kex data =
  match pv,kex with
  | _,Kex_DH ->
      if length data = 0
      then Correct({cke_kex_c = KEX_C_DH})
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | _,Kex_DHE ->
      if length data >= 2
      then (match vlparse 2 data with
           | Error(z) -> Error(z)
           | Correct(y) -> (lemma_repr_bytes_values (length y); Correct({cke_kex_c = KEX_C_DHE y})))
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | _,Kex_ECDHE ->
      if length data >= 1
      then (match vlparse 1 data with
           | Error(z) -> Error(z)
           | Correct(y) -> (lemma_repr_bytes_values (length y); Correct({cke_kex_c = KEX_C_ECDHE y})))
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | SSL_3p0,Kex_RSA ->
      if length data < 4096 then
         (lemma_repr_bytes_values (length data); Correct({cke_kex_c = KEX_C_RSA data}))
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | _,Kex_RSA  ->
        if length data >= 2 then
            match vlparse 2 data with
            | Correct (encPMS) ->
	      if length encPMS < 4096 then (lemma_repr_bytes_values (length encPMS); correct({cke_kex_c = KEX_C_RSA encPMS}))
	      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
            | Error(z) -> Error(z)
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

(* ServerKeyExchange *)

open CoreCrypto

val kex_s_to_bytes: kex_s -> Tot (b:bytes{length b < 16777216 - 65536}) // JK: required for serverKeyExxchangeBytes
let kex_s_to_bytes kex =
  admit(); // JK: TODO
  match kex with
  | KEX_S_DHE (|g, k|) -> CommonDH.serialize #g k
  | KEX_S_RSA pk -> (*TODO: Ephemeral RSA*) empty_bytes

(* JK: TODO, or rewrite the functions altogether *)
assume val commonDH_serialize_is_injective: #g:CommonDH.group -> k1:CommonDH.pre_share g -> k2:CommonDH.pre_share g ->
  Lemma (requires (True))
	(ensures (Seq.equal (CommonDH.serialize k1) (CommonDH.serialize k2) ==> k1 = k2))

(* JK: TODO: missing the proper serialization for RSA so not injective for now *)
(* Actually false for now *)
assume val kex_s_to_bytes_is_injective: k1:kex_s -> k2:kex_s ->
  Lemma (requires (True))
	(ensures (Seq.equal (kex_s_to_bytes k1) (kex_s_to_bytes k2) ==> k1 = k2))

val serverKeyExchangeBytes: ske -> Tot (b:bytes{hs_msg_bytes HT_server_key_exchange b})
let serverKeyExchangeBytes ske =
    let kexB = kex_s_to_bytes ske.ske_kex_s in
    let payload = kexB @| ske.ske_sig in
    lemma_repr_bytes_values (length payload);
    messageBytes HT_server_key_exchange payload

(* JK: TODO, currently not injective and missing an extra argument compared to the
   parsing function: the kex algorithm *)
assume val serverKeyExchangeBytes_is_injective: s1:ske -> s2:ske ->
  Lemma (requires (True))
	(ensures (Seq.equal (serverKeyExchangeBytes s1) (serverKeyExchangeBytes s2) ==> s1 = s2))
(* let serverKeyExchangeBytes_is_injective s1 s2 =  *)
  (* if serverKeyExchangeBytes s1 = serverKeyExchangeBytes s2 then ( *)
  (*   let kexB1 = kex_s_to_bytes s1.ske_kex_s in *)
  (*   let payload1 = kexB1 @| s1.ske_sig in *)
  (*   lemma_repr_bytes_values (length payload1); *)
  (*   let kexB2 = kex_s_to_bytes s2.ske_kex_s in *)
  (*   let payload2 = kexB2 @| s2.ske_sig in *)
  (*   lemma_repr_bytes_values (length payload2); *)
  (*   messageBytes_is_injective HT_server_key_exchange payload1 HT_server_key_exchange payload2; *)
  (*   kex_s_to_bytes_is_injective s1.ske_kex_s s2.ske_kex_s; *)
  (* ) *)

(* val parseServerKeyExchange: kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} ->  *)
(*     Tot (result (s:ske{Seq.equal (serverKeyExchangeBytes s) (messageBytes HT_server_key_exchange b)})) *)
val parseServerKeyExchange: kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} -> Tot (result ske)
let parseServerKeyExchange kex payload : result ske =
    match kex with
    | Kex_DH -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | Kex_RSA -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | Kex_DHE ->
       (match CommonDH.parse_partial false payload with
	| Correct (k,sign) ->
	  if length sign < 65536 then
          Correct ({ske_kex_s = KEX_S_DHE k;
                    ske_sig = sign})
	  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        | Error z -> Error z)
    | Kex_ECDHE ->
       (match CommonDH.parse_partial true payload with
	| Correct (k,sign) ->
	  if length sign < 65536 then
          Correct ({ske_kex_s = KEX_S_DHE k;
                    ske_sig = sign})
	  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        | Error z -> Error z)

(* Certificate Verify *)
val certificateVerifyBytes: cv -> Tot (b:bytes{hs_msg_bytes HT_certificate_verify b})
let certificateVerifyBytes cv =
    lemma_repr_bytes_values (length cv.cv_sig);
    messageBytes HT_certificate_verify cv.cv_sig

val certificateVerifyBytes_is_injective: c1:cv -> c2:cv ->
  Lemma (requires (True))
	(ensures (Seq.equal (certificateVerifyBytes c1) (certificateVerifyBytes c2) ==> c1 = c2))
let certificateVerifyBytes_is_injective c1 c2 =
  if certificateVerifyBytes c1 = certificateVerifyBytes c2 then (
    lemma_repr_bytes_values (length c1.cv_sig);
    lemma_repr_bytes_values (length c2.cv_sig);
    messageBytes_is_injective HT_certificate_verify c1.cv_sig HT_certificate_verify c2.cv_sig
  )

(* JK: FIXME: information on data's length is redundant, but simpler for now to have both
   in the spec *)
val parseCertificateVerify: data:bytes{length data < 65536 /\ repr_bytes(length data) <= 3} ->
    Tot (result (c:cv{Seq.equal (certificateVerifyBytes c) (messageBytes HT_certificate_verify data)}))
let parseCertificateVerify data =
    correct ({cv_sig = data})

val finishedBytes: fin -> Tot (b:bytes{hs_msg_bytes HT_finished b})
let finishedBytes fin =
    lemma_repr_bytes_values (length fin.fin_vd);
    messageBytes HT_finished fin.fin_vd

val finishedBytes_is_injective: f1:fin -> f2:fin ->
  Lemma (requires (True))
	(ensures (Seq.equal (finishedBytes f1) (finishedBytes f2) ==> f1 = f2))
let finishedBytes_is_injective f1 f2 =
  if finishedBytes f1 = finishedBytes f2 then (
    lemma_repr_bytes_values (length f1.fin_vd);
    lemma_repr_bytes_values (length f2.fin_vd);
    messageBytes_is_injective HT_finished f1.fin_vd HT_finished f2.fin_vd
  )

#reset-options
//#set-options "--lax"

val parseFinished: data:bytes{length data < 65536 /\ repr_bytes(length data)<=3} ->
    Tot (result(f:fin{Seq.equal (finishedBytes f) (messageBytes HT_finished data)}))
let parseFinished data =
    Correct ({fin_vd = data})

(* Session ticket *)
val sessionTicketBytes: sticket -> Tot (b:bytes{hs_msg_bytes HT_session_ticket b})
let sessionTicketBytes sticket =
    let payload = sticket.sticket_ticket_lifetime_hint @| sticket.sticket_ticket in
    lemma_repr_bytes_values (length payload);
    messageBytes HT_session_ticket payload

val sessionTicketBytes_is_injective: s1:sticket -> s2:sticket ->
  Lemma (requires (True))
	(ensures (Seq.equal (sessionTicketBytes s1) (sessionTicketBytes s2) ==> s1 = s2))
let sessionTicketBytes_is_injective s1 s2 =
  if sessionTicketBytes s1 = sessionTicketBytes s2 then (
    let payload1 = s1.sticket_ticket_lifetime_hint @| s1.sticket_ticket in
    let payload2 = s2.sticket_ticket_lifetime_hint @| s2.sticket_ticket in
    lemma_repr_bytes_values (length payload1);
    lemma_repr_bytes_values (length payload2);
    messageBytes_is_injective HT_session_ticket payload1 HT_session_ticket payload2;
    lemma_append_inj s1.sticket_ticket_lifetime_hint s1.sticket_ticket s2.sticket_ticket_lifetime_hint s2.sticket_ticket
  )

val parseSessionTicket: b:bytes{repr_bytes(length b) <= 3} ->
    Tot (result (s:sticket{Seq.equal (sessionTicketBytes s) (messageBytes HT_session_ticket b)}))
let parseSessionTicket payload  =
  if length payload >= 4 && length payload < 65542 then
    let (lifetime_hint, ticket) = split payload 4 in
    Correct({sticket_ticket_lifetime_hint = lifetime_hint; sticket_ticket = ticket})
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Inappropriate size in received session ticket")

(* Hello retry request *)
val helloRetryRequestBytes: hrr -> Tot (b:bytes{hs_msg_bytes HT_hello_retry_request b})
let helloRetryRequestBytes hrr =
  let pv = versionBytes hrr.hrr_protocol_version in
  let cs_bytes = cipherSuiteBytes hrr.hrr_cipher_suite in
  let ng = namedGroupBytes hrr.hrr_named_group in
  let exts = extensionsBytes Server hrr.hrr_extensions in
  let data = pv @| (cs_bytes @| (ng @| exts)) in
  lemma_repr_bytes_values (length data);
  messageBytes HT_hello_retry_request data

val namedGroupBytes_is_injective: n1:namedGroup -> n2:namedGroup ->
  Lemma (requires (True))
	(ensures (Seq.equal (namedGroupBytes n1) (namedGroupBytes n2) ==> n1 = n2))
let namedGroupBytes_is_injective n1 n2 =
  if namedGroupBytes n1 = namedGroupBytes n2 then pinverse_namedGroup (namedGroupBytes n1)

val helloRetryRequestBytes_is_injective: h1:hrr -> h2:hrr ->
  Lemma (requires (True))
	(ensures (Seq.equal (helloRetryRequestBytes h1) (helloRetryRequestBytes h2) ==> h1 == h2))
let helloRetryRequestBytes_is_injective h1 h2 =
  if helloRetryRequestBytes h1 = helloRetryRequestBytes h2 then (
    let pv1 = versionBytes h1.hrr_protocol_version in
    let cs_bytes1 = cipherSuiteBytes h1.hrr_cipher_suite in
    let ng1 = namedGroupBytes h1.hrr_named_group in
    let exts1 = extensionsBytes Server h1.hrr_extensions in
    let pv2 = versionBytes h2.hrr_protocol_version in
    let cs_bytes2 = cipherSuiteBytes h2.hrr_cipher_suite in
    let ng2 = namedGroupBytes h2.hrr_named_group in
    let exts2 = extensionsBytes Server h2.hrr_extensions in
    let data1 = pv1 @| (cs_bytes1 @| (ng1 @| exts1)) in
    lemma_repr_bytes_values (length data1);
    let data2 = pv2 @| (cs_bytes2 @| (ng2 @| exts2)) in
    lemma_repr_bytes_values (length data2);
    messageBytes_is_injective HT_hello_retry_request data1 HT_hello_retry_request data2;
    lemma_append_inj pv1 (cs_bytes1 @| (ng1 @| exts1)) pv2  (cs_bytes2 @| (ng2 @| exts2));
    lemma_append_inj cs_bytes1 (ng1 @| exts1) cs_bytes2 (ng2 @| exts2);
    lemma_append_inj ng1 exts1 ng2 exts2;
    versionBytes_is_injective h1.hrr_protocol_version h2.hrr_protocol_version;
    cipherSuiteBytes_is_injective h1.hrr_cipher_suite h2.hrr_cipher_suite;
    namedGroupBytes_is_injective h1.hrr_named_group h2.hrr_named_group;
    extensionsBytes_is_injective Server h1.hrr_extensions h2.hrr_extensions
  )

(* TODO: inversion lemmas *)
val parseHelloRetryRequest: bytes -> Tot (result hrr)
let parseHelloRetryRequest b =
  if length b >= 4 then
    let pv, cs, data = split2 b 2 2 in
    (match TLSConstants.parseVersion pv with
    | Correct(pv) ->
      (match parseCipherSuite cs with
      | Correct(cs) ->
	if length data >= 2 then
	  let ng, data = split data 2 in
	  (match parseNamedGroup ng with
	  | Correct(ng) ->
	    (match parseExtensions Server data with
	    | Correct(exts) ->
	      if List.Tot.length exts < 256 then
	      Correct ({ hrr_protocol_version = pv;
			hrr_cipher_suite = cs;
			hrr_named_group = ng;
			hrr_extensions = exts })
		else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong hello retry request format")
	    | Error(z) -> Error(z))
	  | Error(z) -> Error(z))
	else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong hello retry request format")
      | Error(z) -> Error(z))
    | Error(z) -> Error(z))
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong hello retry request format")

(* Encrypted_extensions *)
let valid_ee : Type0 = msg:ee{repr_bytes (length (extensionsBytes Server msg.ee_extensions)) <= 3}

val encryptedExtensionsBytes: e:valid_ee -> Tot (b:bytes{hs_msg_bytes HT_encrypted_extensions b})
let encryptedExtensionsBytes ee =
    let payload = extensionsBytes Server ee.ee_extensions in
    messageBytes HT_encrypted_extensions payload

val encryptedExtensionsBytes_is_injective: e1:valid_ee -> e2:valid_ee ->
  Lemma (requires (True))
	(ensures (Seq.equal (encryptedExtensionsBytes e1) (encryptedExtensionsBytes e2) ==> e1 == e2))
let encryptedExtensionsBytes_is_injective e1 e2 =
  let payload1 = extensionsBytes Server e1.ee_extensions in
  let payload2 = extensionsBytes Server e2.ee_extensions in
  messageBytes_is_injective HT_encrypted_extensions payload1 HT_encrypted_extensions payload2;
  extensionsBytes_is_injective Server e1.ee_extensions e2.ee_extensions

(* JK : TODO *)
assume val lemma_extensionsBytes_length: r:role -> b:bytes ->
  Lemma (requires (True))
	(ensures (Correct? (parseExtensions r b) ==> length (extensionsBytes r (Correct?._0 (parseExtensions r b))) = length b))

(* val parseEncryptedExtensions: b:bytes{repr_bytes(length b) <= 3} ->  *)
(*     Tot (result (s:valid_ee{Seq.equal (encryptedExtensionsBytes s) (messageBytes HT_encrypted_extensions b)})) *)
val parseEncryptedExtensions: b:bytes{repr_bytes(length b) <= 3} ->
    Tot (result valid_ee)
let parseEncryptedExtensions payload  =
  match parseExtensions Server payload with
  | Error(z) -> Error(z)
  | Correct(exts) -> if List.Tot.length exts < 256 then (
		       lemma_extensionsBytes_length Server payload;
		       Correct({ee_extensions = exts;})
		       )
		     else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "too many extensions")

(* Next protocol message *)
val nextProtocolBytes: np -> Tot (b:bytes{hs_msg_bytes HT_next_protocol b})
let nextProtocolBytes np =
  lemma_repr_bytes_values (length (np.np_selected_protocol));
  lemma_repr_bytes_values (length (np.np_padding));
  let selected_protocol = vlbytes 1 np.np_selected_protocol in
  let padding = vlbytes 1 np.np_padding in
  lemma_repr_bytes_values (length (selected_protocol @| padding));
  messageBytes HT_next_protocol (selected_protocol @| padding)

val nextProtocolBytes_is_injective: np1:np -> np2:np ->
  Lemma (requires (True))
	(ensures (Seq.equal (nextProtocolBytes np1) (nextProtocolBytes np2) ==> np1 = np2))
let nextProtocolBytes_is_injective np1 np2 =
  if nextProtocolBytes np1 = nextProtocolBytes np2 then (
    lemma_repr_bytes_values (length (np1.np_selected_protocol));
    lemma_repr_bytes_values (length (np1.np_padding));
    lemma_repr_bytes_values (length (np2.np_selected_protocol));
    lemma_repr_bytes_values (length (np2.np_padding));
    let selected_protocol1 = vlbytes 1 np1.np_selected_protocol in
    let padding1 = vlbytes 1 np1.np_padding in
    let selected_protocol2 = vlbytes 1 np2.np_selected_protocol in
    let padding2 = vlbytes 1 np2.np_padding in
    let data1 = (selected_protocol1 @| padding1) in
    let data2 = (selected_protocol2 @| padding2) in
    lemma_repr_bytes_values (length data1);
    lemma_repr_bytes_values (length data2);
    messageBytes_is_injective HT_next_protocol data1 HT_next_protocol data2;
    cut (Seq.equal (Seq.slice selected_protocol1 0 1) (Seq.slice data1 0 1));
    cut (Seq.equal (Seq.slice selected_protocol2 0 1) (Seq.slice data2 0 1));
    cut (Seq.equal (Seq.slice selected_protocol2 0 1) (Seq.slice selected_protocol1 0 1));
    vlbytes_length_lemma 1 np1.np_selected_protocol np2.np_selected_protocol;
    lemma_append_inj selected_protocol1 padding1 selected_protocol2 padding2;
    lemma_vlbytes_inj 1 np1.np_selected_protocol np2.np_selected_protocol;
    lemma_vlbytes_inj 1 np1.np_padding np2.np_padding
  )

(* val parseNextProtocol: b:bytes{repr_bytes (length b) <= 3} ->  *)
(*     Tot (result (s:np{Seq.equal (nextProtocolBytes s) (messageBytes HT_next_protocol b)})) *)
val parseNextProtocol: b:bytes{repr_bytes (length b) <= 3} ->Tot (result np)
let parseNextProtocol payload =
  if length payload >= 1 then
  match vlsplit 1 payload with
  | Error(z) -> Error(z)
  | Correct(selected_protocol, data) ->
  if length data >= 1 then
    match vlparse 1 data with
    | Error(z) -> Error(z)
    | Correct(padding) ->
	Correct( { np_selected_protocol = selected_protocol;
		   np_padding = padding;})
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let associated_to_pv (pv:option protocolVersion) (msg:hs_msg) : Type0  =
  (Certificate? msg \/ ClientKeyExchange? msg) ==> Some? pv

let valid_hs_msg: Type0 = msg:hs_msg{
  (EncryptedExtensions? msg ==> repr_bytes (length (extensionsBytes Server (EncryptedExtensions?._0 msg).ee_extensions)) <= 3)
  /\ (ServerHello? msg ==> (((ServerHello?._0 msg).sh_protocol_version = TLS_1p3 ==> (None? (ServerHello?._0 msg).sh_sessionID /\ None? (ServerHello?._0 msg).sh_compression)) /\ ((ServerHello?._0 msg).sh_protocol_version <> TLS_1p3 ==> (Some? (ServerHello?._0 msg).sh_sessionID /\ Some? (ServerHello?._0 msg).sh_compression))))
  /\ (Certificate? msg ==> length (Cert.certificateListBytes (Certificate?._0 msg).crt_chain) < 16777212)}

val handshakeMessageBytes: pv:option protocolVersion -> msg:valid_hs_msg{associated_to_pv pv msg}  -> Tot (b:bytes{exists (ht:handshakeType). hs_msg_bytes ht b})
let handshakeMessageBytes pvo hs =
    match hs,pvo with
    | ClientHello(ch),_-> clientHelloBytes ch
    | ServerHello(sh),_-> serverHelloBytes sh
    | Certificate(c),Some pv-> certificateBytes pv c
    | ServerKeyExchange(ske),_-> serverKeyExchangeBytes ske
    | ServerHelloDone,_-> serverHelloDoneBytes
    | ClientKeyExchange(cke),Some pv-> clientKeyExchangeBytes pv cke
    | Finished(f),_-> finishedBytes f
    | SessionTicket(t),_-> sessionTicketBytes t
    | EncryptedExtensions(e),_-> encryptedExtensionsBytes e
    | CertificateRequest(cr),_-> certificateRequestBytes cr
    | CertificateVerify(cv),_-> certificateVerifyBytes cv
    | HelloRequest,_-> helloRequestBytes
    | HelloRetryRequest(hrr),_-> helloRetryRequestBytes hrr
    (* | ServerConfiguration(sc),_-> serverConfigurationBytes sc *)
    | NextProtocol(n),_->  nextProtocolBytes n

val splitHandshakeMessage: b:bytes{exists (ht:handshakeType). hs_msg_bytes ht b} ->
  Tot (t:(handshakeType * bytes){repr_bytes (length (snd t)) <= 3 /\ b = (htBytes (fst t) @| (vlbytes 3 (snd t)))})
let splitHandshakeMessage b =
  let htbytes, payload = split b 1 in
  let lenbytes,data = split payload 3 in
  let ht = parseHt htbytes in
  assert(Correct? ht);
  match ht with
  | Correct ht ->
    inverse_ht ht;
    assert(Seq.equal b (messageBytes ht data));
    (ht, data)

#reset-options "--z3rlimit 100"
//#set-options "--lax"

val handshakeMessageBytes_is_injective: pv:option protocolVersion -> msg1:valid_hs_msg{associated_to_pv pv msg1} -> msg2:valid_hs_msg{associated_to_pv pv msg2} ->
  Lemma (requires (True))
	(ensures (Seq.equal (handshakeMessageBytes pv msg1) (handshakeMessageBytes pv msg2) ==> msg1 = msg2))
let handshakeMessageBytes_is_injective pv msg1 msg2 =
  if handshakeMessageBytes pv msg1 = handshakeMessageBytes pv msg2 then (
    let bytes1 = handshakeMessageBytes pv msg1 in
    let bytes2 = handshakeMessageBytes pv msg2 in
    let ht1,data1 = splitHandshakeMessage bytes1 in
    let ht2,data2 = splitHandshakeMessage bytes2 in
    messageBytes_is_injective ht1 data1 ht2 data2;
    assert(ht1 = ht2 /\ data1 = data2);
    match ht1 with
    | HT_client_hello -> clientHelloBytes_is_injective (ClientHello?._0 msg1) (ClientHello?._0 msg2)
    | HT_server_hello -> serverHelloBytes_is_injective (ServerHello?._0 msg1) (ServerHello?._0 msg2)
    | HT_certificate -> certificateBytes_is_injective (Some?.v pv) (Certificate?._0 msg1) (Certificate?._0 msg2)
    | HT_server_key_exchange -> serverKeyExchangeBytes_is_injective (ServerKeyExchange?._0 msg1) (ServerKeyExchange?._0 msg2)
    | HT_server_hello_done -> ()
    | HT_client_key_exchange -> clientKeyExchangeBytes_is_injective (Some?.v pv) (ClientKeyExchange?._0 msg1) (ClientKeyExchange?._0 msg2)
    | HT_finished -> finishedBytes_is_injective (Finished?._0 msg1) (Finished?._0 msg2)
    | HT_session_ticket -> sessionTicketBytes_is_injective (SessionTicket?._0 msg1) (SessionTicket?._0 msg2)
    | HT_encrypted_extensions -> encryptedExtensionsBytes_is_injective (EncryptedExtensions?._0 msg1) (EncryptedExtensions?._0 msg2)
    | HT_certificate_request -> certificateRequestBytes_is_injective (CertificateRequest?._0 msg1) (CertificateRequest?._0 msg2)
    | HT_certificate_verify -> certificateVerifyBytes_is_injective (CertificateVerify?._0 msg1) (CertificateVerify?._0 msg2)
    | HT_hello_request -> ()
    | HT_hello_retry_request -> helloRetryRequestBytes_is_injective (HelloRetryRequest?._0 msg1) (HelloRetryRequest?._0 msg2)
    (* | HT_server_configuration -> serverConfigurationBytes_is_injective (ServerConfiguration?._0 msg1) (ServerConfiguration?._0 msg2) *)
    | HT_next_protocol -> nextProtocolBytes_is_injective (NextProtocol?._0 msg1) (NextProtocol?._0 msg2)
  )

val handshakeMessagesBytes: pv:option protocolVersion -> list (msg:valid_hs_msg{associated_to_pv pv msg}) -> Tot bytes
let rec handshakeMessagesBytes pv hsl =
    match hsl with
    | [] -> empty_bytes
    | h::t -> (handshakeMessageBytes pv h) @| (handshakeMessagesBytes pv t)

#reset-options

let lemma_handshakeMessagesBytes_def (pv:option protocolVersion) (li:list (msg:valid_hs_msg{associated_to_pv pv msg}){Cons? li}) : Lemma (handshakeMessagesBytes pv li = ((handshakeMessageBytes pv (Cons?.hd li)) @| (handshakeMessagesBytes pv (Cons?.tl li)))) = ()

let lemma_handshakeMessagesBytes_def2 (pv:option protocolVersion) (li:list (msg:valid_hs_msg{associated_to_pv pv msg}){Nil? li}) : Lemma (handshakeMessagesBytes pv li = empty_bytes) = ()

val lemma_handshakeMessageBytes_aux: pv:option protocolVersion -> msg1:valid_hs_msg{associated_to_pv pv msg1} -> msg2:valid_hs_msg{associated_to_pv pv msg2} ->
  Lemma (requires (let b1 = handshakeMessageBytes pv msg1 in
		       let b2 = handshakeMessageBytes pv msg2 in
		       length b2 >= length b1
		       /\ Seq.equal b1 (Seq.slice b2 0 (length b1))))
	(ensures (Seq.equal (handshakeMessageBytes pv msg1) (handshakeMessageBytes pv msg2)))

#reset-options "--z3rlimit 50"
//#set-options "--lax"

let lemma_handshakeMessageBytes_aux pv msg1 msg2 =
  let payload1 = handshakeMessageBytes pv msg1 in
  let payload2 = handshakeMessageBytes pv msg2 in
  let ht1, data1 = splitHandshakeMessage payload1 in
  let ht2, data2 = splitHandshakeMessage payload2 in
  cut (payload1 = (htBytes ht1 @| vlbytes 3 data1));
  cut (payload2 = (htBytes ht2 @| vlbytes 3 data2));
  cut (length payload1 >= 4 /\ length payload2 >= 4);
  Seq.lemma_index_slice payload1 1 (length payload1) 0;
  Seq.lemma_index_slice payload1 1 (length payload1) 1;
  Seq.lemma_index_slice payload1 1 (length payload1) 2;
  Seq.lemma_index_slice payload2 1 (length payload2) 0;
  Seq.lemma_index_slice payload2 1 (length payload2) 1;
  Seq.lemma_index_slice payload2 1 (length payload2) 2;
  Seq.lemma_eq_intro (Seq.slice (vlbytes 3 data1) 0 3) (Seq.slice (vlbytes 3 data2) 0 3);
  vlbytes_length_lemma 3 data1 data2;
  cut (length (vlbytes 3 data1) = length (vlbytes 3 data2));
  cut (length payload1 = length payload2);
  Seq.lemma_eq_intro (Seq.slice payload2 0 (length payload1)) payload2;
  lemma_append_inj (htBytes ht1) (vlbytes 3 data1) (htBytes ht2) (vlbytes 3 data2)

#reset-options

let lemma_aux_1 (a:bytes) (b:bytes) (c:bytes) (d:bytes) : Lemma
  (requires (Seq.equal (a @| b) (c @| d)))
  (ensures ((length a >= length c ==> Seq.equal (Seq.slice a 0 (length c)) c)
	    /\ (length a < length c ==> Seq.equal (Seq.slice c 0 (length a)) a)))
 = if length a >= length c then (
     cut (Seq.equal (a @| b) (c @| d));
     cut (forall (i:nat). {:pattern (Seq.index (a@|b) i) \/ (Seq.index (c@|d) i)} i < length (a@|b) ==> Seq.index (a@|b) i = Seq.index (c@|d) i);
     cut (length a <= length (a@|b) /\ length c <= length (a@|b));
     ()
     )
   else (
     cut (Seq.equal (a @| b) (c @| d));
     cut (forall (i:nat). {:pattern (Seq.index (a@|b) i) \/ (Seq.index (c@|d) i)} i < length (a@|b) ==> Seq.index (a@|b) i = Seq.index (c@|d) i);
     cut (length a <= length (a@|b) /\ length c <= length (a@|b));
     ()
  )

let lemma_op_At_Bar_def (b:bytes) (b':bytes) : Lemma (requires (True)) (ensures ((b@|b') = Seq.append b b')) = ()

let lemma_handshakeMessageBytes_min_length (pv:option protocolVersion) (msg:valid_hs_msg{associated_to_pv pv msg}) : Lemma (length (handshakeMessageBytes pv msg) >= 4) = ()

let lemma_aux_2 (pv:option protocolVersion) (l:list (msg:valid_hs_msg{associated_to_pv pv msg})) :
  Lemma (requires (Cons? l))
	(ensures (length (handshakeMessagesBytes pv l) > 0))
  = ()

let lemma_aux_3 (b:bytes) (b':bytes) : Lemma (requires (length b <> length b'))
					    (ensures (~(Seq.equal b b'))) = ()

val handshakeMessagesBytes_is_injective: pv:option protocolVersion -> l1:list (msg:valid_hs_msg{associated_to_pv pv msg}) -> l2:list (msg:valid_hs_msg{associated_to_pv pv msg}) ->
  Lemma (requires (True))
	(ensures (Seq.equal (handshakeMessagesBytes pv l1) (handshakeMessagesBytes pv l2) ==> l1 = l2))
let rec handshakeMessagesBytes_is_injective pv l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' -> ();
      let payload1 = handshakeMessagesBytes pv l1 in
      lemma_handshakeMessagesBytes_def pv l1;
      cut (Seq.equal ((handshakeMessageBytes pv hd) @| (handshakeMessagesBytes pv tl)) payload1);
      lemma_op_At_Bar_def (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl);
      let payload2 = handshakeMessagesBytes pv l2 in
      lemma_handshakeMessagesBytes_def pv l2;
      cut (Seq.equal ((handshakeMessageBytes pv hd') @| (handshakeMessagesBytes pv tl')) payload2);
      lemma_op_At_Bar_def (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
      if payload1 = payload2 then (
	cut (Seq.equal (Seq.append (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl))
		       (Seq.append (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl')));
	cut (Seq.equal ((handshakeMessageBytes pv hd) @| (handshakeMessagesBytes pv tl)) ((handshakeMessageBytes pv hd') @| (handshakeMessagesBytes pv tl')));
	if length (handshakeMessageBytes pv hd) >= length (handshakeMessageBytes pv hd')
	then (
	  lemma_aux_1 (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl) (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
	  lemma_handshakeMessageBytes_aux pv hd' hd
	  )
	else (
	  lemma_aux_1 (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl) (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
	  lemma_handshakeMessageBytes_aux pv hd hd'
	);
	lemma_append_inj (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl) (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
	handshakeMessageBytes_is_injective pv hd hd';
	handshakeMessagesBytes_is_injective pv tl tl';
	()
    )
  | [],hd::tl -> (
      lemma_handshakeMessagesBytes_def2 pv l1;
      lemma_aux_2 pv l2;
      lemma_aux_3 (handshakeMessagesBytes pv l1) (handshakeMessagesBytes pv l2)
    )
  | hd::tl, [] -> (
      lemma_handshakeMessagesBytes_def2 pv l2;
      lemma_aux_2 pv l1;
      lemma_aux_3 (handshakeMessagesBytes pv l1) (handshakeMessagesBytes pv l2)
    )

val string_of_handshakeMessage: hs_msg -> Tot string
let string_of_handshakeMessage hs =
    match hs with
    | ClientHello ch -> "ClientHello"
    | ServerHello sh -> "ServerHello"
    | Certificate c -> "Certificate"
    | ServerKeyExchange ske -> "ServerKeyExchange"
    | ServerHelloDone -> "ServerHelloDone"
    | ClientKeyExchange cke -> "ClientKeyExchange"
    | Finished f -> "Finished"
    | SessionTicket t -> "NewSessionTicket"
    | EncryptedExtensions e -> "EncryptedExtensions"
    | CertificateRequest cr -> "CertificateRequest"
    | CertificateVerify cv -> "CertificateVerify"
    | HelloRequest -> "HelloRequest"
    | HelloRetryRequest hrr -> "HelloRetryRequest"
    (* | ServerConfiguration(sc) -> "ServerConfiguration" *)
    | NextProtocol n -> "NextProtocol"
    | _ -> "???"

//17-04-24 should we call parseMessage from this function?

(* val parseHandshakeMessage: option protocolVersion -> option kexAlg -> handshakeType -> b:bytes{repr_bytes (length b) <= 3} -> Tot (result hs_msg) *)
val parseHandshakeMessage: 
  option protocolVersion -> 
  option kexAlg -> 
  ht:handshakeType -> 
  b:bytes{repr_bytes (length b) <= 3} -> 
  Tot (result hs_msg)

let parseHandshakeMessage pv kex hstype pl =
  if length pl < 16777216 then (
    lemma_repr_bytes_values (length pl);
    match hstype,pv,kex with
    | HT_hello_request,_,_       -> if (length pl = 0) then Correct(HelloRequest) else Error(AD_decode_error, "HelloRequest with non-empty body")
    | HT_client_hello,_,_        -> mapResult ClientHello (parseClientHello pl)
    | HT_server_hello,_,_        -> mapResult ServerHello (parseServerHello pl)
    | HT_session_ticket,_,_      -> mapResult SessionTicket (parseSessionTicket pl)
    | HT_hello_retry_request,_,_ -> mapResult HelloRetryRequest (parseHelloRetryRequest pl)
    | HT_encrypted_extensions,_,_ -> mapResult EncryptedExtensions (parseEncryptedExtensions pl)
    | HT_certificate,Some pv,_         -> mapResult Certificate (parseCertificate pv pl)
    | HT_server_key_exchange,_,Some kex -> mapResult ServerKeyExchange (parseServerKeyExchange kex pl)
    | HT_certificate_request,Some pv,_ -> mapResult CertificateRequest (parseCertificateRequest pv pl)
    | HT_server_hello_done,_,_   -> if (length pl = 0) then Correct(ServerHelloDone) else Error(AD_decode_error, "ServerHelloDone with non-empty body")
    | HT_certificate_verify,_,_  -> (
      if length pl < 65536 then mapResult CertificateVerify (parseCertificateVerify pl)
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
      )
    | HT_client_key_exchange,Some pv,Some kex -> mapResult ClientKeyExchange (parseClientKeyExchange pv kex pl)
    (* | HT_server_configuration,_,_ -> mapResult ServerConfiguration (parseServerConfiguration pl) *)
    | HT_next_protocol,_,_       -> mapResult NextProtocol (parseNextProtocol pl)
    | HT_finished,_,_            -> (if length pl < 65536 then mapResult Finished (parseFinished pl)
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "") )
    | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    )
  else  Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

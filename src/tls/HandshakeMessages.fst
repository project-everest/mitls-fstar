(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
(**
Handshake protocol messages
*)
module HandshakeMessages

open FStar.Seq
open FStar.Bytes
open FStar.Error

open TLSError
open TLSConstants
open Extensions
open TLSInfo
open CommonDH

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

let split2 abc n1 n2 =
  let a, bc = split abc (FStar.UInt32.uint_to_t n1) in
  let b, c = split bc (FStar.UInt32.uint_to_t n2) in
  a, b, c

val lbyte_eq_lemma: a:byte -> b:byte -> Lemma (requires (True)) (ensures (a <> b ==> abyte a <> abyte b))
  [SMTPat (abyte a); SMTPat (abyte b)]
let lbyte_eq_lemma a b = if a <> b then cut (Bytes.get (abyte a) 0ul <> Bytes.get (abyte b) 0ul) else ()

/// Handshake types

let htBytes t =
  let z =
  match t with
  | HT_hello_request        -> 0z
  | HT_client_hello         -> 1z
  | HT_server_hello         -> 2z
  | HT_session_ticket       -> 4z
  | HT_end_of_early_data -> 5z
  | HT_hello_retry_request  -> 6z
  | HT_encrypted_extensions -> 8z
  | HT_certificate          -> 11z
  | HT_server_key_exchange  -> 12z
  | HT_certificate_request  -> 13z
  | HT_server_hello_done    -> 14z
  | HT_certificate_verify   -> 15z
  | HT_client_key_exchange  -> 16z
  //| HT_server_configuration -> 17z
  | HT_finished             -> 20z
  | HT_key_update           -> 24z
  | HT_message_hash           -> 254z in
  abyte z

#reset-options "--z3rlimit 100"
let htBytes_is_injective ht1 ht2 = ()

let parseHt b =
  match b.[0ul] with
  |  0z -> Correct HT_hello_request
  |  1z -> Correct HT_client_hello
  |  2z -> Correct HT_server_hello
  |  4z -> Correct HT_session_ticket
  |  5z -> Correct HT_end_of_early_data
  |  6z -> Correct HT_hello_retry_request
  |  8z -> Correct HT_encrypted_extensions
  | 11z -> Correct HT_certificate
  | 12z -> Correct HT_server_key_exchange
  | 13z -> Correct HT_certificate_request
  | 14z -> Correct HT_server_hello_done
  | 15z -> Correct HT_certificate_verify
  | 16z -> Correct HT_client_key_exchange
  //| 17z -> Correct HT_server_configuration
  | 20z -> Correct HT_finished
  | 24z -> Correct HT_key_update
  | 254z -> Correct HT_message_hash
  //| 67z -> Correct HT_next_protocol
  | _   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

#reset-options "--z3rlimit 600 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let inverse_ht x = admit ()
let pinverse_ht x = ()

/// Messages

let ch_is_resumption {ch_sessionID = sid} = length sid > 0

// cwinter: sc is unused?
// noeq type sc = {
//   sc_configuration_id: configurationId;
//   sc_expiration_date: lbytes 4; // SZ: TODO: Use UInt32.t
//   sc_named_group: namedGroup;
//   sc_server_key: kex_c; // JK : use another type ?
//   sc_early_data_type: earlyDataType;
//   sc_configuration_extensions: (l:list configurationExtension{List.Tot.length l < 65536});
// }

/// Post-Handshake Messages 

let error s = Error(AD_decode_error, "Handshake parser: "^s)


/// Handshake message format

let messageBytes ht data =
  let htb = htBytes ht in
  let vldata = vlbytes 3 data in
  htb @| vldata

let messageBytes_is_injective_strong ht1 data1 s1 ht2 data2 s2 = admit()
  //TODO bytes NS 09/27
  // if messageBytes ht1 data1 @| s1 = messageBytes ht2 data2 @| s2 then
  //   begin
  //     assert(Bytes.equal (messageBytes ht1 data1 @| s1) (messageBytes ht2 data2 @| s2));
  //     append_assoc (htBytes ht1) (vlbytes 3 data1) s1;
  //     append_assoc (htBytes ht2) (vlbytes 3 data2) s2;
  //     lemma_append_inj (htBytes ht1) (vlbytes 3 data1 @| s1) (htBytes ht2) (vlbytes 3 data2 @| s2);
  //     lemma_vlbytes_inj_strong 3 data1 s1 data2 s2
  //   end
  // else ()

let messageBytes_is_injective ht1 data1 ht2 data2 =
  messageBytes_is_injective_strong ht1 data1 empty_bytes ht2 data2 empty_bytes

(*
 Somewhat inefficient implementation:
 - Repeatedly parse the first 4 bytes of the incoming buffer until we have a complete message;
 - Then remove that message from the incoming buffer.
*)
let parseMessage buf =
  if length buf < 4 then
    Correct None // not enough data to start parsing
  else
    let hstypeb,rem = split_ buf 1 in
    match parseHt hstypeb with
    | Error z -> Error z
    | Correct ht ->
      match vlsplit 3 rem with
      | Error z -> Correct None // not enough payload, try next time
      | Correct(x) ->
        let payload,rem' = x in
        //assert (Bytes.equal buf (htBytes ht @| rem));
        //assert (Bytes.equal rem (vlbytes 3 payload @| rem'));
        let to_log = messageBytes ht payload in
        Correct (Some (| rem', ht, payload, to_log |))

(** A.4.1 Hello Messages *)

#reset-options
val list_valid_to_valid_list: l:valid_cipher_suites -> Tot (l':list (c:cipherSuite{validCipherSuite c}){List.Tot.length l == List.Tot.length l'})
let rec list_valid_to_valid_list l =
  match l with
  | hd::tl -> hd::(list_valid_to_valid_list tl)
  | [] -> []

val valid_list_to_list_valid: l':list (c:cipherSuite{validCipherSuite c}) -> Tot (l:valid_cipher_suites{List.Tot.length l == List.Tot.length l'})
let rec valid_list_to_list_valid l =
  assume false;
  match l with
  | hd::tl -> hd::(valid_list_to_list_valid tl)
  | [] -> []
#reset-options "--z3rlimit 600 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val messageBytes_extra:
  ht:handshakeType ->
  data:bytes ->
  extra:nat{ repr_bytes (length data + extra) <= 3 } ->
  lbytes (4 + length data)
let messageBytes_extra ht data extra =
  let htb = htBytes ht in
  let vldata = vlbytes_trunc 3 data extra in
  htb @| vldata

let messageBytes_extra_injective
  (ht1: handshakeType)
  (data1: bytes)
  (extra1:nat{ repr_bytes (length data1 + extra1) <= 3 } )
  (s1: bytes)
  (ht2: handshakeType)
  (data2: bytes)
  (extra2:nat{ repr_bytes (length data2 + extra2) <= 3 } )
  (s2: bytes)
: Lemma
  (requires (Bytes.equal (messageBytes_extra ht1 data1 extra1 @| s1) (messageBytes_extra ht2 data2 extra2 @| s2)))
  (ensures (ht1 == ht2 /\ length data1 + extra1 == length data2 + extra2 /\ data1 @| s1 == data2 @| s2))
= let hb1 = htBytes ht1 in
  let v1 = vlbytes_trunc 3 data1 extra1 in
  let hb2 = htBytes ht2 in
  let v2 = vlbytes_trunc 3 data2 extra2 in
  //TODO bytes NS 09/27
  // append_assoc hb1 v1 s1;
  // append_assoc hb2 v2 s2;
  // lemma_append_inj hb1 (v1 @| s1) hb2 (v2 @| s2);
  vlbytes_trunc_injective 3 data1 extra1 s1 data2 extra2 s2

let clientHelloBytes ch =
  //17-04-26 this will complicate injectivity, now conditional on an extension.
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
    | Some ext ->
      assume (repr_bytes (length (extensionListBytes ext)) <= 2 /\ length (Extensions.extensionListBytes ext) + bindersLen ext < 65536); // TODO: FIXME
      extensionsBytes ext
    | None -> empty_bytes in
  let data = verB @| (ch.ch_client_random @| (sidB @| (csB @| (cmB @| extB)))) in
  let binders_len = bindersLen_of_ch ch in
  lemma_repr_bytes_values (length data + binders_len);
  let b = messageBytes_extra HT_client_hello data binders_len in
  assume (FStar.Bytes.length b >= 41 /\ hs_msg_bytes HT_client_hello b); // TODO: FIXME
  b

let versionBytes_is_injective pv1 pv2 =
  cut (pv1 <> pv2 ==> (Bytes.get (versionBytes pv1) 0ul <> Bytes.get (versionBytes pv2) 0ul
                   \/ Bytes.get (versionBytes pv1) 1ul <> Bytes.get (versionBytes pv2) 1ul))

(* JK: additional conditions are required on the size of the extensions after serialization *)
val optionExtensionsBytes: exts:option (ce:list extension{List.Tot.length ce < 256}) -> Tot (b:bytes{length b <= 2 + 65535})
let optionExtensionsBytes exts =
  match exts with
  | Some ext ->
    assume (repr_bytes (length (extensionListBytes ext)) <= 2 /\ length (Extensions.extensionListBytes ext) + bindersLen ext < 65536); // TODO: FIXME
    extensionsBytes ext
  | None -> empty_bytes

#reset-options
val list_valid_to_valid_list_lemma: cs1:valid_cipher_suites{List.Tot.length cs1 < 256} ->
  cs2:valid_cipher_suites{List.Tot.length cs2 < 256} ->
  Lemma (requires True)
  (ensures (list_valid_to_valid_list cs1 == list_valid_to_valid_list cs2 ==> cs1 == cs2))
let rec list_valid_to_valid_list_lemma cs1 cs2 =
  match cs1, cs2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' -> list_valid_to_valid_list_lemma tl tl'
  | _ -> ()

val cipherSuiteBytes_is_injective: cs:valid_cipher_suite -> cs':valid_cipher_suite ->
  Lemma (requires True)
  (ensures (Bytes.equal (cipherSuiteBytes cs) (cipherSuiteBytes cs') ==> cs = cs'))
let cipherSuiteBytes_is_injective cs cs' =
  admit(); // JK: TODO: list the issue in cipherSuiteBytes where there are possible
           // collisions between the serialization of unknown cipher suites and known ones
  //assume (not (UnknownCipherSuite? cs) /\ not (UnknownCipherSuite? cs'));
  cut (Some? (cipherSuiteBytesOpt cs) /\ Some? (cipherSuiteBytesOpt cs'));
  if cs <> cs' then
    match cipherSuiteBytesOpt cs, cipherSuiteBytesOpt cs' with
    | Some a, Some b ->
      let a1, a2 = cbyte2 a in
      let b1, b2 = cbyte2 b in
      assert (a1 <> b1 \/ a2 <> b2)

#reset-options "--z3rlimit 600" // necessary to reset fuel

val cipherSuitesBytes_is_injective_aux: css1:list (c:cipherSuite{validCipherSuite c}) -> css2:list (c:cipherSuite{validCipherSuite c}) ->
  Lemma (requires True)
  (ensures (Bytes.equal (cipherSuitesBytes css1) (cipherSuitesBytes css2) ==> css1 = css2))
let rec cipherSuitesBytes_is_injective_aux css1 css2 =
  match css1, css2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' -> (
      if cipherSuitesBytes css1 = cipherSuitesBytes css2 then (
  assert(cipherSuitesBytes css1 = ((cipherSuiteBytes hd) @| (cipherSuitesBytes tl)));
  assert(cipherSuitesBytes css2 = ((cipherSuiteBytes hd') @| (cipherSuitesBytes tl')));
  assert(length (cipherSuiteBytes hd) = length (cipherSuiteBytes hd'));
  // lemma_append_inj (cipherSuiteBytes hd) (cipherSuitesBytes tl) (cipherSuiteBytes hd') (cipherSuitesBytes tl');   //TODO bytes NS 09/27
  cipherSuitesBytes_is_injective_aux tl tl';
  cipherSuiteBytes_is_injective hd hd'
  )
      else ()
      )
  | _ -> ()

val cipherSuitesBytes_is_injective: cs1:valid_cipher_suites{List.Tot.length cs1 < 256} ->
  cs2:valid_cipher_suites{List.Tot.length cs2 < 256} ->
  Lemma (requires True)
  (ensures (Bytes.equal (cipherSuitesBytes (list_valid_to_valid_list cs1))
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
  Lemma (requires True)
  (ensures (Bytes.equal (compressionMethodsBytes l1) (compressionMethodsBytes l2) ==> l1 = l2))
let rec compressionMethodsBytes_is_injective l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if compressionMethodsBytes l1 = compressionMethodsBytes l2 then (
      compressionMethodsBytes_is_injective tl tl';
      //lemma_append_inj (compressionBytes hd) (compressionMethodsBytes tl) (compressionBytes hd') (compressionMethodsBytes tl');   //TODO bytes NS 09/27
      assert (compressionBytes hd = compressionBytes hd' ==> hd = hd'))
  | _ -> ()

val optionExtensionsBytes_is_injective: ext1:option (ce:list extension{List.Tot.length ce < 256}) ->
  ext2:option (ce2:list extension{List.Tot.length ce2 < 256}) ->
  Lemma (requires True)
  (ensures (Bytes.equal (optionExtensionsBytes ext1) (optionExtensionsBytes ext2) ==> ext1 == ext2))
let optionExtensionsBytes_is_injective ext1 ext2 =
  if optionExtensionsBytes ext1 = optionExtensionsBytes ext2
  then begin
    (* JK: TODO: make the assumes part of the specifications *)
    assume (Some? ext1 ==> (let (Some e1) = ext1 in (repr_bytes (length (extensionListBytes e1)) <= 2 /\ length (Extensions.extensionListBytes e1) + bindersLen e1 < 65536))); // TODO: FIXME
    assume (Some? ext2 ==> (let (Some e2) = ext2 in (repr_bytes (length (extensionListBytes e2)) <= 2 /\ length (Extensions.extensionListBytes e2) + bindersLen e2 < 65536))); // TODO: FIXME
    match ext1, ext2 with
    | Some e1, Some e2 ->
      extensionsBytes_is_injective e1 e2
    | _ -> ()
  end else ()

let clientHelloBytes_is_injective_strong msg1 s1 msg2 s2 =
  if clientHelloBytes msg1 @| s1 = clientHelloBytes msg2 @| s2 then begin
    let legacyVersion1 = minPV TLS_1p2 msg1.ch_protocol_version in
    let verB1 = versionBytes legacyVersion1 in
    lemma_repr_bytes_values (length msg1.ch_sessionID);
    let sidB1 = vlbytes 1 msg1.ch_sessionID in
    let csb1 : bytes = cipherSuitesBytes (list_valid_to_valid_list msg1.ch_cipher_suites) in
    lemma_repr_bytes_values (length csb1);
    let csB1 = vlbytes 2 csb1 in
    lemma_repr_bytes_values (List.Tot.length msg1.ch_compressions);
    let cmb1 = compressionMethodsBytes msg1.ch_compressions in
    let cmB1 = vlbytes 1 cmb1 in
    let extB1 = match msg1.ch_extensions with
    | Some ext ->
      assume (repr_bytes (length (extensionListBytes ext)) <= 2 /\ length (Extensions.extensionListBytes ext) + bindersLen ext < 65536); // TODO: FIXME
      extensionsBytes ext
    | None -> empty_bytes
    in
    let tail3_1 = cmB1 @| extB1 in
    let tail4_1 = csB1 @| tail3_1 in
    let tail5_1 = sidB1 @| tail4_1 in
    let tail6_1 = msg1.ch_client_random @| tail5_1 in
    let data1 = verB1 @| tail6_1 in
    let binders_len1 = bindersLen_of_ch msg1 in
    lemma_repr_bytes_values (length data1 + binders_len1);
    assert (clientHelloBytes msg1 == messageBytes_extra HT_client_hello data1 binders_len1);
    let legacyVersion2 = minPV TLS_1p2 msg2.ch_protocol_version in
    let verB2 = versionBytes legacyVersion2 in
    lemma_repr_bytes_values (length msg2.ch_sessionID);
    let sidB2 = vlbytes 1 msg2.ch_sessionID in
    let csb2 : bytes = cipherSuitesBytes (list_valid_to_valid_list msg2.ch_cipher_suites) in
    lemma_repr_bytes_values (length csb2);
    let csB2 = vlbytes 2 csb2 in
    lemma_repr_bytes_values (List.Tot.length msg2.ch_compressions);
    let cmb2 = compressionMethodsBytes msg2.ch_compressions in
    let cmB2 = vlbytes 1 cmb2 in
    let extB2 = match msg2.ch_extensions with
    | Some ext ->
      assume (repr_bytes (length (extensionListBytes ext)) <= 2 /\ length (Extensions.extensionListBytes ext) + bindersLen ext < 65536); // TODO: FIXME
      extensionsBytes ext
    | None -> empty_bytes
    in
    let tail3_2 = cmB2 @| extB2 in
    let tail4_2 = csB2 @| tail3_2 in
    let tail5_2 = sidB2 @| tail4_2 in
    let tail6_2 = msg2.ch_client_random @| tail5_2 in
    let data2 = verB2 @| tail6_2 in
    let binders_len2 = bindersLen_of_ch msg2 in
    lemma_repr_bytes_values (length data2 + binders_len2);
    assert (clientHelloBytes msg2 == messageBytes_extra HT_client_hello data2 binders_len2);
    messageBytes_extra_injective HT_client_hello data1 binders_len1 s1 HT_client_hello data2 binders_len2 s2;
    //TODO bytes NS 09/27
    // append_assoc verB1 tail6_1 s1;
    // append_assoc verB2 tail6_2 s2;
    // lemma_append_inj verB1 (tail6_1 @| s1) verB2 (tail6_2 @| s2);
    versionBytes_is_injective legacyVersion1 legacyVersion2;
    let f
      ()
    : Lemma (msg1.ch_protocol_version == msg2.ch_protocol_version)
    = assume (~ (msg1.ch_protocol_version == TLS_1p3)); // TODO: FIXME (see comment on ch_protocol_version: should this be formalized as a refinement constraint there?)
      assume (~ (msg2.ch_protocol_version == TLS_1p3)); // TODO: FIXME
      // (those assumes are enclosed in a function so they do not leak into the rest of the proof)
      ()
    in
    f ();
    //TODO bytes NS 09/27
    // append_assoc msg1.ch_client_random tail5_1 s1;
    // append_assoc msg2.ch_client_random tail5_2 s2;
    // lemma_append_inj msg1.ch_client_random (tail5_1 @| s1) msg2.ch_client_random (tail5_2 @| s2);
    // append_assoc sidB1 tail4_1 s1;
    // append_assoc sidB2 tail4_2 s2;
    lemma_vlbytes_inj_strong 1 msg1.ch_sessionID (tail4_1 @| s1) msg2.ch_sessionID (tail4_2 @| s2);
    //TODO bytes NS 09/27
    // append_assoc csB1 tail3_1 s1;
    // append_assoc csB2 tail3_2 s2;
    lemma_vlbytes_inj_strong 2 csb1 (tail3_1 @| s1) csb2 (tail3_2 @| s2);
    let _ : squash (msg1.ch_cipher_suites == msg2.ch_cipher_suites) =
      cipherSuitesBytes_is_injective msg1.ch_cipher_suites msg2.ch_cipher_suites
    in
    //TODO bytes NS 09/27
    // append_assoc cmB1 extB1 s1;
    // append_assoc cmB2 extB2 s2;
    lemma_vlbytes_inj_strong 1 cmb1 (extB1 @| s1) cmb2 (extB2 @| s2);
    let _ : squash (msg1.ch_compressions == msg2.ch_compressions) =
      compressionMethodsBytes_is_injective msg1.ch_compressions msg2.ch_compressions
    in
    assert (length extB1 + binders_len1 == length extB2 + binders_len2);
    match msg1.ch_extensions with
    | None ->
      assert (msg2.ch_extensions == None)
      //TODO bytes NS 09/27
      // lemma_append_inj extB1 s1 extB2 s2
    | Some e1 ->
      let (Some e2) = msg2.ch_extensions in
      assume (repr_bytes (length (extensionListBytes e1)) <= 2 /\ length (Extensions.extensionListBytes e1) + bindersLen e1 < 65536); // TODO: FIXME
      assume (repr_bytes (length (extensionListBytes e2)) <= 2 /\ length (Extensions.extensionListBytes e2) + bindersLen e2 < 65536); // TODO: FIXME
      extensionsBytes_is_injective_strong e1 s1 e2 s2
  end else ()

val clientHelloBytes_is_injective: msg1:ch -> msg2:ch ->
  Lemma (requires True)
  (ensures (Bytes.equal (clientHelloBytes msg1) (clientHelloBytes msg2) ==> (msg1 == msg2)))
  [SMTPat (clientHelloBytes msg1); SMTPat (clientHelloBytes msg2)]
let clientHelloBytes_is_injective msg1 msg2 =
  clientHelloBytes_is_injective_strong msg1 empty_bytes msg2 empty_bytes

(* JK: to work around a subtyping difficulty in parseClientHello *)
val coercion_helper: o:option (list extension){Some? o ==>  List.Tot.length (Some?.v o) < 256}
   -> Tot (option (l:list extension{List.Tot.length l < 256}))
let coercion_helper e =
  match e with
  | None -> None
  | Some li -> cut (List.Tot.length li < 256); Some li

// TR: verifies up to this point

let parseClientHello data =
  if length data < 35 then error "ClientHello is too short" else
  let clVerBytes,cr_data = split data 2ul in
  let cr, data = split cr_data 32ul in
  match parseVersion clVerBytes with
  | Error z -> Error z
  | Correct cv ->
    match vlsplit 1 data with
    | Error z -> error "sid length"
    | Correct (x) ->
      let sid,data = x in
      if length sid > 32 || length data < 2 then error "sid" else (
      match vlsplit 2 data with
      | Error z -> error "ciphersuites length"
      | Correct (x) -> 
        let clCiphsuitesBytes,data = x in
        if length clCiphsuitesBytes >= 512 then error "ciphersuites" else (
        let clientCipherSuites = parseCipherSuites clCiphsuitesBytes in
          (* ADL More relaxed parsing for old ClientHello messages with *)
          (* no compression and no extensions *)
          let compExts =
            if length data < 1 || List.Tot.length clientCipherSuites >= 256 then error "ciphersuites length"
            else (match vlsplit 1 data with
            | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse compression bytes")
            | Correct (x) ->
              let cmBytes, extensions = x in
              let cm = parseCompressions cmBytes in
               (match parseOptExtensions EM_ClientHello extensions with
                | Error z -> Error z
                | Correct (x) ->
                    let exts, obinders = x in
                    if (match exts with
                        | None -> true
                        | Some l -> List.Tot.length l < 256)
                        && List.Tot.length cm < 256 &&  List.Tot.length cm > 0
                    then Correct (cm, (coercion_helper exts, obinders))
                    else error "bad extension lengths"))
            in
            ( match compExts with
              | Error z -> Error z
              | Correct (cm, (exts, obinders)) -> (
                cut (List.Tot.length clientCipherSuites < 256);
                let cCS = valid_list_to_list_valid clientCipherSuites in
                Correct ({
                  ch_protocol_version = cv;
                  ch_client_random = cr;
                  ch_sessionID = sid;
                  ch_cipher_suites = cCS;
                  ch_compressions = cm;
                  ch_extensions = exts; }, obinders)))))

let serverHelloBytes sh =
  // signalling the current draft version
  let pv = match sh.sh_protocol_version with | TLS_1p3 -> TLS_1p2 | v -> v in
  let verB = versionBytes_draft pv in
  lemma_repr_bytes_values (length sh.sh_sessionID);
  let sidB = vlbytes 1 sh.sh_sessionID in
  let csB = cipherSuiteBytes sh.sh_cipher_suite in
  let cmB = compressionBytes sh.sh_compression in
  let extB =
    match sh.sh_extensions with
    | Some ext -> extensionsBytes ext
    | None -> empty_bytes in  // JK: in TLS1.3 case should be vlbytes 2 empty_bytes
  let data:bytes = verB @| (sh.sh_server_random @| (sidB @| (csB @| (cmB @| extB)))) in
  lemma_repr_bytes_values (length data);
  messageBytes HT_server_hello data

#reset-options "--z3rlimit 50"

// 18-02-15 disabling verification attemps (150', 44 errors) till the new parsers.
#set-options "--lax"

let serverHelloBytes_is_injective msg1 msg2 =
  if serverHelloBytes msg1 = serverHelloBytes msg2 then
  begin
    let verB1 = versionBytes_draft msg1.sh_protocol_version in
    lemma_repr_bytes_values (length msg1.sh_sessionID);
    let sidB1 = vlbytes 1 msg1.sh_sessionID in
      let csB1 = cipherSuiteBytes msg1.sh_cipher_suite in
      let cmB1 =  compressionBytes msg1.sh_compression in
      let extB1 = match msg1.sh_extensions with
      | Some ext -> extensionsBytes ext
      | None -> empty_bytes in
      let data1:bytes = match msg1.sh_protocol_version with
      | TLS_1p3 -> verB1 @| (msg1.sh_server_random @| (csB1 @| extB1))
      | _       -> verB1 @| (msg1.sh_server_random @| (sidB1 @| (csB1 @| (cmB1 @| extB1)))) in
      lemma_repr_bytes_values (length data1);
      let verB2 = versionBytes_draft msg2.sh_protocol_version in
      lemma_repr_bytes_values (length msg2.sh_sessionID);
      let sidB2 = vlbytes 1 msg2.sh_sessionID in
      let csB2 = cipherSuiteBytes msg2.sh_cipher_suite in
      let cmB2 = compressionBytes msg2.sh_compression in
      let extB2:bytes = match msg2.sh_extensions with
      | Some ext -> extensionsBytes ext
      | None -> empty_bytes in
      let data2:bytes = match msg2.sh_protocol_version with
      | TLS_1p3 -> verB2 @| (msg2.sh_server_random @| (csB2 @| extB2))
      | _       -> verB2 @| (msg2.sh_server_random @| (sidB2 @| (csB2 @| (cmB2 @| extB2)))) in
      lemma_repr_bytes_values (length data2);
      messageBytes_is_injective HT_server_hello data1 HT_server_hello data2;
      cut(Bytes.equal data1 data2);
      let s1 = split data1 2ul in
      let s2 = split data2 2ul in
      cut(Bytes.equal verB1 (fst s1) /\ Bytes.equal verB2 (fst s2));
      //TODO bytes NS 09/27
      //lemma_append_inj verB1 (snd s1) verB2 (snd s2);
      versionBytes_is_injective msg1.sh_protocol_version msg2.sh_protocol_version;
      cut(msg1.sh_protocol_version = msg2.sh_protocol_version);
      if msg1.sh_protocol_version = TLS_1p3 then (
  cut (Bytes.equal (snd s1) (snd s2));
  cut (Bytes.equal (snd s1) (msg1.sh_server_random @| (csB1 @| extB1)));
  cut (Bytes.equal (snd s2) (msg2.sh_server_random @| (csB2 @| extB2)));
  cut (length msg1.sh_server_random = length msg2.sh_server_random);
  //TODO bytes NS 09/27
  //lemma_append_inj msg1.sh_server_random (csB1 @| extB1) msg2.sh_server_random (csB2 @| extB2);
  assert(msg1.sh_server_random = msg2.sh_server_random);
  let l1 = (csB1 @| extB1) in
  let l2 = (csB2 @| extB2) in
  cut(length csB1 >= 2 /\ length csB2 >= 2);
  cut(Bytes.get csB1 0ul = Bytes.get l1 0ul /\ Bytes.get csB1 1ul = Bytes.get l1 1ul);
  cut(Bytes.get csB2 0ul = Bytes.get l2 0ul /\ Bytes.get csB2 1ul = Bytes.get l2 1ul);
  cut(length (cipherSuiteBytes msg1.sh_cipher_suite) = length (cipherSuiteBytes msg2.sh_cipher_suite));
  //TODO bytes NS 09/27
  //lemma_append_inj csB1 extB1 csB2 extB2;
  cipherSuiteBytes_is_injective msg1.sh_cipher_suite msg2.sh_cipher_suite;
  optionExtensionsBytes_is_injective msg1.sh_extensions msg2.sh_extensions;
  ())
      else (
  cut (Bytes.equal (snd s1) (snd s2));
  cut (Bytes.equal (snd s1) (msg1.sh_server_random @| (sidB1 @| (csB1 @| (cmB1 @| extB1)))));
  cut (Bytes.equal (snd s2) (msg2.sh_server_random @| (sidB2 @| (csB2 @| (cmB2 @| extB2)))));
  cut (length msg1.sh_server_random = length msg2.sh_server_random);
  //TODO bytes NS 09/27
  // lemma_append_inj msg1.sh_server_random (sidB1 @| (csB1 @| (cmB1 @| extB1)))
  //      msg2.sh_server_random (sidB2 @| (csB2 @| (cmB2 @| extB2)));
  let l1 = (sidB1 @| (csB1 @| (cmB1 @| extB1))) in
  let l2 = (sidB2 @| (csB2 @| (cmB2 @| extB2))) in
  cut(length sidB1 >= 1);
  cut(length sidB2 >= 1);
  cut(Bytes.equal l1 l2);
  cut(Bytes.get sidB1 0ul = Bytes.get l1 0ul /\ Bytes.get sidB2 0ul = Bytes.get l2 0ul);
  cut(Bytes.get sidB1 0ul = Bytes.get sidB2 0ul);
  vlbytes_length_lemma 1 (msg1.sh_sessionID) (msg2.sh_sessionID);
  cut (length sidB1 = length sidB2);
  //TODO bytes NS 09/27
  //lemma_append_inj sidB1 (csB1 @| (cmB1 @| extB1)) sidB2 (csB2 @| (cmB2 @| extB2));
  cut(length csB1 >= 2 /\ length csB2 >= 2);
  let l1 = (csB1 @| (cmB1 @| extB1)) in
  let l2 = (csB2 @| (cmB2 @| extB2)) in
  cut(Bytes.get csB1 0ul = Bytes.get l1 0ul /\ Bytes.get csB1 1ul = Bytes.get l1 1ul);
  cut(Bytes.get csB2 0ul = Bytes.get l2 0ul /\ Bytes.get csB2 1ul = Bytes.get l2 1ul);
  cut(length (cipherSuiteBytes msg1.sh_cipher_suite) = length (cipherSuiteBytes msg2.sh_cipher_suite));
  //TODO bytes NS 09/27
  //lemma_append_inj csB1 (cmB1 @| extB1) csB2 (cmB2 @| extB2);
  cut (length cmB1 = length cmB2);
  //TODO bytes NS 09/27
  //lemma_append_inj cmB1 extB1 cmB2 extB2;
  cipherSuiteBytes_is_injective msg1.sh_cipher_suite msg2.sh_cipher_suite;
  optionExtensionsBytes_is_injective msg1.sh_extensions msg2.sh_extensions;
  cut(msg1.sh_protocol_version = msg2.sh_protocol_version);
  cut(msg1.sh_server_random = msg2.sh_server_random);
  cut(Bytes.equal sidB1 sidB2);
  lemma_vlbytes_inj 1 (msg1.sh_sessionID) (msg2.sh_sessionID);
  ()
      )
    end

// TR: the following proof successfully verifies 
let serverHelloBytes_is_injective_strong msg1 s1 msg2 s2 =
  let b1 = serverHelloBytes msg1 in
  let b1' = snd (split b1 4ul) in
  let b2 = serverHelloBytes msg2 in
  let b2' = snd (split b2 4ul) in
  messageBytes_is_injective_strong HT_server_hello b1' s1 HT_server_hello b2' s2;
  serverHelloBytes_is_injective msg1 msg2

#reset-options
//#set-options "--lax"

let parseServerHello data =
  if length data < 34 then
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  else
    let (serverVerBytes, serverRandomBytes, data) = split2 data 2 32 in
    match parseVersion_draft serverVerBytes with
    | Error z -> Error z
    | Correct serverVer ->
     if length data >= 1 then
       match vlsplit 1 data with
       | Error z -> Error z
       | Correct (x) ->
         let sid,data = x in
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
                     let em = // FIXME what can we do about this horrible, atrocious hack?
                       if bytes_of_hex "cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c" = serverRandomBytes
                       then EM_HelloRetryRequest else EM_ServerHello in
                      (match parseOptExtensions em data with
                       | Error z -> Error z
                       | Correct (x) ->
                         let exts,obinders = x in
                         if (match exts with
                             | None -> true
                             | Some l -> List.Tot.length l < 256)
                         then
                           let exts = coercion_helper exts in
                           correct ({
                             sh_protocol_version = serverVer;
                             sh_server_random = serverRandomBytes;
                             sh_sessionID = sid;
                             sh_cipher_suite = cs;
                             sh_compression = NullCompression;
                             sh_extensions = exts})
                         else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))))
           else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
         else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
     else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let helloRequestBytes =
  lemma_repr_bytes_values 0;
  messageBytes HT_hello_request empty_bytes

let ccsBytes = abyte 1z

let serverHelloDoneBytes =
  lemma_repr_bytes_values 0;
  messageBytes HT_server_hello_done empty_bytes

(** A.4.2 Server Authentication and Key Exchange Messages *)

let valid_crt = c:crt {length (Cert.certificateListBytes c.crt_chain) < 16777212}
let valid_crt13 = c:crt13 {length (Cert.certificateListBytes13 c.crt_chain13) < 16777212}

val certificateBytes: valid_crt -> b:bytes{hs_msg_bytes HT_certificate b}
let certificateBytes crt =
  let cb = Cert.certificateListBytes crt.crt_chain in
  lemma_repr_bytes_values (length cb);
  lemma_repr_bytes_values (length (vlbytes 3 cb));
  messageBytes HT_certificate (vlbytes 3 cb)

val certificateBytes13: valid_crt13 -> b:bytes{hs_msg_bytes HT_certificate b}
let certificateBytes13 crt =
  let cb = Cert.certificateListBytes13 crt.crt_chain13 in
  lemma_repr_bytes_values (length empty_bytes);
  cut (length ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb)) < 16777216);
  lemma_repr_bytes_values (length ((vlbytes 1 empty_bytes) @| vlbytes 3 cb));
  messageBytes HT_certificate ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb))

val certificateBytes_is_injective: c1:valid_crt -> c2:valid_crt ->
  Lemma (Bytes.equal (certificateBytes c1) (certificateBytes c2) ==> c1 = c2)
let certificateBytes_is_injective c1 c2 =
  if certificateBytes c1 = certificateBytes c2  then (
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
    cut (Bytes.equal (certificateBytes c1) (messageBytes HT_certificate ((vlbytes 3 cb1))));
    cut (Bytes.equal (certificateBytes c2) (messageBytes HT_certificate ((vlbytes 3 cb2))));
    messageBytes_is_injective HT_certificate (vlbytes 3 cb1)
            HT_certificate (vlbytes 3 cb2);
    lemma_vlbytes_inj 3 cb1 cb2;
    Cert.certificateListBytes_is_injective c1.crt_chain c2.crt_chain;
    ()
  ) else ()

val certificateBytes13_is_injective: c1:valid_crt13 -> c2:valid_crt13 ->
  Lemma (Bytes.equal (certificateBytes13 c1) (certificateBytes13 c2) ==> c1 = c2)
let certificateBytes13_is_injective c1 c2 =
  if certificateBytes13 c1 = certificateBytes13 c2  then (
    let cb1 = Cert.certificateListBytes13 c1.crt_chain13 in
    let cb2 = Cert.certificateListBytes13 c2.crt_chain13 in
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
    cut (Bytes.equal (certificateBytes13 c1) (messageBytes HT_certificate ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb1))));
    cut (Bytes.equal (certificateBytes13 c2) (messageBytes HT_certificate ((vlbytes 1 empty_bytes) @| (vlbytes 3 cb2))));
    messageBytes_is_injective HT_certificate ((vlbytes 1 empty_bytes) @| vlbytes 3 cb1)
            HT_certificate ((vlbytes 1 empty_bytes) @| vlbytes 3 cb2);
    //TODO bytes NS 09/27
    //lemma_append_inj (vlbytes 1 empty_bytes) (vlbytes 3 cb1) (vlbytes 1 empty_bytes) (vlbytes 3 cb2);
    lemma_vlbytes_inj 3 cb1 cb2;
    Cert.certificateListBytes13_is_injective c1.crt_chain13 c2.crt_chain13;
    ()
  ) else ()

// SZ: I think this should be
// val parseCertificate: pv:protocolVersion -> data:bytes{3 <= length data /\ repr_bytes (length data - 3) <= 3}
//  -> Tot (result (r:crt{Bytes.equal (certificateBytes r) (messageBytes HT_certificate data)}))
(* val parseCertificate: pv:protocolVersion -> data:bytes{repr_bytes (length data) <= 3}  *)
(*   -> Tot (result (r:valid_crt{Bytes.equal (certificateBytes pv r) (messageBytes HT_certificate data)})) *)
val parseCertificate: data:bytes{repr_bytes (length data) <= 3} -> Tot (result valid_crt)
let parseCertificate data =
  if length data < 3 then error "not enough certificate-list length bytes" else
  match vlparse 3 data with
  | Error (x,y) -> Error(AD_bad_certificate_fatal, y)
  | Correct certList -> (
    match Cert.parseCertificateList certList with
    | Error (x,y) -> Error(AD_bad_certificate_fatal, y)
    | Correct l ->
      if length certList >= 16777212 then error "certificate list is too large" else
      ( Cert.lemma_parseCertificateList_length certList;
        Correct ({crt_chain = l})))

val parseCertificate13: data:bytes{repr_bytes (length data) <= 3} -> Tot (result valid_crt13)
let parseCertificate13 data =
  if length data < 1 then error "not enough bytes (context)" else
  let hdr, data = split data 1ul in
  if not (hdr = abyte 0z) then error "non-empty context" else
  if length data < 3 then error "not enough bytes (certificate list length)" else (
  match vlparse 3 data with
  | Error (x,y) -> Error(AD_bad_certificate_fatal, y)
  | Correct certList -> (
    match Cert.parseCertificateList13 certList with
    | Error z -> Error z
    | Correct l ->
      if length certList >= 16777212 then error "certificate list is too large" else
      ( //Cert.lemma_parseCertificateList_length13 certList;
        Correct ({crt_request_context = empty_bytes; crt_chain13 = l}))))

(* JK: TODO: rewrite taking the protocol version as an extra parameter, otherwise not injective *)
val certificateRequestBytes: cr -> b:bytes{hs_msg_bytes HT_certificate_request b}
let certificateRequestBytes cr =
  let ctb = certificateTypeListBytes cr.cr_cert_types in
  lemma_repr_bytes_values (length ctb);
  let ctB = vlbytes 1 ctb in
  let saB =
    match cr.cr_sig_algorithms with
    | None -> empty_bytes
    | Some sigAlgs -> signatureSchemeListBytes sigAlgs // includes length header
  in
  let dnb = distinguishedNameListBytes cr.cr_certificate_authorities in
  lemma_repr_bytes_values (length dnb);
  let dnB = vlbytes 2 dnb in
  let data = ctB @| saB @| dnB in
  lemma_repr_bytes_values (length data);
  messageBytes HT_certificate_request data

val certificateTypeListBytes_is_injective: ctl1:list certType -> ctl2:list certType ->
  Lemma (Bytes.equal (certificateTypeListBytes ctl1) (certificateTypeListBytes ctl2) ==> ctl1 = ctl2)
let rec certificateTypeListBytes_is_injective ctl1 ctl2 =
  match ctl1, ctl2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' ->
    if certificateTypeListBytes ctl1 = certificateTypeListBytes ctl2 then (
      cut (Bytes.equal (certTypeBytes hd @| certificateTypeListBytes tl) (certTypeBytes hd' @| certificateTypeListBytes tl'));
      //TODO bytes NS 09/27
      //lemma_append_inj (certTypeBytes hd) (certificateTypeListBytes tl) (certTypeBytes hd') (certificateTypeListBytes tl');
      cut(hd = hd');
      certificateTypeListBytes_is_injective tl tl'
    )
  | _, _ -> ()

#reset-options

let lemma_distinguishedNameListBytes_def (n:list dn{Cons? n /\ repr_bytes (length (utf8_encode (Cons?.hd n))) <= 2}) : Lemma
  (distinguishedNameListBytes n = (vlbytes 2 (utf8_encode (Cons?.hd n)) @| distinguishedNameListBytes (Cons?.tl n))) = ()

let lemma_distinguishedNameListBytes_def2 (n:list dn{Nil? n}) : Lemma (distinguishedNameListBytes n = empty_bytes) = ()

(* TODO: port to FStar.Bytes *)
assume val utf8_is_injective: s:string -> s':string ->
  Lemma (requires True)
  (ensures (Bytes.equal (utf8_encode s) (utf8_encode s') ==> s = s'))

val distinguishedNameListBytes_is_injective: n1:list dn -> n2:list dn ->
  Lemma (requires True)
  (ensures (Bytes.equal (distinguishedNameListBytes n1) (distinguishedNameListBytes n2) ==> n1 = n2))
let rec distinguishedNameListBytes_is_injective n1 n2 = admit ()
  //this is very stale now
  //TODO bytes NS 09/27
  // match n1, n2 with
  // | [],[] -> ()
  // | hd::tl, hd'::tl' ->
  //     let payload1 = distinguishedNameListBytes n1 in
  //     let payload2 = distinguishedNameListBytes n2 in
  //     if payload1 = payload2 then (
  // lemma_repr_bytes_values (length (utf8_encode hd'));
  // lemma_repr_bytes_values (length (utf8_encode hd));
  // lemma_distinguishedNameListBytes_def n1;
  // lemma_distinguishedNameListBytes_def n2;
  // //cut (forall b b'. {:pattern (b@|b')} (b@|b') = Seq.append b b'); //TODO bytes NS 09/27 redundant?
  // //Seq.lemma_eq_refl payload1 payload2;
  // cut (Bytes.equal ((vlbytes 2 (utf8_encode hd))  @| (distinguishedNameListBytes tl))
  //                  ((vlbytes 2 (utf8_encode hd')) @| (distinguishedNameListBytes tl')));
  // // cut (Bytes.equal (Bytes.append (vlbytes 2 (utf8_encode hd))  (distinguishedNameListBytes tl))
  // //                  (Bytes.append (vlbytes 2 (utf8_encode hd')) (distinguishedNameListBytes tl')));
  //       cut (Bytes.get (vlbytes 2 (utf8_encode hd)) 0 = Bytes.get payload1 0);
  //       cut (Bytes.get (vlbytes 2 (utf8_encode hd)) 1 = Bytes.get payload1 1);
  //       cut (Bytes.get (vlbytes 2 (utf8_encode hd')) 0 = Bytes.get payload2 0);
  //       cut (Bytes.get (vlbytes 2 (utf8_encode hd')) 1 = Bytes.get payload2 1);
  // cut (Bytes.get payload1 0 = Bytes.get payload2 0);
  //       cut (Bytes.get payload1 1 = Bytes.get payload2 1);
  // vlbytes_length_lemma 2 (utf8_encode hd) (utf8_encode hd');
  // lemma_append_inj (vlbytes 2 (utf8_encode hd)) (distinguishedNameListBytes tl) (vlbytes 2 (utf8_encode hd')) (distinguishedNameListBytes tl');
  // distinguishedNameListBytes_is_injective tl tl';
  // lemma_vlbytes_inj 2 (utf8_encode hd) (utf8_encode hd');
  // utf8_is_injective hd hd'
  //     )
  // | [],hd::tl -> (
  //     lemma_repr_bytes_values (length (utf8 hd));
  //     lemma_distinguishedNameListBytes_def n2;
  //     lemma_distinguishedNameListBytes_def2 n1;
  //     cut (forall b b'. {:pattern (b@|b')} (b@|b') = Seq.append b b');
  //     cut (length (distinguishedNameListBytes n2) >= 2);
  //     cut (length (distinguishedNameListBytes n1) = 0)
  //     )
  // | hd::tl,[] -> (
  //     lemma_repr_bytes_values (length (utf8 hd));
  //     lemma_distinguishedNameListBytes_def n1;
  //     lemma_distinguishedNameListBytes_def2 n2;
  //     cut (forall b b'. {:pattern (b@|b')} (b@|b') = Seq.append b b');
  //     cut (length (distinguishedNameListBytes n1) >= 2);
  //     cut (length (distinguishedNameListBytes n2) = 0)
  //     )

//#set-options "--lax"

val certificateRequestBytes_is_injective: c1:cr -> c2:cr ->
  Lemma (requires True)
  (ensures (Bytes.equal (certificateRequestBytes c1) (certificateRequestBytes c2) ==> c1 = c2))
let certificateRequestBytes_is_injective c1 c2 =
  admit(); // JK: TODO
  if certificateRequestBytes c1 = certificateRequestBytes c2 then (
    let ctb1 = certificateTypeListBytes c1.cr_cert_types in
    lemma_repr_bytes_values (length ctb1);
    let ctB1 = vlbytes 1 ctb1 in
    let saB1 = admit() in //signatureSchemeListBytes c1.cr_sig_algorithms in
    let dnb1 = distinguishedNameListBytes c1.cr_certificate_authorities in
    lemma_repr_bytes_values (length dnb1);
    let dnB1 = vlbytes 2 dnb1 in
    let data1 = ctB1 @| saB1 @| dnB1 in
    let ctb2 = certificateTypeListBytes c2.cr_cert_types in
    lemma_repr_bytes_values (length ctb2);
    let ctB2 = vlbytes 1 ctb2 in
    let saB2 = admit() in // signatureSchemeListBytes c2.cr_sig_algorithms in
    let dnb2 = distinguishedNameListBytes c2.cr_certificate_authorities in
    lemma_repr_bytes_values (length dnb2);
    let dnB2 = vlbytes 2 dnb2 in
    let data2 = ctB2 @| saB2 @| dnB2 in
    lemma_repr_bytes_values (length data2);
    lemma_repr_bytes_values (length data1);
    messageBytes_is_injective HT_certificate_request data1 HT_certificate_request data2;
    assume (Bytes.equal (slice_ data1 0 1) (slice_ data2 0 1));
    assume (Bytes.equal (slice_ data1 0 1) (slice_ ctB1 0 1));
    assume (Bytes.equal (slice_ data2 0 1) (slice_ ctB2 0 1));
    vlbytes_length_lemma 1 ctb1 ctb2
    //TODO bytes NS 09/27
    //lemma_append_inj ctB1 (saB1 @| dnB1) ctB2 (saB2 @| dnB2)
  )

// TODO split on pv
val parseCertificateRequest: pv:protocolVersion -> data:bytes -> result cr
let parseCertificateRequest pv data =
  if length data >= 1 then
    match vlsplit 1 data with
    | Error z -> Error z
    | Correct (x) ->
      let certTypeListBytes, data = x in
      let certTypeList = parseCertificateTypeList certTypeListBytes in
      let n = List.Tot.length certTypeList in
      if 0 < n && n < 256 then // Redundant to check upper bound
        if length data >= 2 then
          begin
          match pv with
          | TLS_1p2 ->
            begin
            match vlsplit 2 data with
            | Error z -> Error z
            | Correct (x) ->
              let signatureAlgorithmsBytes, data = x in
              begin
              lemma_repr_bytes_values (length signatureAlgorithmsBytes);
              match parseSignatureSchemeList (vlbytes 2 signatureAlgorithmsBytes) with
              | Error z -> Error z
              | Correct sigAlgs ->
                if length data >= 2 then
                  match vlparse 2 data with
                  | Error z -> Error z
                  | Correct certificateAuthoritiesBytes ->
                    begin
                    match parseDistinguishedNameList certificateAuthoritiesBytes [] with
                    | Error z -> Error z
                    | Correct distNamesList ->
                      correct (
                        {cr_cert_types = certTypeList;
                         cr_sig_algorithms = Some sigAlgs;
                         cr_certificate_authorities = distNamesList})
                    end
                else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Certificate Request message is too short")
              end
            end
          | _ -> // TLS_1p0, TLS_1p1
            match parseDistinguishedNameList data [] with
            | Error z -> Error z
            | Correct distNamesList ->
              correct (
               {cr_cert_types = certTypeList;
                cr_sig_algorithms = None;
                cr_certificate_authorities = distNamesList})
          end // match pv
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Certificate Request message is too short")
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "empty certificate_types in Certificate Request")
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Certificate Request message is too short")

let mk_certificateRequestBytes sign cs version =
  certificateRequestBytes (
    {cr_cert_types = defaultCertTypes sign cs;
     cr_sig_algorithms =
       (match version with
        | TLS_1p2 -> Some (default_signatureScheme version cs)
        | _ -> None);
     cr_certificate_authorities = []})

let parseCertificateRequest13 (body:bytes): result cr13 = error "Certificate requests not yet implemented"

(** A.4.3 Client Authentication and Key Exchange Messages *)

open CoreCrypto

let kex_c_of_dh_key #g kex =
  if CommonDH.is_ec g then
    KEX_C_ECDHE (CommonDH.serialize_raw #g kex)
  else
    KEX_C_DHE (CommonDH.serialize_raw #g kex)

(* JK: TODO: add the kex as an extra parameter, otherwise not injective *)
val clientKeyExchangeBytes: cke -> Tot (b:bytes{hs_msg_bytes HT_client_key_exchange b})
let clientKeyExchangeBytes cke =
  let kexB =
    match cke.cke_kex_c with
    | KEX_C_DHE b -> (
      lemma_repr_bytes_values (length b);
      lemma_vlbytes_len 2 b;
      lemma_repr_bytes_values (length (vlbytes 2 b));
      vlbytes 2 b )
    | KEX_C_ECDHE b -> (
      lemma_repr_bytes_values (length b);
      lemma_vlbytes_len 1 b;
      lemma_repr_bytes_values (length (vlbytes 1 b));
      vlbytes 1 b)
    // | SSL_3p0,KEX_C_RSA(encpms) -> (lemma_repr_bytes_values (length encpms); encpms)
    | KEX_C_RSA(encpms) -> (
      lemma_repr_bytes_values (length encpms);
      lemma_vlbytes_len 2 encpms;
      lemma_repr_bytes_values (length (vlbytes 2 encpms));
      vlbytes 2 encpms )
    | KEX_C_DH -> (
      lemma_repr_bytes_values (length empty_bytes);
      empty_bytes) in
  lemma_repr_bytes_values (length kexB);
  messageBytes HT_client_key_exchange kexB

val clientKeyExchangeBytes_is_injective: cke1:cke -> cke2:cke ->
  Lemma (Bytes.equal (clientKeyExchangeBytes cke1) (clientKeyExchangeBytes cke2) ==> cke1 = cke2)
let clientKeyExchangeBytes_is_injective cke1 cke2 =
  admit(); // JK: TODO, see comment above
  if clientKeyExchangeBytes cke1 = clientKeyExchangeBytes cke2 then (
    ()
  ) else ()

(* val parseClientKeyExchange: p:protocolVersion -> kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} ->  *)
(*     Tot (result (cke:cke{Bytes.equal (clientKeyExchangeBytes p cke) (messageBytes HT_client_key_exchange b)})) *)
val parseClientKeyExchange: kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} -> Tot (result cke)
let parseClientKeyExchange kex data =
  match kex with
  | Kex_DH ->
      if length data = 0
      then Correct({cke_kex_c = KEX_C_DH})
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | Kex_DHE ->
      if length data >= 2
      then (match vlparse 2 data with
           | Error(z) -> Error(z)
           | Correct(y) -> (lemma_repr_bytes_values (length y); Correct({cke_kex_c = KEX_C_DHE y})))
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | Kex_ECDHE ->
      if length data >= 1
      then (match vlparse 1 data with
           | Error(z) -> Error(z)
           | Correct(y) -> (lemma_repr_bytes_values (length y); Correct({cke_kex_c = KEX_C_ECDHE y})))
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
//  | SSL_3p0,Kex_RSA ->
//      if length data < 4096 then
//         (lemma_repr_bytes_values (length data); Correct({cke_kex_c = KEX_C_RSA data}))
//      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | Kex_RSA  ->
        if length data >= 2 then
            match vlparse 2 data with
            | Correct (encPMS) ->
        if length encPMS < 4096 then (lemma_repr_bytes_values (length encPMS); correct({cke_kex_c = KEX_C_RSA encPMS}))
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
            | Error(z) -> Error(z)
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

(* Signature *)

val signatureBytes: signature -> b:bytes{length b < 65540}
let signatureBytes sig =
  lemma_repr_bytes_values (length sig.sig_signature);
  let sig_bytes = vlbytes2 sig.sig_signature in
  match sig.sig_algorithm with
  | None -> sig_bytes
  | Some sigalg ->
    let sig_algorithm_bytes = signatureSchemeBytes sigalg in
    sig_algorithm_bytes @| sig_bytes

val signatureBytes_is_injective: sig1:signature -> sig2:signature ->
  Lemma (requires (None? sig1.sig_algorithm == None? sig2.sig_algorithm))
  (ensures (Bytes.equal (signatureBytes sig1) (signatureBytes sig2) ==> sig1 == sig2))
let signatureBytes_is_injective sig1 sig2 =
  if signatureBytes sig1 = signatureBytes sig2 then
    begin
    lemma_repr_bytes_values (length sig1.sig_signature);
    lemma_repr_bytes_values (length sig2.sig_signature);
    match sig1.sig_algorithm, sig2.sig_algorithm with
    | None, None -> lemma_vlbytes_inj 2 sig1.sig_signature sig2.sig_signature
    | Some sigalg1, Some sigalg2 ->
      begin
      //TODO bytes NS 09/27
      // lemma_append_inj (signatureSchemeBytes sigalg1)
      //                  (vlbytes2 sig1.sig_signature)
      //                  (signatureSchemeBytes sigalg2)
      //                  (vlbytes2 sig2.sig_signature);
      signatureSchemeBytes_is_injective sigalg1 sigalg2;
      lemma_vlbytes_inj 2 sig1.sig_signature sig2.sig_signature
      end
    end

val parseSignature: pv:protocolVersion -> data:bytes -> result (sig:signature{Bytes.equal (signatureBytes sig) data})
let parseSignature pv data =
  if pv `geqPV` TLS_1p2 then
    if length data >= 4 then
      let alg, sig = split data 2ul in
      match parseSignatureScheme alg with
      | Correct sigalg ->
        begin
        match vlparse 2 sig with
        | Correct sigv ->
          lemma_repr_bytes_values (length sigv);
          Correct ({sig_algorithm = Some sigalg; sig_signature = sigv})
        | _ ->
          Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Signature: incorrect signature length")
        end
      | Error _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Signature: invalid signature scheme")
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Signature: message too short")
  else
    if length data >= 2 then
      match vlparse 2 data with
      | Correct sigv ->
        lemma_repr_bytes_values (length sigv);
        Correct ({sig_algorithm = None; sig_signature = sigv})
      | _ ->
        Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Signature: incorrect signature length")
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Signature: message too short")


(* ServerKeyExchange *)

open CoreCrypto

let kex_s_to_bytes kex =
  admit(); // JK: TODO
  match kex with
  | KEX_S_DHE (|g, k|) -> CommonDH.serialize #g k
  | KEX_S_RSA pk -> (*TODO: Ephemeral RSA*) empty_bytes

(* JK: TODO, or rewrite the functions altogether *)
assume val commonDH_serialize_is_injective: #g:CommonDH.group -> k1:CommonDH.pre_share g -> k2:CommonDH.pre_share g ->
  Lemma (requires True)
  (ensures (Bytes.equal (CommonDH.serialize k1) (CommonDH.serialize k2) ==> k1 == k2))

(* JK: TODO: missing the proper serialization for RSA so not injective for now *)
(* Actually false for now *)
assume val kex_s_to_bytes_is_injective: k1:kex_s -> k2:kex_s ->
  Lemma (requires True)
  (ensures (Bytes.equal (kex_s_to_bytes k1) (kex_s_to_bytes k2) ==> k1 == k2))

val serverKeyExchangeBytes: ske -> Tot (b:bytes{hs_msg_bytes HT_server_key_exchange b})
let serverKeyExchangeBytes ske =
  let kexB = kex_s_to_bytes ske.ske_kex_s in
  let sigB = signatureBytes ske.ske_signed_params in
  let payload = kexB @| sigB in
  lemma_repr_bytes_values (length payload);
  messageBytes HT_server_key_exchange payload

(* JK: TODO, currently not injective and missing an extra argument compared to the
   parsing function: the kex algorithm *)
assume val serverKeyExchangeBytes_is_injective: s1:ske -> s2:ske ->
  Lemma (requires True)
  (ensures (Bytes.equal (serverKeyExchangeBytes s1) (serverKeyExchangeBytes s2) ==> s1 == s2))
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
(*     Tot (result (s:ske{Bytes.equal (serverKeyExchangeBytes s) (messageBytes HT_server_key_exchange b)})) *)
val parseServerKeyExchange: pv:protocolVersion -> kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} -> result ske
let parseServerKeyExchange pv kex payload =
  match kex with
  | Kex_DHE ->
    begin
    match CommonDH.parse_partial false payload with
    | Correct (k, sigv) ->
      begin
      match parseSignature pv sigv with
      | Correct sig ->
        Correct ({ske_kex_s = KEX_S_DHE k; ske_signed_params = sig})
      | Error z -> Error z
      end
    | Error z -> Error z
    end
  | Kex_ECDHE ->
    begin
    match CommonDH.parse_partial true payload with
    | Correct (k, sigv) ->
      begin
      match parseSignature pv sigv with
      | Correct sig ->
        Correct ({ske_kex_s = KEX_S_DHE k; ske_signed_params = sig})
      | Error z -> Error z
      end
    | Error z -> Error z
    end
  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "ServerKeyExchange: Unexpected Key Exchange")


(* Certificate Verify *)

val certificateVerifyBytes: cv -> b:bytes{hs_msg_bytes HT_certificate_verify b}
let certificateVerifyBytes cv =
  let sigB = signatureBytes cv in
  lemma_repr_bytes_values (length sigB);
  messageBytes HT_certificate_verify sigB

val certificateVerifyBytes_is_injective: c1:cv -> c2:cv ->
  Lemma (requires (None? c1.sig_algorithm == None? c2.sig_algorithm))
  (ensures (Bytes.equal (certificateVerifyBytes c1) (certificateVerifyBytes c2) ==> c1 == c2))
let certificateVerifyBytes_is_injective c1 c2 =
  if certificateVerifyBytes c1 = certificateVerifyBytes c2 then
    begin
    let sig1 = signatureBytes c1 in
    let sig2 = signatureBytes c2 in
    lemma_repr_bytes_values (length sig1);
    lemma_repr_bytes_values (length sig2);
    signatureBytes_is_injective c1 c2;
    messageBytes_is_injective HT_certificate_verify sig1 HT_certificate_verify sig2
    end

val parseCertificateVerify: pv:protocolVersion -> data:bytes{repr_bytes(length data) <= 3} ->
  result (c:cv{Bytes.equal (certificateVerifyBytes c) (messageBytes HT_certificate_verify data)})
let parseCertificateVerify pv data =
  match parseSignature pv data with
  | Correct sig -> Correct sig
  | Error z -> Error z

val finishedBytes: fin -> Tot (b:bytes{hs_msg_bytes HT_finished b})
let finishedBytes fin =
  lemma_repr_bytes_values (length fin.fin_vd);
  messageBytes HT_finished fin.fin_vd

val finishedBytes_is_injective: f1:fin -> f2:fin ->
  Lemma (requires True)
  (ensures (Bytes.equal (finishedBytes f1) (finishedBytes f2) ==> f1 == f2))
let finishedBytes_is_injective f1 f2 =
  if finishedBytes f1 = finishedBytes f2 then (
    lemma_repr_bytes_values (length f1.fin_vd);
    lemma_repr_bytes_values (length f2.fin_vd);
    messageBytes_is_injective HT_finished f1.fin_vd HT_finished f2.fin_vd
  )

#reset-options

val parseFinished: data:bytes{repr_bytes(length data) <= 3} ->
  result(f:fin{Bytes.equal (finishedBytes f) (messageBytes HT_finished data)})
let parseFinished data =
  if length data < 65536 then Correct ({fin_vd = data}) else error "Finished too large"


(* Session ticket *)

val sessionTicketBytes: sticket -> Tot (b:bytes{hs_msg_bytes HT_session_ticket b})
let sessionTicketBytes t =
  let payload =
    bytes_of_int 4 (UInt32.v t.sticket_lifetime) @|
    (vlbytes 2 t.sticket_ticket) in
  lemma_repr_bytes_values (length payload);
  messageBytes HT_session_ticket payload

val sessionTicketBytes13: sticket13 -> Tot (b:bytes{hs_msg_bytes HT_session_ticket b})
let sessionTicketBytes13 t =
  let payload =
    bytes_of_int 4 (UInt32.v t.ticket13_lifetime) @|
    bytes_of_int 4 (UInt32.v t.ticket13_age_add) @|
    vlbytes 1 t.ticket13_nonce @|
    vlbytes 2 t.ticket13_ticket @|
    extensionsBytes t.ticket13_extensions in
  lemma_repr_bytes_values (length payload);
  messageBytes HT_session_ticket payload

(* TODO generalize, with adequate condition of s1 and s2:
val sessionTicketBytes_is_injective: p:protocolVersion -> s1:sticket -> s2:sticket ->
  Lemma (requires (p <> TLS_1p3))
  (ensures (Bytes.equal (sessionTicketBytes p s1) (sessionTicketBytes p s2) ==> s1 = s2))
let sessionTicketBytes_is_injective p s1 s2 =
  if sessionTicketBytes p s1 = sessionTicketBytes p s2 then (
    let payload1 = s1.sticket_lifetime @| s1.sticket_ticket in
    let payload2 = s2.sticket_lifetime @| s2.sticket_ticket in
    lemma_repr_bytes_values (length payload1);
    lemma_repr_bytes_values (length payload2);
    messageBytes_is_injective HT_session_ticket payload1 HT_session_ticket payload2;
    lemma_append_inj s1.sticket_lifetime s1.sticket_ticket s2.sticket_lifetime s2.sticket_ticket
  )
*)

val parseSessionTicket: b:bytes{repr_bytes(length b) <= 3} ->
  result (s:sticket {Bytes.equal (sessionTicketBytes s) (messageBytes HT_session_ticket b)})
let parseSessionTicket b =
  if length b < 6 then
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket: too short")
  else
    begin
    let lifetimeB, ticketB = split b 4ul in
    let lifetime = int_of_bytes lifetimeB in
    lemma_repr_bytes_values lifetime;
    let lifetime = UInt32.uint_to_t lifetime in
    match vlparse 2 ticketB with
    | Correct ticket ->
      Correct ({ sticket_lifetime = lifetime; sticket_ticket = ticket })
    | Error _ ->
      Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket: incorrect length")
    end

val parseSessionTicket13: b:bytes{repr_bytes(length b) <= 3} ->
  result (s:sticket13 {Bytes.equal (sessionTicketBytes13 s) (messageBytes HT_session_ticket b)})
let parseSessionTicket13 b =
  if length b < 12 then
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket13: too short")
  else
    begin
    let lifetimeB, rest = split b 4ul in
    let lifetime = int_of_bytes lifetimeB in
    lemma_repr_bytes_values lifetime;
    let lifetime = UInt32.uint_to_t lifetime in
    let ageB, rest = split rest 4ul in
    let age = int_of_bytes ageB in
    lemma_repr_bytes_values age;
    let age = UInt32.uint_to_t age in
    match vlsplit 1 rest with
    | Error _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket13: invalid nonce (check draft version 21 or greater)")
    | Correct(x) ->
      let nonce, rest = x in
      begin
        match vlsplit 2 rest with
        | Correct (x) ->
          let ticket, rest = x in
          begin
          match vlsplit 2 rest with
          | Correct (x) ->
            let exts, eof = x in
            if length eof > 0 then
              Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket13: dangling bytes")
            else
              begin
              match parseExtensions EM_NewSessionTicket (vlbytes 2 exts) with
              | Correct (exts,None) ->
                Correct ({ ticket13_lifetime = lifetime;
                           ticket13_age_add = age;
                           ticket13_nonce = nonce;
                           ticket13_ticket = ticket;
                           ticket13_extensions = exts})
              | Error _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket13: invalid extensions")
              end
          | Error _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket13: incorrect length")
          end
        | Error _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "NewSessionTicket13: incorrect length")
        end
      end


(* Hello retry request *)
val helloRetryRequestBytes: hrr -> Tot (b:bytes{hs_msg_bytes HT_hello_retry_request b})
let helloRetryRequestBytes hrr =
  serverHelloBytes ({
    sh_protocol_version = TLS_1p2;
    sh_server_random = bytes_of_hex "cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c";
    sh_sessionID = hrr.hrr_sessionID;
    sh_cipher_suite = hrr.hrr_cipher_suite;
    sh_compression = NullCompression;
    sh_extensions = Some hrr.hrr_extensions
  })
  (*
  let pvb = versionBytes hrr.hrr_protocol_version in
  let csb = cipherSuiteBytes hrr.hrr_cipher_suite in
  let extb = extensionsBytes hrr.hrr_extensions in
  let data = pvb @| csb @| extb in
  lemma_repr_bytes_values (length data);
  messageBytes HT_hello_retry_request data
  *)

val helloRetryRequestBytes_is_injective: h1:hrr -> h2:hrr ->
  Lemma (requires True)
  (ensures (Bytes.equal (helloRetryRequestBytes h1) (helloRetryRequestBytes h2) ==> h1 == h2))
let helloRetryRequestBytes_is_injective h1 h2 = admit()
(*
  if helloRetryRequestBytes h1 = helloRetryRequestBytes h2 then (
    let pv1 = versionBytes h1.hrr_protocol_version in
    let cs_bytes1 = cipherSuiteBytes h1.hrr_cipher_suite in
    let exts1 = extensionsBytes h1.hrr_extensions in
    let pv2 = versionBytes h2.hrr_protocol_version in
    let cs_bytes2 = cipherSuiteBytes h2.hrr_cipher_suite in
    let exts2 = extensionsBytes h2.hrr_extensions in
    let data1 = pv1 @| cs_bytes1 @| exts1 in
    lemma_repr_bytes_values (length data1);
    let data2 = pv2 @| cs_bytes2 @| exts2 in
    lemma_repr_bytes_values (length data2);
    messageBytes_is_injective HT_hello_retry_request data1 HT_hello_retry_request data2;
    //TODO bytes NS 09/27
    // lemma_append_inj pv1 (cs_bytes1 @| exts1) pv2 (cs_bytes2 @| exts2);
    // lemma_append_inj cs_bytes1 exts1 cs_bytes2 exts2;
    versionBytes_is_injective h1.hrr_protocol_version h2.hrr_protocol_version;
    cipherSuiteBytes_is_injective h1.hrr_cipher_suite h2.hrr_cipher_suite;
    extensionsBytes_is_injective h1.hrr_extensions h2.hrr_extensions
  )
*)

(* TODO: inversion lemmas *)
val parseHelloRetryRequest: bytes -> Tot (result hrr)
let parseHelloRetryRequest b = Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "HRR message type is disabled since draft 22")
(*
  if length b >= 4 then
    let pv, cs, data = split2 b 2 2 in
    (match TLSConstants.parseVersion pv with
    | Correct(pv) ->
      (match parseCipherSuite cs with
      | Correct(cs) ->
        (match parseExtensions EM_HelloRetryRequest data with
        | Correct(exts, None) ->
          if List.Tot.length exts < 256 then
            Correct ({
              hrr_protocol_version = pv;
              hrr_cipher_suite = cs;
              hrr_extensions = exts; })
          else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong hello retry request format")
        | Error(z) -> Error(z))
      | Error(z) -> Error(z))
    | Error(z) -> Error(z))
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong hello retry request format")
*)

(* Encrypted_extensions *)
let valid_ee : Type0 = msg:ee{repr_bytes (length (extensionsBytes msg)) <= 3}

val encryptedExtensionsBytes: e:valid_ee -> Tot (b:bytes{hs_msg_bytes HT_encrypted_extensions b})
let encryptedExtensionsBytes ee =
    let payload = extensionsBytes ee in
    messageBytes HT_encrypted_extensions payload

val encryptedExtensionsBytes_is_injective: e1:valid_ee -> e2:valid_ee ->
  Lemma (requires True)
  (ensures (Bytes.equal (encryptedExtensionsBytes e1) (encryptedExtensionsBytes e2) ==> e1 == e2))
let encryptedExtensionsBytes_is_injective e1 e2 =
  let payload1 = extensionsBytes e1 in
  let payload2 = extensionsBytes e2 in
  messageBytes_is_injective HT_encrypted_extensions payload1 HT_encrypted_extensions payload2;
  extensionsBytes_is_injective e1 e2

(* JK : TODO *)
assume val lemma_extensionsBytes_length: mt:ext_msg -> b:bytes ->
  Lemma (requires True)
  (ensures (
    match parseExtensions mt b with
    | Error _ -> True
    | Correct (ee, obinders) ->
    let len = match obinders with
      | Some binders -> length (bindersBytes binders)
      | _ -> 0 in
    length (extensionsBytes ee) + len == length b))

(* val parseEncryptedExtensions: b:bytes{repr_bytes(length b) <= 3} ->  *)
(*     Tot (result (s:valid_ee{Bytes.equal (encryptedExtensionsBytes s) (messageBytes HT_encrypted_extensions b)})) *)
val parseEncryptedExtensions: b:bytes{repr_bytes(length b) <= 3} ->
    Tot (result valid_ee)
let parseEncryptedExtensions payload  =
  match parseExtensions EM_EncryptedExtensions payload with
  | Error z -> Error z
  | Correct (exts,None) ->
    if List.Tot.length exts >= 256 then  error "too many extensions" else
    ( lemma_extensionsBytes_length EM_EncryptedExtensions payload;
      Correct exts)

(*
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
  Lemma (requires True)
  (ensures (Bytes.equal (nextProtocolBytes np1) (nextProtocolBytes np2) ==> np1 = np2))
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
    cut (Bytes.equal (Seq.slice selected_protocol1 0 1) (Seq.slice data1 0 1));
    cut (Bytes.equal (Seq.slice selected_protocol2 0 1) (Seq.slice data2 0 1));
    cut (Bytes.equal (Seq.slice selected_protocol2 0 1) (Seq.slice selected_protocol1 0 1));
    vlbytes_length_lemma 1 np1.np_selected_protocol np2.np_selected_protocol;
    lemma_append_inj selected_protocol1 padding1 selected_protocol2 padding2;
    lemma_vlbytes_inj 1 np1.np_selected_protocol np2.np_selected_protocol;
    lemma_vlbytes_inj 1 np1.np_padding np2.np_padding
  )

(* val parseNextProtocol: b:bytes{repr_bytes (length b) <= 3} ->  *)
(*     Tot (result (s:np{Bytes.equal (nextProtocolBytes s) (messageBytes HT_next_protocol b)})) *)
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
*)

val endOfEarlyDataBytes: b:lbytes 4{hs_msg_bytes HT_end_of_early_data b}
let endOfEarlyDataBytes =
  lemma_repr_bytes_values 0;
  messageBytes HT_end_of_early_data empty_bytes

val keyUpdateBytes: u:bool -> b:lbytes 5{hs_msg_bytes HT_key_update b}
let keyUpdateBytes u =
  lemma_repr_bytes_values 1;
  messageBytes HT_key_update (abyte (if u then 1z else 0z))

//FIXME: Implement CertificateRequest in TLS 1.3
val certificateRequestBytes13: cr13 -> b:lbytes 4{hs_msg_bytes HT_certificate_request b}
let certificateRequestBytes13 cr =
  lemma_repr_bytes_values 0;
  messageBytes HT_certificate_request empty_bytes

let handshakeMessageBytes pvo = function
  | ClientHello ch -> clientHelloBytes ch
  | ServerHello sh -> serverHelloBytes sh
  | Certificate c -> certificateBytes c
  | Certificate13 c -> certificateBytes13 c
  | ServerKeyExchange ske -> serverKeyExchangeBytes ske
  | ServerHelloDone -> serverHelloDoneBytes
  | ClientKeyExchange cke -> clientKeyExchangeBytes cke
  | Finished f -> finishedBytes f
  | NewSessionTicket t -> sessionTicketBytes t
  | NewSessionTicket13 t -> sessionTicketBytes13 t
  | EncryptedExtensions e -> encryptedExtensionsBytes e
  | CertificateRequest cr -> certificateRequestBytes cr
  | CertificateVerify cv -> certificateVerifyBytes cv
  | HelloRequest -> helloRequestBytes
  | HelloRetryRequest hrr -> helloRetryRequestBytes hrr
  | EndOfEarlyData -> endOfEarlyDataBytes
  | CertificateRequest13 cr -> certificateRequestBytes13 cr
  | KeyUpdate u -> keyUpdateBytes u
  // these two are not actual HS messages
  | Binders bs -> bindersBytes bs //
  | MessageHash h -> h // not


val splitHandshakeMessage: b:bytes{exists (ht:handshakeType). hs_msg_bytes ht b} ->
  t:(handshakeType * bytes)
    {repr_bytes (length (snd t)) <= 3 /\ b == (htBytes (fst t) @| (vlbytes 3 (snd t)))}
let splitHandshakeMessage b =
  let htbytes, payload = split b 1ul in
  let lenbytes,data = split payload 3ul in
  let ht = parseHt htbytes in
  assert(Correct? ht);
  match ht with
  | Correct ht ->
    inverse_ht ht;
    assert(Bytes.equal b (messageBytes ht data));
    (ht, data)

#reset-options "--z3rlimit 100"
//#set-options "--lax"

//17-05-05 update this proof, relying on pv to disambiguate messages with the same header
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
    | HT_certificate -> certificateBytes_is_injective (Certificate?._0 msg1) (Certificate?._0 msg2)
    | HT_server_key_exchange -> serverKeyExchangeBytes_is_injective (ServerKeyExchange?._0 msg1) (ServerKeyExchange?._0 msg2)
    | HT_server_hello_done -> ()
    | HT_client_key_exchange -> clientKeyExchangeBytes_is_injective (ClientKeyExchange?._0 msg1) (ClientKeyExchange?._0 msg2)
    | HT_finished -> finishedBytes_is_injective (Finished?._0 msg1) (Finished?._0 msg2)
    | HT_session_ticket -> admit() //17-05-05 TODO: sessionTicketBytes_is_injective (NewSessionTicket?._0 msg1) (NewSessionTicket?._0 msg2)
    | HT_encrypted_extensions -> encryptedExtensionsBytes_is_injective (EncryptedExtensions?._0 msg1) (EncryptedExtensions?._0 msg2)
    | HT_certificate_request -> certificateRequestBytes_is_injective (CertificateRequest?._0 msg1) (CertificateRequest?._0 msg2)
    | HT_certificate_verify -> certificateVerifyBytes_is_injective (CertificateVerify?._0 msg1) (CertificateVerify?._0 msg2)
    | HT_hello_request -> ()
    | HT_hello_retry_request -> helloRetryRequestBytes_is_injective (HelloRetryRequest?._0 msg1) (HelloRetryRequest?._0 msg2)
    (* | HT_server_configuration -> serverConfigurationBytes_is_injective (ServerConfiguration?._0 msg1) (ServerConfiguration?._0 msg2) *)
    //| HT_next_protocol -> nextProtocolBytes_is_injective (NextProtocol?._0 msg1) (NextProtocol?._0 msg2)
  )

let rec handshakeMessagesBytes pv = function
  | [] -> empty_bytes
  | h::t -> handshakeMessageBytes pv h @| handshakeMessagesBytes pv t

#reset-options

let lemma_handshakeMessagesBytes_def (pv:option protocolVersion) (li:list (msg:valid_hs_msg pv){Cons? li}) : Lemma (handshakeMessagesBytes pv li = ((handshakeMessageBytes pv (Cons?.hd li)) @| (handshakeMessagesBytes pv (Cons?.tl li)))) = ()

let lemma_handshakeMessagesBytes_def2 (pv:option protocolVersion) (li:list (msg:valid_hs_msg pv){Nil? li}) : Lemma (handshakeMessagesBytes pv li = empty_bytes) = ()

val lemma_handshakeMessageBytes_aux: pv:option protocolVersion -> msg1:valid_hs_msg pv -> msg2:valid_hs_msg pv ->
  Lemma (requires (let b1 = handshakeMessageBytes pv msg1 in
           let b2 = handshakeMessageBytes pv msg2 in
           length b2 >= length b1
           /\ Bytes.equal b1 (slice_ b2 0 (length b1))))
  (ensures (Bytes.equal (handshakeMessageBytes pv msg1) (handshakeMessageBytes pv msg2)))

#reset-options "--z3rlimit 50"
//#set-options "--lax"

let lemma_handshakeMessageBytes_aux pv msg1 msg2 = admit()
  //TODO bytes NS 09/27 : stale
  // let payload1 = handshakeMessageBytes pv msg1 in
  // let payload2 = handshakeMessageBytes pv msg2 in
  // let ht1, data1 = splitHandshakeMessage payload1 in
  // let ht2, data2 = splitHandshakeMessage payload2 in
  // cut (payload1 = (htBytes ht1 @| vlbytes 3 data1));
  // cut (payload2 = (htBytes ht2 @| vlbytes 3 data2));
  // cut (length payload1 >= 4 /\ length payload2 >= 4);
  // Seq.lemma_index_slice payload1 1 (length payload1) 0;
  // Seq.lemma_index_slice payload1 1 (length payload1) 1;
  // Seq.lemma_index_slice payload1 1 (length payload1) 2;
  // Seq.lemma_index_slice payload2 1 (length payload2) 0;
  // Seq.lemma_index_slice payload2 1 (length payload2) 1;
  // Seq.lemma_index_slice payload2 1 (length payload2) 2;
  // Seq.lemma_eq_intro (Seq.slice (vlbytes 3 data1) 0 3) (Seq.slice (vlbytes 3 data2) 0 3);
  // vlbytes_length_lemma 3 data1 data2;
  // cut (length (vlbytes 3 data1) = length (vlbytes 3 data2));
  // cut (length payload1 = length payload2);
  // Seq.lemma_eq_intro (Seq.slice payload2 0 (length payload1)) payload2;
  // lemma_append_inj (htBytes ht1) (vlbytes 3 data1) (htBytes ht2) (vlbytes 3 data2)

#reset-options

let lemma_aux_1 (a:bytes) (b:bytes) (c:bytes) (d:bytes) : Lemma
  (requires (Bytes.equal (a @| b) (c @| d)))
  (ensures ((length a >= length c ==> Bytes.equal (slice_ a 0 (length c)) c)
      /\ (length a < length c ==> Bytes.equal (slice_ c 0 (length a)) a)))
 = if length a >= length c then (
     cut (Bytes.equal (a @| b) (c @| d));
     cut (forall (i:nat). {:pattern (Bytes.index (a@|b) i) \/ (Bytes.index (c@|d) i)} i < length (a@|b) ==> Bytes.index (a@|b) i = Bytes.index (c@|d) i);
     cut (length a <= length (a@|b) /\ length c <= length (a@|b));
     ()
     )
   else (
     cut (Bytes.equal (a @| b) (c @| d));
     cut (forall (i:nat). {:pattern (Bytes.index (a@|b) i) \/ (Bytes.index (c@|d) i)} i < length (a@|b) ==> Bytes.index (a@|b) i = Bytes.index (c@|d) i);
     cut (length a <= length (a@|b) /\ length c <= length (a@|b));
     ()
  )

// let lemma_op_At_Bar_def (b:bytes) (b':bytes) : Lemma (requires True) (ensures ((b@|b') = Seq.append b b')) = ()

let lemma_handshakeMessageBytes_min_length (pv:option protocolVersion) (msg:valid_hs_msg pv) : Lemma (length (handshakeMessageBytes pv msg) >= 4) = ()

let lemma_aux_2 (pv:option protocolVersion) (l:list (msg:valid_hs_msg pv)) :
  Lemma (requires (Cons? l))
  (ensures (length (handshakeMessagesBytes pv l) > 0))
  = ()

let lemma_aux_3 (b:bytes) (b':bytes) : Lemma (requires (length b <> length b'))
              (ensures (~(Bytes.equal b b'))) = ()

let rec handshakeMessagesBytes_is_injective pv l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | hd::tl, hd'::tl' -> ();
      let payload1 = handshakeMessagesBytes pv l1 in
      lemma_handshakeMessagesBytes_def pv l1;
      cut (Bytes.equal ((handshakeMessageBytes pv hd) @| (handshakeMessagesBytes pv tl)) payload1);
      //TODO bytes NS 09/27 redundant
      // lemma_op_At_Bar_def (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl);
      let payload2 = handshakeMessagesBytes pv l2 in
      lemma_handshakeMessagesBytes_def pv l2;
      cut (Bytes.equal ((handshakeMessageBytes pv hd') @| (handshakeMessagesBytes pv tl')) payload2);
      //TODO bytes NS 09/27 redundant
      //lemma_op_At_Bar_def (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
      if payload1 = payload2 then (
  cut (Bytes.equal (Bytes.append (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl))
                   (Bytes.append (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl')));
  cut (Bytes.equal  ((handshakeMessageBytes pv hd)  @| (handshakeMessagesBytes pv tl))
                    ((handshakeMessageBytes pv hd') @| (handshakeMessagesBytes pv tl')));
  if length (handshakeMessageBytes pv hd) >= length (handshakeMessageBytes pv hd')
  then (
    lemma_aux_1 (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl) (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
    lemma_handshakeMessageBytes_aux pv hd' hd
    )
  else (
    lemma_aux_1 (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl) (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
    lemma_handshakeMessageBytes_aux pv hd hd'
  );
  //TODO bytes NS 09/27
  // lemma_append_inj (handshakeMessageBytes pv hd) (handshakeMessagesBytes pv tl) (handshakeMessageBytes pv hd') (handshakeMessagesBytes pv tl');
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

let string_of_handshakeMessage hs =
    match hs with
    | ClientHello ch -> "ClientHello"
    | ServerHello sh -> "ServerHello"
    | CertificateVerify cv -> "CertificateVerify"
    | Finished f -> "Finished"

    | ClientKeyExchange cke -> "ClientKeyExchange"
    | ServerKeyExchange ske -> "ServerKeyExchange"
    | ServerHelloDone -> "ServerHelloDone"
    | Certificate c -> "Certificate"
    | CertificateRequest cr -> "CertificateRequest"
    | HelloRequest -> "HelloRequest"
    | NewSessionTicket t -> "NewSessionTicket"

    | EndOfEarlyData -> "EndOfEarlyData"
    | EncryptedExtensions e -> "EncryptedExtensions"
    | Certificate13 c -> "Certificate13"
    | CertificateRequest13 cr -> "CertificateRequest13"
    | HelloRetryRequest hrr -> "HelloRetryRequest"
    | NewSessionTicket13 t -> "NewSessionTicket13"
    | KeyUpdate b -> "KeyUpdate"^(if b then "1" else "2")
    | Binders _ -> "Binders"
    | MessageHash _ -> "MessageHash"


let parseEmptyMessage v body =
  if length body = 0 then Correct v else error "non-empty body"

let parseBoolean (body: bytes): result bool =
  if body = abyte 1z then Correct true
  else if body = abyte 0z then Correct false
  else error "not a boolean"

let parseHandshakeMessage pv kex hstype body =
  if length body >= 16777216 then error "message too large" else
    begin
    lemma_repr_bytes_values (length body);
    match hstype,pv,kex with
    | HT_hello_request,_,_              -> parseEmptyMessage HelloRequest body
  //| HT_client_hello,_,_               -> mapResult ClientHello (parseClientHello body)
    | HT_server_hello,_,_               ->
      (match parseServerHello body with
      | Correct sh ->
        if sh.sh_server_random = bytes_of_hex "cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c" then
          Correct (HelloRetryRequest ({
            hrr_sessionID = sh.sh_sessionID;
            hrr_cipher_suite = sh.sh_cipher_suite;
            hrr_extensions = Some?.v (sh.sh_extensions)
          }))
        else Correct (ServerHello sh)
      | err -> error "failed to parse ServerHello/HRR")
    | HT_session_ticket, Some TLS_1p3,_ -> mapResult NewSessionTicket13 (parseSessionTicket13 body)
    | HT_session_ticket, Some _,_       -> mapResult NewSessionTicket (parseSessionTicket body)
    | HT_end_of_early_data, Some TLS_1p3,_ -> parseEmptyMessage EndOfEarlyData body
    | HT_hello_retry_request,_,_        -> mapResult HelloRetryRequest (parseHelloRetryRequest body)
    | HT_encrypted_extensions,_,_       -> mapResult EncryptedExtensions (parseEncryptedExtensions body)
    | HT_certificate, Some TLS_1p3,_    -> mapResult Certificate13 (parseCertificate13 body)
    | HT_certificate, Some _,_          -> mapResult Certificate (parseCertificate body)
    | HT_server_key_exchange,Some pv,Some kex -> mapResult ServerKeyExchange (parseServerKeyExchange pv kex body)
    | HT_certificate_request,Some TLS_1p3,_ -> mapResult CertificateRequest13 (parseCertificateRequest13 body)
    | HT_certificate_request,Some pv,_ -> mapResult CertificateRequest (parseCertificateRequest pv body)
    | HT_server_hello_done,_,_          -> parseEmptyMessage ServerHelloDone body
    | HT_certificate_verify,Some pv,_   -> mapResult CertificateVerify (parseCertificateVerify pv body)
    | HT_client_key_exchange,Some pv,Some kex -> mapResult ClientKeyExchange (parseClientKeyExchange kex body)
    | HT_finished,_,_                   -> mapResult Finished (parseFinished body)
    | HT_key_update,_,_                 -> mapResult KeyUpdate (parseBoolean body)
    | _                                 -> error "unexpected message"
    end

(**
This file implements type representations and parsing functions
for the different values negotiated during the TLS
handshake. For instance protocol version, key exchange mechanism,
hash algorithm etc.

@summary Module for main constants
*)
module TLSConstants

/// 18-09-08 contents & triage (beware of scopes)
/// - crypto ==> EverCrypt
/// - datatypes ==> QD
///    7% for signatures
///   53% for ciphersuites!
///   10% for certificates
/// - prf details ==> KeySchedule
/// - parsed extension contents ==> Extensions
/// - split Config (defaults are defined much later); align to EverCrypt
/// - callbacks + ad hoc string conversions ==> FFI ?

//18-02-27 not a reasonable default?
//#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

open FStar.Seq
open FStar.UInt32
open FStar.Bytes
open FStar.Error
open TLSError

open Mem
module Parse = Parse
//include Parse

(*
 * In the previous TLSConstants.fst, without the interface,
 * there was an admit_smt_queries true around line 310, and the rest of the
 * file eas verified with that (i.e. no reset-options after that
 *
 * The definitions below hence were already admitted
 *)
#set-options "--admit_smt_queries true"

let strongAuthAlg _ _ = admit ()  //AR: 04/08: was already assume val

let strongAuthAE _ _ = admit ()  //AR: 04/08: was already assume val

type cert_cb = {
  app_context : FStar.Dyn.dyn;
  (* Each callback takes an application context (app_context)
     and a function pointer to an application-provided functionality.

     The callback is actually performed in FFI.fst, which calls into ffi.c
     and takes care of marshalling miTLS parameters like signatureSchemeList
     to the types expected by the application.

     This explicit representation of closures is necessary for compiling this
     to C via KaRaMeL. The representation is hidden from callers and the wrappers
     are provided below to implement it.
   *)
  cert_select_ptr: FStar.Dyn.dyn;
  cert_select_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> pv:protocolVersion -> sni:bytes -> alpn:bytes -> sig:signatureSchemeList -> ST (option (cert_type * signatureScheme))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));

  cert_format_ptr: FStar.Dyn.dyn;
  cert_format_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> cert_type -> ST (list cert_repr)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));

  cert_sign_ptr: FStar.Dyn.dyn;
  cert_sign_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> cert_type -> signatureScheme -> tbs:bytes -> ST (option bytes)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));

  cert_verify_ptr: FStar.Dyn.dyn;
  cert_verify_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> list cert_repr -> signatureScheme -> tbs:bytes -> sigv:bytes -> ST bool
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));
}

let mk_cert_cb
    app_ctx
    cert_select_ptr
    cert_select_cb
    cert_format_ptr
    cert_format_cb
    cert_sign_ptr
    cert_sign_cb
    cert_verify_ptr
    cert_verify_cb = {
  app_context  = app_ctx;
  cert_select_ptr = cert_select_ptr;
  cert_select_cb = cert_select_cb;
  cert_format_ptr = cert_format_ptr;
  cert_format_cb = cert_format_cb;
  cert_sign_ptr = cert_sign_ptr;
  cert_sign_cb = cert_sign_cb;
  cert_verify_ptr = cert_verify_ptr;
  cert_verify_cb = cert_verify_cb
}

let cert_select_cb (c:config) (pv:protocolVersion) (sni:bytes) (alpn:bytes) (sig:signatureSchemeList)
   : ST (option (cert_type * signatureScheme))
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_select_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_select_ptr
            pv
            sni
            alpn
            sig

let cert_format_cb (c:config) (ct:cert_type)
   : ST (list cert_repr)
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_format_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_format_ptr
            ct

let cert_sign_cb (c:config) (ct:cert_type) (ss:signatureScheme) (tbs:bytes)
   : ST (option bytes)
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_sign_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_sign_ptr
            ct
            ss
            tbs

let cert_verify_cb (c:config) (cl:list cert_repr) (ss:signatureScheme) (tbs:bytes) (sigv:bytes)
   : ST bool
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_verify_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_verify_ptr
            cl
            ss
            tbs
            sigv

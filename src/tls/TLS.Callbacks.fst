module TLS.Callbacks 

open FStar.Bytes
open Mem 

include Parsers.ProtocolVersion 
include Parsers.ServerName
include Parsers.ProtocolName
include Parsers.ProtocolNameList
include Parsers.PskIdentity
include CipherSuite 

let context = FStar.Dyn.dyn
let default_context() = FStar.Dyn.mkdyn()

// just an example; should be defined by the verified application. 
let negotiated pv client_ext cookie r = True

let payload ct = admit()
let cert_selected pv sni alpn sig ct sa = True 
let cert_format ct = admit()
let cert_parse cc = admit()

noeq 
type cert_cb = {
  app_context:     context;
  cert_select_ptr: context;
  cert_select_cb:  context -> context -> cert_select_cb_fun;
  cert_format_ptr: context;
  cert_format_cb:  context -> context -> cert_format_cb_fun;
  cert_sign_ptr:   context;
  cert_sign_cb:    context -> context -> cert_sign_cb_fun;
  cert_verify_ptr: context;
  cert_verify_cb:  context -> context -> cert_verify_cb_fun;
}

[@"opaque_to_smt"]
inline_for_extraction
noextract
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

let cert_select_cb c pv sni alpn sig =
  c.cert_select_cb
    c.app_context
    c.cert_select_ptr
    pv sni alpn sig

let cert_format_cb c ct =
  c.cert_format_cb
    c.app_context
    c.cert_format_ptr
    ct

let cert_sign_cb c ct ss tbs = 
  c.cert_sign_cb
    c.app_context
    c.cert_sign_ptr
    ct ss tbs

let cert_verify_cb c cl ss tbs sigv =
  c.cert_verify_cb
    c.app_context
    c.cert_verify_ptr
    cl ss tbs sigv


val defaultServerNegoCBFun: context -> nego_cb_fun
let defaultServerNegoCBFun _ pv cext ocookie = Nego_accept []

let defaultServerNegoCB : nego_cb = {
  nego_context = default_context();
  negotiate = defaultServerNegoCBFun;
}



private let none6: context -> context -> cert_select_cb_fun = fun _ _ _ _ _ _ -> None
private let empty3: context -> context -> cert_format_cb_fun = fun _ _ _ -> []
private let none5: context -> context -> cert_sign_cb_fun = fun _ _ _ _ _ -> None
private let false6: context -> context -> cert_verify_cb_fun = fun _ _ _ _ _ _ -> false

let defaultCertCB_app_context     = default_context ()
let defaultCertCB_cert_select_ptr = default_context ()
let defaultCertCB_cert_format_ptr = default_context () 
let defaultCertCB_cert_sign_ptr   = default_context ()
let defaultCertCB_cert_verify_ptr = default_context ()
let defaultCertCB : cert_cb =
  mk_cert_cb
    defaultCertCB_app_context
    defaultCertCB_cert_select_ptr
    none6
    defaultCertCB_cert_format_ptr
    empty3
    defaultCertCB_cert_sign_ptr
    none5
    defaultCertCB_cert_verify_ptr
    false6

let defaultTicketCBFun _ sni ticket info psk =
  let h0 = get() in
  begin
  (*
  match info with
  | TicketInfo_12 (pv, cs, ems) ->
    // 2018.03.10 SZ: The ticket must be fresh
    assume False;
    s12_extend ticket (pv, cs, ems, psk) // modifies PSK.tregion
  | TicketInfo_13 pskInfo ->
    // 2018.03.10 SZ: Missing refinement in ticket_cb_fun
    assume (exists i.{:pattern index psk i} index psk i <> 0z);
    // 2018.03.10 SZ: The ticket must be fresh
    assume False;
    coerce_psk ticket pskInfo psk;      // modifies psk_region
    extend sni ticket                   // modifies PSK.tregion
  *) ()
  end;
  let h1 = get() in
  // 2018.03.10 SZ: [ticket_cb_fun] ensures [modifies_none]
  assume (modifies_none h0 h1)

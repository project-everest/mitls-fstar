open TLSConstants
open FStar_Dyn

open Ctypes
open PosixTypes
open Foreign

type bytes = FStar_Bytes.bytes

let mipki_chain = int64_t

(* mipki_state* MITLS_CALLCONV mipki_init(const mipki_config_entry config[],
                                          size_t config_len,
                                          password_callback pcb, int *erridx); *)
let mipki_init =
  foreign "mipki_init"
    (ptr void
     @-> size_t
     @-> ptr void
     @-> ptr int
     @-> returning (ptr void))

(* int MITLS_CALLCONV mipki_add_root_file_or_path(mipki_state *st, const char *ca_file); *)
let mipki_add_root_file_or_path =
  foreign "mipki_add_root_file_or_path"
    (ptr void
     @-> string
     @-> returning int)

(*
typedef struct {
  const char *cert_file;
  const char *key_file;

} mipki_config_entry;
*)
type mipki_config_entry
let mipki_config_entry : mipki_config_entry structure typ = structure "mipki_config_entry"
let cert_file    = field mipki_config_entry "cert_file"    string
let key_file     = field mipki_config_entry "key_file"     string
let is_universal = field mipki_config_entry "is_universal" bool
let () = seal mipki_config_entry

(* val init: cafile:string -> server_certs:list (string * string * bool) -> St FStar.Dyn.dyn *)
let init cafile server_certs =
  let open Unsigned.Size_t in
  let err_ptr = allocate Ctypes.int 0 in
  let len = List.length server_certs in

  let config = CArray.make mipki_config_entry len in
  for i = 0 to len-1 do
    let entry = Ctypes.make mipki_config_entry in
    let file, key, univ = List.nth server_certs i in
    setf entry cert_file file;
    setf entry key_file key;
    setf entry is_universal univ;
    CArray.set config i entry
  done;

  let pki = mipki_init (to_voidp (CArray.start config)) (of_int len) Ctypes.null err_ptr in

  if is_null pki then failwith "mipki_init";

  if String.length cafile > 0 then
    begin
    let ret = mipki_add_root_file_or_path pki cafile in
    if ret = 0 then failwith "mipki_add_root_file_or_path"
    end;

  mkdyn pki

type mipki_signature
let mipki_signature = Ctypes.uint16_t

(*
mipki_chain MITLS_CALLCONV mipki_select_certificate(mipki_state *st,
                                                    const char *sni,
                                                    const mipki_signature *algs,
                                                    size_t algs_len,
                                                    mipki_signature *selected) *)
let mipki_select_certificate =
  foreign "mipki_select_certificate"
    (ptr void
     @-> string
     @-> ptr mipki_signature
     @-> size_t
     @-> ptr mipki_signature
     @-> returning (ptr void))

(*
val cert_select:
  FStar_Dyn.dyn ->
  FStar_Dyn.dyn ->
  FStar_Bytes.bytes ->
  signatureSchemeList ->
  (cert_type * signatureScheme) FStar_Pervasives_Native.option
*)
let cert_select pki _ sni algs =
  let open Unsigned in
  let sigalgs_len = List.length algs in

  let sigalgs = CArray.make Ctypes.uint16_t sigalgs_len in
  List.iteri (fun i alg ->
      let pki_alg = alg |> TLSConstants.signatureSchemeBytes |> FStar_Bytes.int16_of_bytes in
      CArray.set sigalgs i (UInt16.of_int pki_alg)
    )
  algs;

  let sni = FStar_Bytes.string_of_bytes sni in
  let sel_ptr = allocate Ctypes.uint16_t (UInt16.of_int 0) in
  let chain = mipki_select_certificate (undyn pki) sni (CArray.start sigalgs) (Size_t.of_int sigalgs_len) sel_ptr in

  if is_null chain then FStar_Pervasives_Native.None
  else
    let FStar_Error.Correct sel =
      !@ sel_ptr
      |> UInt16.to_int
      |> FStar_Bytes.bytes_of_int16
      |> TLSConstants.parseSignatureScheme in
    let chain =
      chain
      |> raw_address_of_ptr
      |> Nativeint.to_string
      |> Int64.of_string in
    FStar_Pervasives_Native.Some (chain, sel)

let alloc_callback = ptr void @-> size_t @-> ptr (ptr char) @-> returning (ptr void)

let mipki_format_alloc =
  foreign "mipki_format_alloc"
    (ptr void
     @-> mipki_chain
     @-> ptr void
     @-> funptr alloc_callback
     @-> returning void)

(* val cert_format: FStar_Dyn.dyn -> FStar_Dyn.dyn -> cert_type -> cert_repr Prims.list *)
let cert_format pki _ chain =
  let open Unsigned.Size_t in
  let res: (char ptr * int) list ref = ref [] in
  let append _ len buf =
    let len = to_int len in
    let next = allocate_n char len in
    res := (next, len) :: !res;
    buf <-@ next;
    to_voidp buf
  in
  mipki_format_alloc (undyn pki) chain null append;
  List.map (fun (ptr, len) -> string_from_ptr ptr len) !res


type mipki_mode = MIPKI_SIGN | MIPKI_VERIFY
let of_int = function
  | 0 -> MIPKI_SIGN
  | 1 -> MIPKI_VERIFY
  | _ -> raise (Invalid_argument "Unexpected value for C enum")
let to_int = function
  | MIPKI_SIGN -> 0
  | MIPKI_VERIFY -> 1
let mipki_mode = Ctypes.view ~read:of_int ~write:to_int Ctypes.int

let mipki_sign =
  foreign "mipki_sign_verify"
    (ptr void
     @-> mipki_chain
     @-> mipki_signature
     @-> string
     @-> size_t
     @-> ptr char
     @-> ptr size_t
     @-> mipki_mode
     @-> returning int)

let max_signature_len = 8192

(*
val cert_sign_cb
 FStar_Dyn.dyn ->
 FStar_Dyn.dyn ->
 cert_type ->
 signatureScheme ->
 FStar_Bytes.bytes ->
 FStar_Bytes.bytes FStar_Pervasives_Native.option
*)
let cert_sign pki _ cert alg tbs =
  let open Unsigned.Size_t in
  let alg = alg |> TLSConstants.signatureSchemeBytes |> FStar_Bytes.int16_of_bytes |> Unsigned.UInt16.of_int in
  let tbs = FStar_Bytes.string_of_bytes tbs in
  let len = of_int (String.length tbs) in
  let signature = allocate_n char max_signature_len in
  let sig_len_ptr = allocate size_t (of_int max_signature_len) in
  let ret = mipki_sign (undyn pki) cert alg tbs len signature sig_len_ptr MIPKI_SIGN in
  if ret = 0 then
    FStar_Pervasives_Native.None (* failwith "mipki_sign_verify in MIPKI_SIGN mode"; *)
  else
    FStar_Pervasives_Native.Some
      (FStar_Bytes.bytes_of_string (string_from_ptr signature (to_int (!@ sig_len_ptr))))

let mipki_parse_list =
  foreign "mipki_parse_list"
    (ptr void
     @-> ptr string
     @-> ptr size_t
     @-> size_t
     @-> returning mipki_chain)

let mipki_validate_chain =
  foreign "mipki_validate_chain"
    (ptr void
     @-> mipki_chain
     @-> string
     @-> returning int)

let mipki_verify =
  foreign "mipki_sign_verify"
    (ptr void
     @-> mipki_chain
     @-> mipki_signature
     @-> string
     @-> size_t
     @-> string
     @-> ptr size_t
     @-> mipki_mode
     @-> returning int)
(*
val cert_verify:
  FStar_Dyn.dyn ->
  FStar_Dyn.dyn ->
  cert_repr Prims.list ->
  signatureScheme ->
  FStar_Bytes.bytes ->
  FStar_Bytes.bytes ->
  Prims.bool
*)
let cert_verify pki _ certs alg tbs signature =
  let open Unsigned.Size_t in
  let pki = undyn pki in
  let alg = alg
            |> TLSConstants.signatureSchemeBytes
            |> FStar_Bytes.int16_of_bytes
            |> Unsigned.UInt16.of_int in
  let tbs = FStar_Bytes.string_of_bytes tbs in
  let len = of_int (String.length tbs) in
  let signature = FStar_Bytes.string_of_bytes signature in
  let sig_len = String.length signature in
  let sig_len_ptr = allocate size_t (of_int sig_len) in
  let chain_len = of_int (List.length certs) in
  let ders = List.map FStar_Bytes.string_of_bytes certs in
  let lens = List.map (fun c -> of_int (String.length c)) ders in
  let ders = CArray.of_list string ders in
  let lens = CArray.of_list size_t lens in
  let chain = mipki_parse_list pki (CArray.start ders) (CArray.start lens) chain_len in
  let ret = mipki_verify pki chain alg tbs len signature sig_len_ptr MIPKI_VERIFY in
  (ret = 1)

(* val tls_callbacks: FStar.Dyn.dyn -> St cert_cb *)
let tls_callbacks ctxt = {
    app_context     = ctxt;
    cert_select_ptr = mkdyn ();
    cert_select_cb  = cert_select;
    cert_format_ptr = mkdyn ();
    cert_format_cb  = cert_format;
    cert_sign_ptr   = mkdyn ();
    cert_sign_cb    = cert_sign;
    cert_verify_ptr = mkdyn ();
    cert_verify_cb  = cert_verify
  }

(* void MITLS_CALLCONV mipki_free(mipki_state *st) *)
let mipki_free =
  foreign "mipki_free"
  (ptr void @-> returning void)

(* val free: FStar.Dyn.dyn -> St unit *)
let free pki =
  mipki_free (undyn pki)

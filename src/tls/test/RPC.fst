module RPC

open Mem
open Mem
open FStar.Monotonic.RRef
open FStar.Seq

open Platform.Bytes
open Platform.Error
open Platform.Tcp
open CoreCrypto

open Signature
open Formatting
open TLSConstants


type message = bytes

(* Two events, recording genuine requests and responses *)
assume new logic type requested: string -> Type
assume new logic type responded: string -> string -> Type

(* The meaning of signatures, as used in RPC *)
type reqresp (msg:message) =
    (exists s.   msg = Formatting.request s    /\ requested s)
  \/ (exists s t. msg = Formatting.response s t /\ responded s t)

let sigalg = RSASIG
let siglen = 2048/8
let hashalg = Hash SHA256
let algo = Signature.Use reqresp sigalg [hashalg] false false

type role =
  | Client
  | Server

type state (r:role) =
  | State:
      #region: rid{region <> root /\ region <> keyRegion}
    -> peer_region: rid{peer_region <> root /\ peer_region <> keyRegion /\ disjoint region peer_region}
    -> key: rref (if Client? r then peer_region else region) (skey algo)
    -> state r

type matching (r:state Client) (w:state Server) =
    r.region = w.peer_region
  /\ w.region = r.peer_region
  /\ r.key = w.key
  /\ disjoint (parent r.region) (parent w.region)

type both = state Client * state Server


(*-------------------------------------------------------------------*)
val init: client_parent:rid -> server_parent:rid -> All both
  (requires (fun h0 ->
      m_contains rkeys h0 /\
      disjoint client_parent server_parent))
  (ensures  (fun h0 (rw:result both) h1 ->
    V? rw ==>
     (let r,w = V.v rw in
       matching r w
     /\ modifies_one keyRegion h0 h1
     /\ modifies_rref keyRegion !{as_ref (as_rref rkeys)} h0 h1
     /\ m_contains rkeys h1
     /\ fresh_region r.region h0 h1
     /\ fresh_region w.region h0 h1
     /\ extends r.region client_parent
     /\ extends w.region server_parent
     /\ contains_ref w.key h1)
  ))
let init client_parent server_parent =
  let client_region = new_region client_parent in
  let server_region = new_region server_parent in
  let sk = Signature.gen algo in
  let key = ralloc server_region sk in
  let r = State #Client #client_region server_region key in
  let w = State #Server #server_region client_region key in
  r,w


(*-------------------------------------------------------------------*)
val client_send: networkStream -> client:state Client -> s:string16 -> All unit
  (requires (fun h0 ->
      m_contains rkeys h0
    /\ contains_ref client.key h0))
  (ensures  (fun h0 _ h1 ->
      modifies (Set.union (Set.singleton keyRegion)
			  (Set.singleton client.peer_region)) h0 h1
    /\ contains_ref client.key h1
    /\ m_contains rkeys h1
  ))
let client_send tcp client s =
  let _ = IO.debug_print_string "Client sends " in
  let _ = IO.debug_print_string (s ^ "\n") in
  let req = Formatting.request s in
  let sk = !client.key in
  assume (requested s);
  let signature = sign hashalg sk req in
  let _ = IO.debug_print_string "Signature " in
  let _ = IO.debug_print_string (print_bytes signature ^ "\n") in
  match send tcp ((utf8 s) @| signature) with
  | Correct _ -> ()
  | Error z -> failwith z


(*-------------------------------------------------------------------*)
val client_recv: networkStream -> client:state Client -> s:string16 -> All string
  (requires (fun h0 ->
      m_contains rkeys h0
    /\ contains_ref client.key h0))
  (ensures  (fun h0 t h1 ->
      modifies (Set.union (Set.singleton keyRegion)
			  (Set.singleton client.region)) h0 h1
    /\ contains_ref client.key h1
    /\ m_contains rkeys h1
    /\ (let pk,_ = sel h0 client.key in
	 V? t
       /\ int_cma algo hashalg
       /\ generated (algo,pk) h0
       /\ m_sel h0 (PK?.log pk) <> Corrupt ==> responded s (V.v t))
  ))
let client_recv tcp client s =
  match recv tcp (65535 + siglen) with
  | Correct msg ->
    begin
    let _ = IO.debug_print_string "Client receives " in
    let _ = IO.debug_print_string (print_bytes msg ^ "\n") in
    if length msg < siglen then failwith "Response is too short"
    else
      let v,signature = split msg (length msg - siglen) in
      let _ = IO.debug_print_string "Signature " in
      let _ = IO.debug_print_string (print_bytes signature ^ "\n") in
      match iutf8_opt v with
      | Some t ->
	  cut (utf8 t = v);
	  let pk,_ = !client.key in
	  if verify hashalg pk (Formatting.response s t) signature
          then
            let _ = IO.debug_print_string "Client verifies " in
	    let _ = IO.debug_print_string (t ^ "\n") in
	    t
          else failwith "Invalid signature"
      | None -> failwith "Received malformed response (non-UTF8)"
    end
  | Error z -> failwith "No response"


(*-------------------------------------------------------------------*)
val server_recv: networkStream -> server:state Server -> All string16
  (requires (fun h0 ->
      m_contains rkeys h0
    /\ contains_ref server.key h0))
  (ensures  (fun h0 s h1 ->
      modifies (Set.union (Set.singleton keyRegion)
			  (Set.singleton server.region)) h0 h1
    /\ contains_ref server.key h1
    /\ m_contains rkeys h1
    /\ (let pk,_ = sel h0 server.key in
	 V? s
       /\ int_cma algo hashalg
       /\ generated (algo,pk) h0
       /\ m_sel h0 (PK?.log pk) <> Corrupt ==> requested (V.v s))
  ))
let server_recv tcp server =
  match recv tcp (65535 + siglen) with
  | Correct msg ->
    begin
    let _ = IO.debug_print_string "Server receives " in
    let _ = IO.debug_print_string (print_bytes msg ^ "\n") in
    if length msg < siglen then failwith "Request is too short"
    else
      let v,signature = split msg (length msg - siglen) in
      let _ = IO.debug_print_string "Signature " in
      let _ = IO.debug_print_string (print_bytes signature ^ "\n") in
      match iutf8_opt v with
      | Some s ->
	  cut (utf8 s = v);
	  let pk,_ = !server.key in
	  if verify hashalg pk (Formatting.request s) signature
          then
            let _ = IO.debug_print_string "Server verifies " in
	    let _ = IO.debug_print_string (s ^ "\n") in
	    s
          else failwith "Invalid signature"
      | None -> failwith "Received malformed request (non-UTF8)"
    end
  | Error z -> failwith "No request"


(*-------------------------------------------------------------------*)
val server_send: networkStream -> server:state Server -> string16 -> string -> All unit
  (requires (fun h0 ->
      m_contains rkeys h0
    /\ contains_ref server.key h0))
  (ensures  (fun h0 s h1 ->
      modifies (Set.union (Set.singleton keyRegion)
			  (Set.singleton server.region)) h0 h1
    /\ contains_ref server.key h1
    /\ m_contains rkeys h1
  ))
let server_send tcp server s t =
  let _ = IO.debug_print_string "Server responds " in
  let _ = IO.debug_print_string (t ^ "\n") in
  let res = Formatting.response s t in
  let sk = !server.key in
  assume (responded s t);
  let signature = sign hashalg sk res in
  let _ = IO.debug_print_string "Signature " in
  let _ = IO.debug_print_string (print_bytes signature ^ "\n") in
  match send tcp ((utf8 t) @| signature) with
  | Correct _ -> ()
  | Error z -> failwith z


let start () =
  let client_parent = new_region root in
  let server_parent = new_region root in
  m_recall rkeys;
  init client_parent server_parent


val run: r:role -> state r -> string -> nat -> All unit
  (requires (fun h0 -> True))
  (ensures  (fun h0 _ h1 -> True))
let rec run role st host port =
  m_recall rkeys;
  recall st.key;
  match role with
  | Client ->
    let query = "4 + 2" in
    if length (utf8 query) > 65535 then failwith "UTF8 encoded request is too long"
    else
      let client_stream = connect host port in
      client_send client_stream st query;
      let _ = IO.input_line () in
      let t = client_recv client_stream st in
      let _ = IO.debug_print_string "---Client finished---\n" in
      ()
  | Server ->
    let server_socket = listen host port in
    let server_stream = accept server_socket in
    let h0 = ST.get () in
    let s = server_recv server_stream st in
    server_send server_stream st s ("Indeed, " ^ s);
    let _ = IO.debug_print_string "---Server finished---\n" in
    () //run Server st host port


(*
$FSTAR_HOME/bin/fstar.exe --universes --use_native_int --fstar_home $FSTAR_HOME --include $FSTAR_HOME/ucontrib/Platform/fst --include $FSTAR_HOME/ucontrib/CoreCrypto/fst --include $FSTAR_HOME/ulib/hyperheap --universes RPC.fst --codegen OCaml --lax --odir output

ocamlfind ocamlopt -package batteries,stdint,fileutils,sqlite3,zarith -linkpkg -g -thread -I $FSTAR_HOME/ulib/ml/native_int -I $FSTAR_HOME/ulib/ml/hyperheap -I $FSTAR_HOME/ulib/ml -I $FSTAR_HOME/ucontrib/Platform/ml -I $FSTAR_HOME/ucontrib/CoreCrypto/ml -I $FSTAR_HOME/ucontrib/CoreCrypto/ml/db $FSTAR_HOME/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa $FSTAR_HOME/ulib/ml/fstarlib-hyperheap.cmxa RPC.ml -o rpc.exe
*)

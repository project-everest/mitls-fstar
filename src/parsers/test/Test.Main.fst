module Test.Main
include Test.FinalExtensions

module LWP = LowParse.Writers.NoHoare.Combinators
module U32 = FStar.UInt32
module B = LowStar.Buffer


[@@ noextract_to "Kremlin"]
inline_for_extraction
noextract
let write_extensions1
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share inv))
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
  ()
: LWP.TWrite
    unit
    LWP.parse_empty
    Parsers.ClientHelloExtensions.lwp_clientHelloExtensions
    inv
=
  LWP.write_vllist_nil _ _;

  (* sni *)
  let peer_name = Parsers.MiTLSConfig.lwp_accessor_miTLSConfig_peer_name cfg in
  let peer_name_tag = Parsers.MiTLSConfig.lwp_miTLSConfig_peer_name_accessor_tag peer_name in
  let peer_name_tag = LWP.deref Parsers.Boolean.boolean_reader peer_name_tag in
  LWP.ifthenelse_combinator (peer_name_tag = Parsers.Boolean.B_true)
    (fun _ -> LWP.extend_vllist_snoc_ho _ _ _ begin fun _ ->
    let peer_name = Parsers.MiTLSConfig.lwp_miTLSConfig_peer_name_accessor_b_true peer_name in
    Parsers.ClientHelloExtension.clientHelloExtension_server_name_lwriter (fun _ ->
      Parsers.ClientHelloExtension_CHE_server_name.clientHelloExtension_CHE_server_name_lwp_writer (fun _ ->
        LWP.write_vllist_nil _ _;
        LWP.extend_vllist_snoc_ho _ _ _ (fun _ -> 
          Parsers.ServerName.serverName_host_name_lwriter (fun _ ->        
            LWP.cat peer_name
          )
        );
        Parsers.ServerNameList.serverNameList_lwp_write ()
      )
    )
    end)
    (fun _ -> ());

  Parsers.ClientHelloExtensions.clientHelloExtensions_lwp_write ()

[@@ noextract_to "Kremlin"]
noextract
let write_extensions2 = write_extensions1

let write_extensions
  (inv: LWP.memory_invariant)
  (cfg: LWP.ptr Parsers.MiTLSConfig.lwp_miTLSConfig inv)
  (ks: option (LWP.ptr Parsers.ClientHelloExtension.lwp_clientHelloExtension_CHE_key_share inv))
  (edi: bool)
  (lri: LWP.lptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  (now: U32.t)
: Tot (LWP.extract_t _ (write_extensions2 inv cfg ks edi lri now))
= LWP.extract _ (write_extensions1 _ _ _ _ _ _)

let main () : Tot C.exit_code = C.EXIT_SUCCESS

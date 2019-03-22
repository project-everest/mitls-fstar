module Test.Parsers

open C.String
open FStar.Error
open FStar.HyperStack.ST
open LowStar.BufferOps
open Parsers

module B = FStar.Bytes
module LB = LowStar.Buffer
module LPL = LowParse.Low.Base

open FStar.Printf
open TLSError
open TLSConstants

// No need to verify test for now
#set-options "--admit_smt_queries true"

let discard _ : ST unit (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let bprint s = discard (FStar.IO.debug_print_string (s^"\n"))

let from_bytes (b:B.bytes{B.length b <> 0}) : StackInline (LB.buffer LPL.byte)
  (requires (fun h0 -> True))
  (ensures  (fun h0 buf h1 ->
    LB.(modifies loc_none h0 h1) /\
    LB.live h1 buf /\ LB.unused_in buf h0 /\
    LB.length buf = B.length b /\
    B.reveal b `Seq.equal` LB.as_seq h1 buf))
  =
  let h0 = get () in
  let len = FStar.UInt32.uint_to_t (B.length b) in
  let lb = LB.alloca 0uy len in
  FStar.Bytes.store_bytes b lb;
  let h1 = get () in
  LB.(modifies_only_not_unused_in loc_none h0 h1);
  lb

let test_clientHello () : St bool =
  (* From Chrome 70 *)
  let chb = B.bytes_of_hex "0303c4168caa4297df69306988b842fe1f62f7cf07dcb2ad03aeb0012eae4b84e3cc203b03c8b3c20860716b6d8c405a9f64306ae660c77a51fe01f7c7c8f301458c9a00228a8a130113021303c02bc02fc02cc030cca9cca8c013c014009c009d002f0035000a010001914a4a0000ff010001000000000e000c0000096c6f63616c686f73740017000000230000000d00140012040308040401050308050501080606010201000500050100000000001200000010000e000c02683208687474702f312e3175500000000b000201000033002b00294a4a000100001d00209aad9849cf973510294b18ad9dfbcce2ee087b21276ba16f89570254796dcb75002d00020101002b000b0a9a9a0304030303020301000a000a00084a4a001d00170018001b00030200025a5a000100001500cb0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" in
  print !$" - ClientHello (intermediate)\n";
  let b =
    match ClientHello.clientHello_parser32 chb with
    | None -> bprint " failed to parse CH!\n"; false
    | Some (ch, len) ->
      if B.len chb <> len then
	(print !$"leftover bytes after parsing!\n"; false)
      else
	if ClientHello.clientHello_serializer32 ch <> chb then
	(print !$"roundtrip serialization failed!\n"; false)
	else
          (print !$"  + Roundtrip serialization matches!\n"; true)
    in
  print !$" - ClientHello (low-level)\n";
  let b' =
    let open FStar.UInt32 in
    let lb = from_bytes chb in
    let slice = LPL.make_slice lb (B.len chb) in
    if ClientHello.clientHello_validator slice 0ul >^ LPL.validator_max_length then
      (print !$"Validator failed on ClientHello!\n"; false)
    else
      let pos_random = ClientHello.accessor_clientHello_random slice 0ul in
      let p_random = LB.sub lb pos_random 32ul in
      bprint (sprintf " Read client_random: %s" (B.hex_of_bytes (B.of_buffer 32ul p_random)));
      true
    in
  b && b'

let test_Certificate13 () : St bool =
  let b =
    let open HandshakeMessages in
    let open Parsers.CertificateEntry13 in
    let open Parsers.CertificateExtension in
    let open Parsers.CertificateStatus in
    let open Parsers.CertificateStatusType in
    let ext = CE_status_request ({status_type = Ocsp; response = B.bytes_of_hex "00"}) in
    let cert1 = { cert_data = B.bytes_of_hex "3003000000"; extensions = [ext] } in
    let cert2 = { cert_data = B.bytes_of_string "hello world"; extensions = [] } in
    let m = { crt_request_context = B.empty_bytes; crt_chain13 = [cert1; cert2] } in
    let b = handshakeMessageBytes (Some TLS_1p3) (Certificate13 m) in
    bprint (sprintf " - Certificate13 test: %s\n" (B.hex_of_bytes b));
    match parseMessage b with
    | Error z -> bprint (" Parsing error: "^string_of_error z); false
    | Correct None -> bprint " Message not fully parsed!\n"; false
    | Correct (Some (| rem, hst, payload, _ |)) -> bprint " Roundtrip OK!\n"; true
    in
  let b' = 
    let open Parsers.Handshake13 in
    let open Parsers.Certificate13 in
    let open Parsers.CertificateEntry13 in
    let crt = B.bytes_of_hex "0b0005660000056200055d3082055930820441a0030201020212037361994ce91e0c760625b8bb58f816e809300d06092a864886f70d01010b0500304a310b300906035504061302555331163014060355040a130d4c6574277320456e6372797074312330210603550403131a4c6574277320456e637279707420417574686f72697479205833301e170d3139303131393135353031375a170d3139303431393135353031375a301b31193017060355040313107365637572652e6d6178672e696e666f30820122300d06092a864886f70d01010105000382010f003082010a0282010100c5a2d39f5d69aaeacbf69f458e4c68749d76bd962f4dca0ca7d90b1e4b3735d5eaa85139afdf866d7824c0d4909ccf346a3319880b77ff6b81b64f1ee869c644d72ec99aa0ca6ba63b7877e7566e7f5c71cb2ce9399088f7e77dd91046d8f5da5551e2820775d54f8c08181ec27c5d6f6cd8967a274b82d8aa967c477f927640414f7e9dab426833c80dec4f790a716823290b4a3a70531d3387eb8ab71580146597b5416c5a58368011edbfecd47963a7ea349a9d4eb5c10022e4486fff85fa884e665836d062386fdc0f8391d4b7f086ff3274c7b90fd84b7121e0ba4e78a0670520fdae2a172112e7586c10dc4c1609c04d455eed86ef76403b20c2564e850203010001a382026630820262300e0603551d0f0101ff0404030205a0301d0603551d250416301406082b0601050507030106082b06010505070302300c0603551d130101ff04023000301d0603551d0e041604147e687f0c2c93e052847ca3faa733563c70a2d56e301f0603551d23041830168014a84a6a63047dddbae6d139b7a64565eff3a8eca1306f06082b0601050507010104633061302e06082b060105050730018622687474703a2f2f6f6373702e696e742d78332e6c657473656e63727970742e6f7267302f06082b060105050730028623687474703a2f2f636572742e696e742d78332e6c657473656e63727970742e6f72672f301b0603551d110414301282107365637572652e6d6178672e696e666f304c0603551d20044530433008060667810c0102013037060b2b0601040182df130101013028302606082b06010505070201161a687474703a2f2f6370732e6c657473656e63727970742e6f726730820105060a2b06010401d6790204020481f60481f300f1007700747eda8331ad331091219cce254f4270c2bffd5e422008c6373579e6107bcc5600000168670528550000040300483046022100a8d5e22e20592c705762f5d194f1d705ff6949eb6fed08ed6bf49cfc0676ccd2022100e309718110ec3e1c077d212f1f2a227d86bf98cb79e8db360b7a600c6fce3ad4007600293c519654c83965baaa50fc5807d4b76fbf587a2972dca4c30cf4e54547f4780000016867052a50000004030047304502200e8663a2226cf2c675b006b3361c6b692804245f56eb52c3a0d9ac3be3d755cb022100ea4233befb67b31631d28a33fa5878478f22f77a8129a9e110baf8781c4a8477300d06092a864886f70d01010b05000382010100238009368ec903cb5234b12a2bd42d83d2d49d9a2f94f7e1e08709e1cb841a094c61ab92d6dab33697127616e1e2a45f26be6e1ce4c11354ea2a8e4f02b92b41725bc62e734978e1a9d12e2ab9850885cbe7cc04e95b7538d9352f912b61ddab9dd9ffa4cd49f5caacbe820aac06e04206563c0887866a35b05ad11e91b3f7231aa87f8f299ba9453f8ff195f630729379d00a8df2d8d2757fa4fab28218e0ecce364e790b675398fbf09a66cb8a707aed2eafa87dc27be0a41b4ba2d26097ba352e03da7a3dce0adf1ffeac585deac5991a29ab6696375d654a6bf27834f0e95b515b417bd856069ec2632abcfff2f6b108ff030055ee1df897d45e881828ed0000" in
    match handshake13_parser32 crt with
    | Some (M_certificate ({certificate_request_context = ctx; certificate_list = cl}),l) ->
      if B.len crt = l then
        (bprint (sprintf " Parsed %d certificates, context %s!\n" (List.Tot.length cl) (B.hex_of_bytes ctx)); true)
      else
        (bprint "dangling bytes after certificate message"; false)
    | None -> bprint (" failed to pare certificate chain!"); false
    in
  let b'' =
    let open Parsers.Handshake13 in
    let open Parsers.HandshakeType in
    let sf = B.bytes_of_hex "080000160014000a0010000e00190018001d00170102010101000b0002350000023100022c30820228308201cfa003020102020101300906072a8648ce3d0401308180310b3009060355040613024343310e300c06035504080c0553746174653111300f06035504070c084c6f636174696f6e31153013060355040a0c0c4f7267616e697a6174696f6e3118301606035504030c0f65636473612e6d69746c732e6f7267311d301b06092a864886f70d010901160e726f6f74406d69746c732e6f7267301e170d3137303332343232353035315a170d3235303631303232353035315a3072310b3009060355040613024343310e300c06035504080c05537461746531153013060355040a0c0c4f7267616e697a6174696f6e311d301b06035504030c1465636473612e636572742e6d69746c732e6f7267311d301b06092a864886f70d010901160e726f6f74406d69746c732e6f72673059301306072a8648ce3d020106082a8648ce3d03010703420004f90d50c1922e61ab3f89b27346b7b5a1a7688ef984021e7cc9105573c56e82777d8d80cb7832cb7b29956b0be8646d8a9cc81519a52f9aa0156183940fded8d1a3483046300b0603551d0f0404030205e030090603551d1304023000302c06096086480186f842010d041f161d4f70656e53534c2047656e657261746564204365727469666963617465300906072a8648ce3d04010348003045022100eb918198af80353dcb307dbe685e132c72eeae38db8813450b61cbf83f5e5e060220530a62525ea87edb760792401b2e464947ad3a0a660aaf2f980529d4c5987be000000f00004b0203004730450220621aacba1ea6500747b0404072be6dc5b394a9e3a37fb8a22df8554220f0e4590221009cab81d07ded7a51b1c6a88eb652d9a48b4e8afe9fc8d1dca5a69c52fd4b70931400002086ebea331c7ce1b5893a5bf4d474d6a5af0cbdf0bf02123ee6994221562b5054" in
    match handshake13_parser32 sf with
    | None -> bprint "failed to parse 1st message of server flight.\n"; false
    | Some (msg, l) ->
      bprint ("Received "^(string_of_handshakeType (tag_of_handshake13 msg)));
      let (_, crt) = B.split sf l in
      match handshake13_parser32 crt with
      | None -> bprint "failed to parse 2nd message of server flight.\n"; false
      | Some (msg, l) ->
        bprint ("Received "^(string_of_handshakeType (tag_of_handshake13 msg)));
        let (_, cv) = B.split crt l in
	match handshake13_parser32 cv with
	| None -> bprint "failed to parse 3rd message of server flight.\n"; false
	| Some (msg, l) ->
          bprint ("Received "^(string_of_handshakeType (tag_of_handshake13 msg)));
          let (_, sf) = B.split cv l in
	  match handshake13_parser32 sf with
	  | None -> bprint "failed to parse 4th message of server flight.\n"; false
	  | Some (msg, l) ->
            bprint ("Received "^(string_of_handshakeType (tag_of_handshake13 msg)));
	    let (_, rem) = B.split sf l in
	    bprint (sprintf "%d bytes remaining in buffer: %s" (B.length rem) (B.hex_of_bytes rem));
	    true
    in
  b && b' && b''

// called from Test.Main
let main () : St C.exit_code =
  match test_clientHello () with
  | false ->
    print !$"ClientHello test failed.\n";
    C.EXIT_FAILURE
  | true ->
    print !$"ClientHello test succeeded.\n";
    match test_Certificate13 () with
    | false ->
      print !$"Certificate13 test failed.\n";
      C.EXIT_FAILURE
    | true ->
      print !$"Certificate13 test succeeded.\n";
      C.EXIT_SUCCESS

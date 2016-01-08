(*--build-config
    options: --z3timeout 100 --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --admit_fsi FStar.Seq --admit_fsi Fstar.Set --admit_fsi FStar.IO --admit_fsi CoreCrypto --verify_module TestGCM;

    variables: CONTRIB=../../../FStar/contrib;
    
    other-files: FStar.FunctionalExtensionality.fst classical.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst 
      map.fst listTot.fst hyperHeap.fst stHyperHeap.fst allHyperHeap.fst
      string.fst list.fst seq.fsi seqproperties.fst FStar.IO.fsti
      $CONTRIB/Platform/fst/Bytes.fst $CONTRIB/Platform/fst/Date.fst 
      $CONTRIB/Platform/fst/Error.fst $CONTRIB/Platform/fst/Tcp.fst
      $CONTRIB/CoreCrypto/fst/CoreCrypto.fst 
      $CONTRIB/CoreCrypto/fst/DHDB.fst 
      TLSError.fst Nonce.fst TLSConstants.fst RSAKey.fst DHGroup.p.fst 
      ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst 
      UntrustedCert.fst Cert.fst TLSInfo.fst Range.p.fst DataStream.fst Alert.fst 
      Content.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fst 
--*)
module TestGCM

(*
Code generation:

../../../FStar/bin/fstar.exe FStar.FunctionalExtensionality.fst classical.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst map.fst listTot.fst hyperHeap.fst stHyperHeap.fst allHyperHeap.fst string.fst list.fst seq.fst seqproperties.fst FStar.IO.fsti --admit_fsi Fstar.Set --admit_fsi FStar.IO --admit_fsi CoreCrypto --include ../../../FStar/contrib/Platform/fst/ --include ../../../FStar/contrib/CoreCrypto/fst Bytes.fst Date.fst Error.fst Tcp.fst CoreCrypto.fst DHDB.fst TLSError.fst Nonce.fst TLSConstants.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fst Cert.fst TLSInfo.fst Range.p.fst DataStream.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fst TestGCM.fst --codegen OCaml --codegen-lib CoreCrypto --codegen-lib Platform --lax --trace_error --use_native_int

Workarounds:

In DHGroup.ml:
- add type annotation: 
  let goodPP_log = (FStar_ST.alloc ([]:CoreCrypto.dh_params list))

In TLSInfo.ml:
- drop extracted assumed logic types
- Redefine safeKDF: let safeKDF = (fun i -> false)

Compilation (Mac OS X): 

Use the current implementation of DHDB (requires packages sqlite3 and fileutils)

ocamlfind ocamlopt -I ../../../FStar/lib/ml/hyperheap -I ../../../FStar/lib/ml/native_int -I ../../../FStar/lib/ml -I ../../../FStar/contrib/CoreCrypto/ml -I ../../../FStar/contrib/CoreCrypto/ml/db -I ../../../FStar/contrib/Platform/ml ../../../FStar/lib/ml/native_int/prims.ml ../../../FStar/contrib/Platform/ml/platform.ml ../../../FStar/contrib/CoreCrypto/ml/db/DB.ml ../../../FStar/contrib/CoreCrypto/ml/DHDB.ml ../../../FStar/contrib/CoreCrypto/ml/CoreCrypto.ml ../../../FStar/lib/ml/FStar_All.ml FStar_FunctionalExtensionality.ml FStar_Classical.ml ../../../FStar/lib/ml/FStar_Set.ml FStar_Map.ml ../../../FStar/lib/ml/FStar_List.ml ../../../FStar/lib/ml/hyperheap/FStar_ST.ml ../../../FStar/lib/ml/hyperheap/FStar_HyperHeap.ml FStar_Seq.ml FStar_SeqProperties.ml ../../../FStar/lib/ml/FStar_IO.ml TLSError.ml Nonce.ml TLSConstants.ml RSAKey.ml HASH.ml HMAC.ml ECGroup.ml DHGroup.ml CommonDH.ml Sig.ml UntrustedCert.ml Cert.ml PMS.ml TLSInfo.ml Range.ml DataStream.ml Content.ml StatefulPlain.ml LHAEPlain.ml AEAD_GCM.ml StatefulLHAE.ml TestGCM.ml -cc "gcc-5" -cclib -L../../../FStar/3rdparty/osx -cclib -lopenssl_wrap -cclib ../../../FStar/3rdparty/osx/libcrypto.a -package batteries -package sqlite3 -package fileutils -linkpkg -g -thread -o sample.exe

Or replace DHDB with dummy implementation DHDB.ml:

ocamlfind ocamlopt -I ../../../FStar/lib/ml/hyperheap -I ../../../FStar/lib/ml/native_int -I ../../../FStar/lib/ml -I ../../../FStar/contrib/CoreCrypto/ml -I ../../../FStar/contrib/Platform/ml ../../../FStar/lib/ml/native_int/prims.ml ../../../FStar/contrib/Platform/ml/platform.ml ../../../FStar/contrib/CoreCrypto/ml/db/DB.ml DHDB.ml ../../../FStar/contrib/CoreCrypto/ml/CoreCrypto.ml ../../../FStar/lib/ml/FStar_All.ml FStar_FunctionalExtensionality.ml FStar_Classical.ml ../../../FStar/lib/ml/FStar_Set.ml FStar_Map.ml ../../../FStar/lib/ml/FStar_List.ml ../../../FStar/lib/ml/hyperheap/FStar_ST.ml ../../../FStar/lib/ml/hyperheap/FStar_HyperHeap.ml FStar_Seq.ml FStar_SeqProperties.ml ../../../FStar/lib/ml/FStar_IO.ml TLSError.ml Nonce.ml TLSConstants.ml RSAKey.ml HASH.ml HMAC.ml ECGroup.ml DHGroup.ml CommonDH.ml Sig.ml UntrustedCert.ml Cert.ml PMS.ml TLSInfo.ml Range.ml DataStream.ml Content.ml StatefulPlain.ml LHAEPlain.ml AEAD_GCM.ml StatefulLHAE.ml TestGCM.ml -cc "gcc-5" -cclib -L../../../FStar/3rdparty/osx -cclib -lopenssl_wrap -cclib ../../../FStar/3rdparty/osx/libcrypto.a -package batteries -linkpkg -g -thread -o sample.exe
*)


open FStar.Heap
open FStar.HyperHeap
open FStar.IO

open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open StatefulPlain
open AEAD_GCM
open StatefulLHAE


let i = {noId with aeAlg = AEAD CoreCrypto.AES_256_GCM CoreCrypto.SHA256}

val ad: adata i
let ad = makeAD i Application_data

val clen: n:nat { valid_clen i n  }
let clen = 34

val rg: frange i
let rg = Range.cipherRangeClass i clen // point (clen - 8 - 16) = (10,10)

val text: rbytes rg
let text = Platform.Bytes.createBytes 10 70uy
//let text = Platform.Bytes.utf8 "Top secret"

val p: plain i ad rg
let p =
  assume (~(authId i)); 
  mk_plain i ad rg text

let both = gen FStar.HyperHeap.root i

val rd: reader i
let rd = fst both

val wr: writer i
let wr = snd both

let main =
  admit (); // TODO: prove invariants
  let c = encrypt #i #ad #rg wr p in
  print_string "Encrypted: "; 
  print_string (Platform.Bytes.iutf8 c);
  print_string "\n";
  let d = decrypt #i #ad rd c in
  match d with
  | Some p' -> 
    print_string "Decrypted: "; 
    print_string (Platform.Bytes.iutf8 (repr i ad rg p'));
    print_string "\n"
  | None -> failwith "Failure"

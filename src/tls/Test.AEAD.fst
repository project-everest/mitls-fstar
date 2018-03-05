module Test.AEAD

open FStar.HyperStack.ST
open FStar.HyperStack.IO

open FStar.Bytes
open CoreCrypto

let prefix = "Test.AEAD"
let print_string s = print_string (prefix ^ ": " ^ s ^ ".\n")

type vector = {
  cipher:    aead_cipher;
  key:       string;
  iv:        string;
  aad:       string;
  tag:       string;
  plaintext: string;
  ciphertext:string;
}

val test: vector -> St bool
let test v =
  let key = Bytes.bytes_of_hex v.key in
  let iv  = Bytes.bytes_of_hex v.iv in
  let aad = Bytes.bytes_of_hex v.aad in
  let plaintext = Bytes.bytes_of_hex v.plaintext in
  let ciphertext = Bytes.bytes_of_hex (v.ciphertext ^ v.tag) in
  assume (length key = aeadKeySize v.cipher);
  assume (length iv = aeadRealIVSize v.cipher);
  let encrypted = aead_encrypt v.cipher key iv aad plaintext in
  if encrypted <> ciphertext then
    begin
    print_string ("ERROR: encryption result doesn't match");
    print_string ("Expected:   " ^ (Bytes.hex_of_bytes ciphertext));
    print_string ("Decryption: " ^ (Bytes.hex_of_bytes encrypted));
    false
    end
  else
  match aead_decrypt v.cipher key iv aad ciphertext with
  | None ->
    begin
    print_string ("ERROR: decryption failed without producing a plaintext");
    false
    end
  | Some plain' ->
    if plain' = plaintext then true
    else
      begin
      print_string ("ERROR: the decrypted data doesn't match the encrypted data");
      print_string ("Key:        " ^ v.key);
      print_string ("IV:         " ^ v.iv);
      print_string ("AAD:        " ^ v.aad);
      print_string ("Tag:        " ^ v.tag);
      print_string ("Ciphertext: " ^ v.ciphertext);
      print_string ("Expected:   " ^ v.plaintext);
      print_string ("Decryption: " ^ (Bytes.hex_of_bytes plain'));
      false
      end

let test_vectors = [
  { (* rfc7539#page-22 *)
    cipher = CHACHA20_POLY1305;
    key = "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f";
    iv  = "070000004041424344454647";
    aad = "50515253c0c1c2c3c4c5c6c7";
    tag = "1ae10b594f09e26a7e902ecbd0600691";
    plaintext  = "4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e";
    ciphertext = "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116";
  };
  {
    cipher = CHACHA20_POLY1305;
    key = "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0";
    iv  = "000000000102030405060708";
    aad = "f33388860000000000004e91";
    tag = "eead9d67890cbb22392336fea1851f38";
    plaintext  = "496e7465726e65742d4472616674732061726520647261667420646f63756d656e74732076616c696420666f722061206d6178696d756d206f6620736978206d6f6e74687320616e64206d617920626520757064617465642c207265706c616365642c206f72206f62736f6c65746564206279206f7468657220646f63756d656e747320617420616e792074696d652e20497420697320696e617070726f70726961746520746f2075736520496e7465726e65742d447261667473206173207265666572656e6365206d6174657269616c206f7220746f2063697465207468656d206f74686572207468616e206173202fe2809c776f726b20696e2070726f67726573732e2fe2809d";
    ciphertext = "64a0861575861af460f062c79be643bd5e805cfd345cf389f108670ac76c8cb24c6cfc18755d43eea09ee94e382d26b0bdb7b73c321b0100d4f03b7f355894cf332f830e710b97ce98c8a84abd0b948114ad176e008d33bd60f982b1ff37c8559797a06ef4f0ef61c186324e2b3506383606907b6a7c02b0f9f6157b53c867e4b9166c767b804d46a59b5216cde7a4e99040c5a40433225ee282a1b0a06c523eaf4534d7f83fa1155b0047718cbc546a0d072b04b3564eea1b422273f548271a0bb2316053fa76991955ebd63159434ecebb4e466dae5a1073a6727627097a1049e617d91d361094fa68f0ff77987130305beaba2eda04df997b714d6c6f2c29a6ad5cb4022b02709b";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "58e2fccefa7e3061367f1d57a4e7455a";
    plaintext  = "";
    ciphertext = "";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "ab6e47d42cec13bdf53a67b21257bddf";
    plaintext  = "00000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78";
  };
  {
    cipher = AES_128_GCM;
    key = "feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "";
    tag = "4d5c2af327cd64a62cf35abd2ba6fab4";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985";
  };
  {
    cipher = AES_128_GCM;
    key = "feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "5bc94fbc3221a5db94fae95ae7121a47";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091";
  };
  {
    cipher = AES_256_GCM;
    key = "0000000000000000000000000000000000000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "530f8afbc74536b9a963b4f1c4cb738b";
    plaintext  = "";
    ciphertext = "";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "";
    tag = "b094dac5d93471bdec1a502270e3cc6c";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "";
    tag = "b094dac5d93471bdec1a502270e3cc6c";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "76fc6ece0f4e1768cddf8853bb2d551b";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
    tag = "5fea793a2d6f974d37e68e0cb8ff9492";
    plaintext  = "";
    ciphertext = "";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "9dd0a376b08e40eb00c35f29f9ea61a4";
    plaintext  = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "98885a3a22bd4742fe7b72172193b163";
    plaintext  = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0c94da219118e297d7b7ebcbcc9c388f28ade7d85a8ee35616f7124a9d5270291";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "cac45f60e31efd3b5a43b98a22ce1aa1";
    plaintext  = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0c94da219118e297d7b7ebcbcc9c388f28ade7d85a8ee35616f7124a9d527029195b84d1b96c690ff2f2de30bf2ec89e00253786e126504f0dab90c48a30321de3345e6b0461e7c9e6c6b7afedde83f40";
  };
  {
    cipher = AES_128_GCM;
    key = "843ffcf5d2b72694d19ed01d01249412";
    iv  = "dbcca32ebf9b804617c3aa9e";
    aad = "00000000000000000000000000000000101112131415161718191a1b1c1d1e1f";
    tag = "3b629ccfbc1119b7319e1dce2cd6fd6d";
    plaintext  = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f";
    ciphertext = "6268c6fa2a80b2d137467f092f657ac04d89be2beaa623d61b5a868c8f03ff95d3dcee23ad2f1ab3a6c80eaf4b140eb05de3457f0fbc111a6b43d0763aa422a3013cf1dc37fe417d1fbfc449b75d4cc5";
  };
  ]

let rec iter vs: St C.exit_code =
  match vs with
  | [] -> C.EXIT_SUCCESS
  | v :: vs -> if test v then iter vs else C.EXIT_FAILURE

// Called from Test.Main
let main () =
  iter test_vectors

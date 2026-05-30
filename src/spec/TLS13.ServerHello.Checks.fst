module TLS13.ServerHello.Checks

module B = TLS13.Bytes
module Seq = FStar.Seq

let server_hello_header_ok (input:B.bytes) : GTot bool =
  if B.length input == 90 then
    Seq.index input 0 = 0x02uy &&
    Seq.index input 1 = 0uy &&
    Seq.index input 2 = 0uy &&
    Seq.index input 3 = 0x56uy &&
    Seq.index input 4 = 0x03uy &&
    Seq.index input 5 = 0x03uy &&
    Seq.index input 38 = 0uy &&
    Seq.index input 39 = 0x13uy &&
    Seq.index input 40 = 0x03uy &&
    Seq.index input 41 = 0uy &&
    Seq.index input 42 = 0uy &&
    Seq.index input 43 = 0x2euy
  else false

let server_hello_is_hrr (input:B.bytes) : GTot bool =
  if B.length input == 90 then
    Seq.index input 6 = 0xcfuy &&
    Seq.index input 7 = 0x21uy &&
    Seq.index input 8 = 0xaduy &&
    Seq.index input 9 = 0x74uy &&
    Seq.index input 10 = 0xe5uy &&
    Seq.index input 11 = 0x9auy &&
    Seq.index input 12 = 0x61uy &&
    Seq.index input 13 = 0x11uy &&
    Seq.index input 14 = 0xbeuy &&
    Seq.index input 15 = 0x1duy &&
    Seq.index input 16 = 0x8cuy &&
    Seq.index input 17 = 0x02uy &&
    Seq.index input 18 = 0x1euy &&
    Seq.index input 19 = 0x65uy &&
    Seq.index input 20 = 0xb8uy &&
    Seq.index input 21 = 0x91uy &&
    Seq.index input 22 = 0xc2uy &&
    Seq.index input 23 = 0xa2uy &&
    Seq.index input 24 = 0x11uy &&
    Seq.index input 25 = 0x16uy &&
    Seq.index input 26 = 0x7auy &&
    Seq.index input 27 = 0xbbuy &&
    Seq.index input 28 = 0x8cuy &&
    Seq.index input 29 = 0x5euy &&
    Seq.index input 30 = 0x07uy &&
    Seq.index input 31 = 0x9euy &&
    Seq.index input 32 = 0x09uy &&
    Seq.index input 33 = 0xe2uy &&
    Seq.index input 34 = 0xc8uy &&
    Seq.index input 35 = 0xa8uy &&
    Seq.index input 36 = 0x33uy &&
    Seq.index input 37 = 0x9cuy
  else false

let server_hello_key_share_first (input:B.bytes) : GTot bool =
  if B.length input == 90 then
    Seq.index input 44 = 0uy &&
    Seq.index input 45 = 0x33uy &&
    Seq.index input 46 = 0uy &&
    Seq.index input 47 = 0x24uy &&
    Seq.index input 48 = 0uy &&
    Seq.index input 49 = 0x1duy &&
    Seq.index input 50 = 0uy &&
    Seq.index input 51 = 0x20uy &&
    Seq.index input 84 = 0uy &&
    Seq.index input 85 = 0x2buy &&
    Seq.index input 86 = 0uy &&
    Seq.index input 87 = 0x02uy &&
    Seq.index input 88 = 0x03uy &&
    Seq.index input 89 = 0x04uy
  else false

let server_hello_supported_versions_first (input:B.bytes) : GTot bool =
  if B.length input == 90 then
    Seq.index input 44 = 0uy &&
    Seq.index input 45 = 0x2buy &&
    Seq.index input 46 = 0uy &&
    Seq.index input 47 = 0x02uy &&
    Seq.index input 48 = 0x03uy &&
    Seq.index input 49 = 0x04uy &&
    Seq.index input 50 = 0uy &&
    Seq.index input 51 = 0x33uy &&
    Seq.index input 52 = 0uy &&
    Seq.index input 53 = 0x24uy &&
    Seq.index input 54 = 0uy &&
    Seq.index input 55 = 0x1duy &&
    Seq.index input 56 = 0uy &&
    Seq.index input 57 = 0x20uy
  else false

let server_hello_ok_52 (input:B.bytes) : GTot bool =
  server_hello_header_ok input &&
  not (server_hello_is_hrr input) &&
  server_hello_key_share_first input

let server_hello_ok_58 (input:B.bytes) : GTot bool =
  server_hello_header_ok input &&
  not (server_hello_is_hrr input) &&
  not (server_hello_key_share_first input) &&
  server_hello_supported_versions_first input

let server_hello_ok (input:B.bytes) : GTot bool =
  server_hello_ok_52 input || server_hello_ok_58 input

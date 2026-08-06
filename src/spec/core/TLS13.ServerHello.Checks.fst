module TLS13.ServerHello.Checks

module B = TLS13.Bytes
module Seq = FStar.Seq

let server_hello_header_ok (input:B.bytes) : GTot bool =
  if B.length input == 122 then
    Seq.index input 0 = 0x02uy &&
    Seq.index input 1 = 0uy &&
    Seq.index input 2 = 0uy &&
    Seq.index input 3 = 0x76uy &&
    Seq.index input 4 = 0x03uy &&
    Seq.index input 5 = 0x03uy &&
    Seq.index input 38 = 0x20uy &&
    Seq.index input 71 = 0x13uy &&
    Seq.index input 72 = 0x03uy &&
    Seq.index input 73 = 0uy &&
    Seq.index input 74 = 0uy &&
    Seq.index input 75 = 0x2euy
  else false

let server_hello_is_hrr (input:B.bytes) : GTot bool =
  if B.length input == 122 then
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
  if B.length input == 122 then
    Seq.index input 76 = 0uy &&
    Seq.index input 77 = 0x33uy &&
    Seq.index input 78 = 0uy &&
    Seq.index input 79 = 0x24uy &&
    Seq.index input 80 = 0uy &&
    Seq.index input 81 = 0x1duy &&
    Seq.index input 82 = 0uy &&
    Seq.index input 83 = 0x20uy &&
    Seq.index input 116 = 0uy &&
    Seq.index input 117 = 0x2buy &&
    Seq.index input 118 = 0uy &&
    Seq.index input 119 = 0x02uy &&
    Seq.index input 120 = 0x03uy &&
    Seq.index input 121 = 0x04uy
  else false

let server_hello_supported_versions_first (input:B.bytes) : GTot bool =
  if B.length input == 122 then
    Seq.index input 76 = 0uy &&
    Seq.index input 77 = 0x2buy &&
    Seq.index input 78 = 0uy &&
    Seq.index input 79 = 0x02uy &&
    Seq.index input 80 = 0x03uy &&
    Seq.index input 81 = 0x04uy &&
    Seq.index input 82 = 0uy &&
    Seq.index input 83 = 0x33uy &&
    Seq.index input 84 = 0uy &&
    Seq.index input 85 = 0x24uy &&
    Seq.index input 86 = 0uy &&
    Seq.index input 87 = 0x1duy &&
    Seq.index input 88 = 0uy &&
    Seq.index input 89 = 0x20uy
  else false

let server_hello_ok_84 (input:B.bytes) : GTot bool =
  server_hello_header_ok input &&
  not (server_hello_is_hrr input) &&
  server_hello_key_share_first input

let server_hello_ok_90 (input:B.bytes) : GTot bool =
  server_hello_header_ok input &&
  not (server_hello_is_hrr input) &&
  not (server_hello_key_share_first input) &&
  server_hello_supported_versions_first input

let server_hello_ok (input:B.bytes) : GTot bool =
  server_hello_ok_84 input || server_hello_ok_90 input

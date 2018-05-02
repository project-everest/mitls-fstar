open Prims

type 'Al lbuffer = FStar_UInt8.t FStar_Buffer.buffer

let to_bytes : Prims.nat -> Prims.unit lbuffer -> FStar_Bytes.bytes =
  fun len -> fun buf ->
  String.init (Z.to_int len) (fun i -> Char.chr (FStar_Buffer.index buf i))

let store_bytes : Prims.nat ->
                  Prims.unit lbuffer -> Prims.nat -> FStar_Bytes.bytes -> Prims.unit
  =
  fun len -> fun buf -> fun i -> fun b ->
  let i   = Z.to_int i in
  let len = Z.to_int len in
  String.iteri (fun j c -> FStar_Buffer.upd buf Pervasives.(i + j) (Char.code c))
               (FStar_Bytes.sub b i Pervasives.(len - i))

let from_bytes : FStar_Bytes.bytes -> Prims.unit lbuffer =
  fun b ->
  let buf =
      FStar_Buffer.create (FStar_UInt8.uint_to_t (Prims.parse_int "0"))
        (FStar_UInt32.uint_to_t (FStar_UInt32.v (FStar_Bytes.len b)))
    in
    store_bytes (FStar_UInt32.v (FStar_Bytes.len b)) buf (Prims.parse_int "0") b;
    buf

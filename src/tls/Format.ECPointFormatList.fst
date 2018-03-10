module Format.ECPointFormatList

open Format.ECPointFormat

module L = FStar.List.Tot

(*
    https://tools.ietf.org/html/rfc4492#section-5.1.2

    struct {
        ECPointFormat ec_point_format_list<1..2^8-1>
    } ECPointFormatList;

*)

type ecPointFormatList = (l:list ecPointFormat{1 <= L.length l && L.length l <= 255})

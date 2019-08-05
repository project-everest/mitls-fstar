module ConnectionTable_Aux

let connection_id = FStar.UInt32.t

val configuration: Type0

val client_hello: Type0

val ch_random: ch:client_hello -> FStar.UInt32.t

val cookie : Type0

val has_cookie: client_hello -> bool

val ch_of_cookie: ch:client_hello{has_cookie ch} -> client_hello

val ch_compatible: client_hello -> configuration -> bool

val rgn: FStar.HyperStack.ST.erid

module LowParse.Low.VLData.Aux
include LowParse.Spec.VLData
include LowParse.Low.Base

inline_for_extraction
val read_bounded_integer_1 : unit -> Tot (leaf_reader (parse_bounded_integer 1))

inline_for_extraction
val read_bounded_integer_2 : unit -> Tot (leaf_reader (parse_bounded_integer 2))

inline_for_extraction
val read_bounded_integer_3 : unit -> Tot (leaf_reader (parse_bounded_integer 3))

inline_for_extraction
val read_bounded_integer_4 : unit -> Tot (leaf_reader (parse_bounded_integer 4))

inline_for_extraction
val write_bounded_integer_1 : unit -> Tot (leaf_writer_strong (serialize_bounded_integer 1))

inline_for_extraction
val write_bounded_integer_2 : unit -> Tot (leaf_writer_strong (serialize_bounded_integer 2))

inline_for_extraction
val write_bounded_integer_3 : unit -> Tot (leaf_writer_strong (serialize_bounded_integer 3))

inline_for_extraction
val write_bounded_integer_4 : unit -> Tot (leaf_writer_strong (serialize_bounded_integer 4))

inline_for_extraction
let write_bounded_integer_1_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 1)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_1 ()) 1ul ()

inline_for_extraction
let write_bounded_integer_2_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 2)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_2 ()) 2ul ()

inline_for_extraction
let write_bounded_integer_3_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 3)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_3 ()) 3ul ()

inline_for_extraction
let write_bounded_integer_4_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 4)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_4 ()) 4ul ()

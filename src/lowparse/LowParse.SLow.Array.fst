module LowParse.SLow.Array

module U32 = FStar.UInt32

let parse32_array #k #t #p s p32 array_byte_size array_byte_size32 elem_count u
= [@inline_let]
  let _ =
    fldata_to_array_inj s array_byte_size elem_count u
  in
  parse32_synth
    _
    (fldata_to_array s array_byte_size elem_count u)
    (fun x -> fldata_to_array s array_byte_size elem_count u x)
    (parse32_fldata_strong
      (serialize_list _ s)
      (parse32_list p32)
      array_byte_size
      array_byte_size32
    )
    ()

let serialize32_array #k #t #p #s s32 array_byte_size elem_count u
= [@inline_let]
  let _ =
    fldata_to_array_inj s array_byte_size elem_count u
  in
  [@inline_let]
  let _ =
    array_to_fldata_to_array s array_byte_size elem_count u
  in
  serialize32_synth
    _
    (fldata_to_array s array_byte_size elem_count u)
    _
    (serialize32_fldata_strong
      (partial_serialize32_list _ _ s32 ())
      array_byte_size
    )
    (array_to_fldata s array_byte_size elem_count u)
    (fun x -> array_to_fldata s array_byte_size elem_count u x)
    ()

let size32_array #k #t #p s array_byte_size array_byte_size32 elem_count u
= size32_constant (serialize_array s array_byte_size elem_count u) array_byte_size32 ()


let parse32_vlarray array_byte_size_min array_byte_size_min32 array_byte_size_max array_byte_size_max32 #k #t #p s p32 elem_count_min elem_count_max u
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  parse32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    (parse32_bounded_vldata_strong
      array_byte_size_min
      array_byte_size_min32
      array_byte_size_max
      array_byte_size_max32
      (serialize_list _ s)
      (parse32_list p32)
    )
    ()

let serialize32_vlarray array_byte_size_min array_byte_size_max #k #t #p #s s32 elem_count_min elem_count_max u
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  [@inline_let]
  let _ =
    vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  serialize32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    _
    (serialize32_bounded_vldata_strong
      array_byte_size_min
      array_byte_size_max
      (partial_serialize32_list _ _ s32 ())
    )
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    ()

let size32_vlarray array_byte_size_min array_byte_size_max #k #t #p s elem_count_min elem_count_max u size_header_byte_size32 elem_byte_size32
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  [@inline_let]
  let _ =
    vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  size32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    _
    (size32_bounded_vldata_strong
      array_byte_size_min
      array_byte_size_max
      (size32_list #_ #_ #_ #s (size32_constant s elem_byte_size32 ()) ())
      size_header_byte_size32
    )
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    ()

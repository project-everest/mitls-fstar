(* -------------------------------------------------------------------- *)
let rng = Random.self_init ()

(* -------------------------------------------------------------------- *)
let random (i : int) =
  if i < 0 then
    invalid_arg "length must be non-negative";

  let s = String.create i in

  for i = 0 to i-1 do
    s.[i] <- char_of_int (Random.int 256)
  done;

  Bytes.abytes s

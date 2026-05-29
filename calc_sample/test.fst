module Test

type my_stack = list int

val f (s:my_stack) : option (my_stack & int)

let f s = Some (s, 0)

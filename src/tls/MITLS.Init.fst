module MITLS.Init

// Resolves to the right symbol in the shared object. This trick won't work with
// static linking against libmitls.a. The CPrelude thing is to avoid a karamel
// naming collision.
[@ (CPrologue "#define mitls_krmlinit_globals krmlinit_globals") ]
assume val mitls_krmlinit_globals:
  unit ->
  FStar.HyperStack.ST.Stack unit
    (fun _ -> True)
    (fun h0 _ h1 -> h0 == h1)

let mitls_init () =
  mitls_krmlinit_globals ()

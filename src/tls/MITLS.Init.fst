module MITLS.Init

// Resolves to the right symbol in the shared object. This trick won't work with
// static linking against libmitls.a. The CPrelude thing is to avoid a kremlin
// naming collision.
[@ (CPrologue "#define mitls_kremlinit_globals kremlinit_globals") ]
assume val mitls_kremlinit_globals:
  unit ->
  FStar.HyperStack.ST.Stack unit
    (fun _ -> True)
    (fun h0 _ h1 -> h0 == h1)

let mitls_init () =
  mitls_kremlinit_globals ()

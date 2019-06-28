module MITLS.Init

// Clients of miTLS (even in F*) should call this function before using the
// library (until we totally move it to Low*)
val mitls_init: unit ->
  FStar.HyperStack.ST.Stack unit
    (fun _ -> True)
    (fun h0 _ h1 -> h0 == h1)

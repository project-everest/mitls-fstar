module TLS13.Impl.ConnectionState.Bounds

let lemma_option_is_some_some #a (x:option a)
  : Lemma
      (requires option_is_some x)
      (ensures Some? x)
=
  match x with
  | Some _ -> ()
  | None -> ()

let lemma_option_is_some_some_imp #a (x:option a) (b:bool)
  : Lemma
      (requires (b ==> option_is_some x))
      (ensures (b ==> Some? x))
=
  match x with
  | Some _ -> ()
  | None -> ()

module List.Helpers

(* Some basic utility functions for closure converting arguments
   to the higher-order combinators in the list library ...
   for use with KreMLin extraction *)
let rec filter_aux (#a:Type)
                   (#b:Type)
                   (env:b)
                   (f:(b -> a -> Tot bool))
                   (l: list a)
    : Tot (m:list a { forall u . FStar.List.Tot.mem_filter_spec (f env) m u } ) =
      match l with
      | [] -> []
      | hd::tl -> if f env hd then hd::filter_aux env f tl else filter_aux env f tl
                                                                                             
let rec find_aux (#a:Type)
                 (#b:Type)
                 (env:b)
                 (f:(b -> a -> Tot bool))
                 (l:list a)
    : (option (x:a{f env x})) =
      match l with
      | [] -> None #(x:a{f env x}) //These type annotations are only present because it makes bootstrapping go much faster
      | hd::tl -> if f env hd then Some #(x:a{f env x}) hd else find_aux env f tl

let rec choose_aux  (#a:Type)
                    (#b:Type)
                    (#c:Type)
                    (env:c)
                    (f:(c -> a -> Tot (option b)))
                    (l:list a)
    : list b =
      match l with
      | [] -> []
      | hd::tl ->
        match f env hd with
        | Some i -> i :: choose_aux env f tl
        | None -> choose_aux env f tl

let exists_b_aux (#a:Type) (#b:Type) (env:b) (f:b -> a -> Tot bool) (l:list a) =
  Some? (find_aux env f l)

let mem_rev (#a:eqtype) (l:list a) (x:a) = List.Tot.mem x l

let rec forall_aux (#a:Type) (#b:Type) (env:b) (f: b -> a -> Tot bool) (l:list a)
  : Tot bool
  = match l with
    | [] -> true
    | hd::tl -> if f env hd then forall_aux env f tl else false

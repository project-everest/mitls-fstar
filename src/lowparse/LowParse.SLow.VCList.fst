module LowParse.SLow.VCList
include LowParse.Spec.VCList
include LowParse.SLow.List

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Classical = FStar.Classical
module L = FStar.List.Tot
module B32 = LowParse.Bytes32

let rec parse_nlist_tailrec
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (accu: list t * nat)
  (b: bytes)
: GTot (option (list t * nat))
= if n = 0
  then Some accu
  else
    match parse p b with
    | Some (elem, consumed) ->
      let (l0, consumed0) = accu in
      let b' = Seq.slice b consumed (Seq.length b) in
      parse_nlist_tailrec (n - 1) p (elem :: l0, consumed0 + consumed) b'
    | _ -> None

let rec parse_nlist_tailrec_correct'
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (accu: list t * nat)
  (b: bytes)
: Lemma
  (match parse_nlist_tailrec n p accu b, parse (parse_nlist n p) b with
    | None, None -> True
    | Some (l', consumed'), Some (l, consumed) ->
      let (l0, consumed0) = accu in
      consumed' == consumed0 + consumed /\ l' == L.rev l `L.append` l0
    | _ -> False)
= parse_nlist_eq n p b;
  if n = 0
  then ()
  else begin
    match parse p b with
    | None -> ()
    | Some (elem1, consumed1) ->
      let (l0, consumed0) = accu in
      let b' = Seq.slice b consumed1 (Seq.length b) in
      parse_nlist_tailrec_correct' (n - 1) p (elem1 :: l0, consumed0 + consumed1) b' ;
      match parse (parse_nlist (n - 1) p) b' with
      | None -> ()
      | Some (l2, consumed2) ->
        L.rev_rev' (elem1 :: l2);
        L.rev_rev' l2;
        L.append_assoc (L.rev l2) [elem1] l0
  end

let parse_nlist_tailrec_correct
  (n: nat)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  (match parse_nlist_tailrec n p ([], 0) b, parse (parse_nlist n p) b with
    | None, None -> True
    | Some (l', consumed'), Some (l, consumed) ->
      consumed' == consumed /\ l == L.rev l'
    | _ -> False)
= parse_nlist_tailrec_correct' n p ([], 0) b;
  match parse (parse_nlist n p) b with
  | None -> ()
  | Some (l, _) ->
    L.append_l_nil (L.rev l);
    L.rev_involutive l

let parse_nlist_tailrec_inv
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (accu: list t * nat)
  (input: bytes32)
  (b: bool)
  (x: option (bytes32 * U32.t * list t * U32.t))
: GTot Type0
= match x with
  | Some (input', i, accu', consumed') ->
    U32.v i <= U32.v n /\
    U32.v consumed' + B32.length input' < 4294967296 /\
    parse_nlist_tailrec (U32.v n) p accu (B32.reveal input) == parse_nlist_tailrec (U32.v n - U32.v i) p (accu', U32.v consumed') (B32.reveal input') /\
    (b == false ==> i == n)
  | None ->
    b == false /\ None? (parse_nlist_tailrec (U32.v n) p accu (B32.reveal input))

let parse_nlist_tailrec_measure
  (#t: Type)
  (n: U32.t)
  (x: option (bytes32 * U32.t * list t * U32.t))
: GTot nat
= match x with
  | None -> 0
  | Some (_, i', _, _) -> if U32.v i' > U32.v n then 0 else (U32.v n - U32.v i' + 1)

inline_for_extraction
let parse_nlist_body
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
  (x: option (bytes32 * U32.t * list t * U32.t))
: Pure (bool * option (bytes32 * U32.t * list t * U32.t))
  (requires (parse_nlist_tailrec_inv n p ([], 0) input true x))
  (ensures (fun (continue, y) ->
    parse_nlist_tailrec_inv n p ([], 0) input continue y /\
    (if continue then parse_nlist_tailrec_measure n y < parse_nlist_tailrec_measure n x else True)
  ))
= match x with
  | Some (input', i, accu', consumed') ->
    if i = n
    then (false, x)
    else
      match p32 input' with
      | None -> (false, None)
      | Some (y, consumed1) ->
        let input2 = B32.slice input' consumed1 (B32.len input') in
        (true, Some (input2, i `U32.add` 1ul, y :: accu', consumed' `U32.add` consumed1))

inline_for_extraction
let parse32_nlist
  (n: U32.t)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_nlist (U32.v n) p))
= fun input -> ((
    parse_nlist_tailrec_correct (U32.v n) p  (B32.reveal input);
    let res =
      C.Loops.total_while
        (parse_nlist_tailrec_measure n)
        (parse_nlist_tailrec_inv n p ([], 0) input)
        (fun x -> parse_nlist_body n p32 input x)
        (Some (input, 0ul, [], 0ul))
    in
    match res with
    | Some (_, _, accu, consumed) ->
      Some (list_rev accu, consumed)
    | None -> None
  ) <: Tot (res: _ { parser32_correct (parse_nlist (U32.v n) p) input res } ))

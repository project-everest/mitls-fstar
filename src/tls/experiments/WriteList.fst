module WriteList
open LowParse.Low.Base
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
open FStar.Integers

val write_list
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_writer_weak s)
  (l: list t)
  (sl: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    live_slice h sl /\
    pos <= sl.len /\
    sl.len < max_uint32 /\
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0
  ))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from sl pos) h h' /\ (
    if pos' = max_uint32
    then
      True
    else
      valid_list p h' sl pos pos' /\
      contents_list p h' sl pos pos' == l
  )))

let rec write_list #k #t #p #s w l sl pos =
  match l with
  | [] ->
    let h = HST.get () in
    valid_list_nil p h sl pos;
    pos
  | a :: q ->
    let pos1 = w a sl pos in
    if pos1 = max_uint32
    then pos1
    else begin
      let pos' = write_list w q sl pos1 in
      let h' = HST.get () in
      [@inline_let]
      let _ =
        if pos' = max_uint32
        then ()
        else begin
          valid_list_cons p h' sl pos pos'
        end
      in
      pos'
    end

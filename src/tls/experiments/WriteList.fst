module WriteList
open LowParse.Low.Base
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
open FStar.Integers

inline_for_extraction
let list_writer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_writer_weak s)
  (l: list t)
  =
   (sl: slice)
 -> (pos: U32.t)
 -> HST.Stack U32.t
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

inline_for_extraction
let write_list_nil
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_writer_weak s)
: Tot (list_writer w [])
= fun sl pos ->
    let h = HST.get () in
    valid_list_nil p h sl pos;
    pos

inline_for_extraction
let write_list_cons
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_writer_weak s)
  (a: t)
  (#q: list t)
  (wq: list_writer w q)
: Tot (list_writer w (a :: q))
= fun sl pos ->
    let pos1 = w a sl pos in
    if pos1 = max_uint32
    then pos1
    else begin
      let pos' = wq sl pos1 in
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

val write_list
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_writer_weak s)
  (l: list t)
: list_writer w l


let rec write_list #k #t #p #s w l=
  match l with
  | [] -> write_list_nil w
  | a :: q ->
    write_list_cons
      w
      a
      (write_list w q)

inline_for_extraction
let write_list'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (w: leaf_writer_weak s)
  (l: list t)
 : list_writer w l
 = Pervasives.norm [delta_only [`%write_list]; zeta; iota]
        (write_list w l)

let test
    (#k: parser_kind)
    (#t: Type)
    (#p: parser k t)
    (#s: serializer p)
    (w: leaf_writer_weak s)
    (elt : t)
 : list_writer w [elt;elt]
 = write_list' w [elt;elt]

(* Extracts to

   let pos1 = w elt sl pos  in
                  if
                    pos1 =
                      (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                  then pos1
                  else
                    (let pos' =
                       let pos11 = w elt sl pos1  in
                       if
                         pos11 =
                           (FStar_UInt32.uint_to_t
                              (Prims.parse_int "4294967295"))
                       then pos11
                       else
                         (let pos' =
                            let h1 = FStar_HyperStack_ST.get ()  in pos11  in
                          let h' = FStar_HyperStack_ST.get ()  in pos')
                        in
                     let h' = FStar_HyperStack_ST.get ()  in pos')
*)

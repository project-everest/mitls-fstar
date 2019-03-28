module MITLS.Repr.ClientHello
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module CH = Parsers.ClientHello
open FStar.Integers
open FStar.HyperStack.ST

let repr #p #q (b:LP.slice p q) =
  R.repr_p CH.clientHello b CH.clientHello_parser

let meta #p #q (b:LP.slice p q) (from to:R.index b) (h:HS.mem)
  : Pure (Ghost.erased (R.repr_meta CH.clientHello))
    (requires
      R.valid_pos b CH.clientHello_parser from to h)
    (ensures fun m ->
      let open R in
      let r = { start_pos = from;
                end_pos = to;
                meta = m } in
      valid r h)
  = let open R in
    let v = LP.contents CH.clientHello_parser h b from in
    Ghost.hide ({
      parser_kind = _;
      parser = CH.clientHello_parser;
      value = v
    })

let mk #p #q (b:LP.slice p q) (from to:R.index b)
  : Stack (repr b)
    (requires R.valid_pos b CH.clientHello_parser from to)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid r h1)
  = let open R in
    let h = get () in
    let m = meta b from to h in
    { start_pos = from;
      end_pos = to;
      meta = m }

let version (#b:LP.slice 'p 'q) (r:repr b)
  : Stack Parsers.ProtocolVersion.protocolVersion
    (requires R.valid r)
    (ensures fun h0 _ h1 ->
      B.modifies B.loc_none h0 h1) //underspecifying the returned value, until we figure out how much we need
  = let open R in
    let pos = CH.accessor_clientHello_version b r.start_pos in
    Parsers.ProtocolVersion.protocolVersion_reader b pos

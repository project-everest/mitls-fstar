(* -------------------------------------------------------------------- *)
open Bytes
 
type engine = Engine of string * Evp.MD.md

(* -------------------------------------------------------------------- *)
let name (Engine (name, m)) =
  name

let digest (Engine (name, m)) b = 
  let e = Evp.MD.create m in
  Evp.MD.update e (cbytes b);
  let h = Evp.MD.final e in
  Evp.MD.fini e; abytes h

(* -------------------------------------------------------------------- *)
let md5engine    () = Engine ("MD5"   , Evp.MD.md5    ())
let sha1engine   () = Engine ("SHA1"  , Evp.MD.sha1   ())
let sha256engine () = Engine ("SHA256", Evp.MD.sha256 ())
let sha384engine () = Engine ("SHA384", Evp.MD.sha384 ())
let sha512engine () = Engine ("SHA512", Evp.MD.sha512 ())

(* -------------------------------------------------------------------- *)
let md5    b = digest (md5engine    ()) b
let sha1   b = digest (sha1engine   ()) b
let sha256 b = digest (sha256engine ()) b
let sha384 b = digest (sha384engine ()) b
let sha512 b = digest (sha512engine ()) b

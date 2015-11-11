module SBA

// A simple array reindexer
// Avoids the many copies created by Array.sub
// (c) 2014 Microsoft Research

open System
open System.Text
open System.Text.RegularExpressions
open System.Security.Cryptography
open System.Numerics

exception OutOfBounds

type bytes = {
    A : byte[];
    S : int;
    L : int;
}

let create (a:byte[]) : bytes =
    {A=a; S=0; L=Array.length a}

let is_empty (a:bytes) : bool =
    a.L = 0

let sub (sa:bytes) (start:int) (len:int) : bytes =
    let len = if len=0 then sa.L-start else len in
    if start < 0 || len < 0 || start + len > sa.L then raise OutOfBounds
    {A=sa.A; S=sa.S+start; L=len}

let get (sa:bytes) (off:int) : byte =
    sa.A.[sa.S+off]

let set (sa:bytes) (off:int) (v:byte) : unit =
    sa.A.[sa.S+off] <- v

let peek (sa:bytes) (off:int) (l:int) : list<byte> =
    let l = if l=0 then sa.L else l in
    try
        Array.sub sa.A (sa.S+off) l |> List.ofArray
    with
    | _ -> raise OutOfBounds

let b2ba (sa:bytes) : byte[] =
    Array.sub sa.A sa.S sa.L

let b2list (sa:bytes) : list<byte> =
    b2ba sa
    |> Array.toList

let list2b (la:list<byte>) : bytes =
    la |> Array.ofList |> create

let beq (a:bytes) (b:bytes) : bool =
    b2list a = b2list b

let blen (sa:bytes) = sa.L

let rec trimz = function
| 0uy :: t -> trimz t
| l -> l    

let oid2b x =
    CryptoConfig.EncodeOID x
    |> fun r->Array.sub r 2 ((Array.length r)-2)
    |> create

let b2oid x =
    let rec next = function
    | x::t ->
        let (u, b, v) = next t
        if x &&& 128uy = 0uy then  (int x, 1, (if b>0 then "." + (string u) else "") + v)
        else ((int (x &&& 127uy) <<< (7*b)) + u, b+1, v)
    | [] -> (0, 0, "")
    match b2list x with
    | h::r ->
        let (u, b, v) = next r in
        let t = "." + (string u) + v //(match b with 0|1 -> v | n -> "." + (string n) + v)
        (string (h / 40uy)) + "." + (string (h % 40uy)) + t
    | _ -> failwith "Invalid OID"

let str2b (x:string) =
    Encoding.UTF8.GetBytes(x)
    |> create

let b2str (b:bytes) =
    Encoding.UTF8.GetString(b2ba b)

let b2ascii (b:bytes) =
    Encoding.ASCII.GetString(b2ba b)

let hex2b (s:string) = 
    (if s.Length % 2 = 1 then "0"+s else s)
    |> Seq.windowed 2
    |> Seq.mapi (fun i j -> (i,j))
    |> Seq.filter (fun (i,j) -> i % 2=0)
    |> Seq.map (fun (_,j) -> Byte.Parse(new String(j), Globalization.NumberStyles.AllowHexSpecifier))
    |> Array.ofSeq
    |> create

let b2hex (b:bytes) = 
    BitConverter.ToString(b2ba b).Replace("-", "")

let int2b (s:string) =
    let bx = BigInteger.Parse s in
    let ba = bx.ToByteArray()
    // encoding rule: if int is positive and top bit isn't 0 then pad with 0 byte
    let ba = if bx.Sign>=0 && (ba.[0] >>> 7)=1uy then Array.concat [ba; [|0uy|]] else ba
    create ba

let b2int (b:bytes) =
    let bx = new BigInteger(b2ba b |> Array.rev)
    bx.ToString()

let bitstr2b (s:string) = 
    let mutable t = new String(s.ToCharArray() |> Array.rev)
    let mutable i = 0
    while t.Length % 8 <> 0 do t <- t+"0"; i <- i+1 done
    t
    |> Seq.windowed 8
    |> Seq.mapi (fun i j -> (i,j))
    |> Seq.filter (fun (i,j) -> i % 8 = 0)
    |> Seq.map (fun (_,j) -> Convert.ToByte(new String(j), 2))
    |> Array.ofSeq
    |> create

let bitstrdec (x:bytes) =
    let ba = b2ba x
    let zb = ba.[0]
    let ba = Array.sub ba 1 (ba.Length - 1)
    let x = new BigInteger(Array.rev ba)
    BigInteger.op_RightShift(x, int zb).ToByteArray()

let isIA5 (b:bytes) =
    b2ba b |> Array.forall (fun b -> (b < 128uy))

let isTeletex (b:bytes) =
    b2ba b |> Array.forall (fun b -> (b >= 32uy) && (b < 127uy))

let isPrintable (b:bytes) =
    Regex.IsMatch(b2ascii b, "^[a-zA-Z0-9 '()+,-.?:/=]*$")

let isUTF8 (b:bytes) =
    try let _ = b2str in true with _ -> false

let isUniv (b:bytes) =
    try let _ = Encoding.UTF32.GetString(b2ba b) in true with _ -> false

let isBMP (b:bytes) =
    try let _ = Encoding.Unicode.GetString(b2ba b) in true with _ -> false

let isURI (b:bytes) =
    try
        let _ = new System.Uri(b2ascii b, System.UriKind.Absolute)
        true
    with
    | _ -> false

let isDate (b:bytes) =
    let d = b2ascii b
    Regex.IsMatch(d, "^([0-9]{2})(1[0-2]|0[0-9])(3[01]|[0-2][0-9])(2[0-3]|[01][0-9])([0-5][0-9])([0-5][0-9])Z$")

let isGenDate (b:bytes) =
    let d = b2ascii b
    Regex.IsMatch(d, "^([0-9]{4})(1[0-2]|0[0-9])(3[01]|[0-2][0-9])(2[0-3]|[01][0-9])([0-5][0-9])([0-5][0-9])Z$")

let isRFC822 (b:bytes) =
    Regex.IsMatch(b2ascii b, @"^(?("")("".+?(?<!\\)""@)|(([0-9a-z]((\.(?!\.))|[-!#\$%&'\*\+/=\?\^`\{\}\|~\w])*)(?<=[0-9a-z])@))""(?(\[)(\[(\d{1,3}\.){3}\d{1,3}\])|(([0-9a-z][-\w]*[0-9a-z]*\.)+[a-z0-9][\-a-z0-9]{0,22}[a-z0-9]))$")

let bTrue = create [| 255uy |]
let bFalse = create [| 0uy |]
let bEmpty = create [||]

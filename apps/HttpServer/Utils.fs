(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Utils

open System
open System.IO
open System.Text.RegularExpressions
open System.Web
open Microsoft.FSharp.Reflection

(* ------------------------------------------------------------------------ *)
type String with
    member self.UrlDecode () = HttpUtility.UrlDecode(self)

(* ------------------------------------------------------------------------ *)
type Stream with
    member self.CopyTo (output : Stream, length : int64) : int64 =
        let (*---*) buffer   : byte[] = Array.zeroCreate (128 * 1024) in
        let mutable position : int64  = (int64 0) in
        let mutable eof      : bool   = false in
            while not eof && (position < length) do
                let remaining = min (int64 buffer.Length) (length - position) in
                let rr = self.Read(buffer, 0, int remaining) in
                    if rr = 0 then
                        eof <- true
                    else begin
                        output.Write(buffer, 0, rr);
                        position <- position + (int64 rr)
                    end
            done;
            position

(* ------------------------------------------------------------------------ *)
let noexn = fun cb ->
    try cb () with _ -> ()

(* ------------------------------------------------------------------------ *)
let unerror (x : 'a TLSError.Result) =
    match x with
    | Error.Error   _ -> failwith "Utils.unerror"
    | Error.Correct x -> x

(* ------------------------------------------------------------------------ *)
let (|Match|_|) pattern input =
    let re = System.Text.RegularExpressions.Regex(pattern)
    let m  = re.Match(input) in
        if   m.Success
        then Some (re.GetGroupNames()
                        |> Seq.map (fun n -> (n, m.Groups.[n]))
                        |> Seq.filter (fun (n, g) -> g.Success)
                        |> Seq.map (fun (n, g) -> (n, g.Value))
                        |> Map.ofSeq)
        else None

(* ------------------------------------------------------------------------ *)
module IO =
    let ReadAllLines (stream : StreamReader) = seq {
        while not stream.EndOfStream do
            yield stream.ReadLine ()
    }

(* ------------------------------------------------------------------------ *)
exception NotAValidEnumeration

let enumeration<'T> () =
    let t = typeof<'T>

    if not (FSharpType.IsUnion(t)) then
        raise NotAValidEnumeration;

    let cases = FSharpType.GetUnionCases(t)

    if not (Array.forall
                (fun (c : UnionCaseInfo) -> c.GetFields().Length = 0)
                (FSharpType.GetUnionCases(t))) then
        raise NotAValidEnumeration;

    let cases =
        Array.map
            (fun (c : UnionCaseInfo) ->
                (FSharpValue.MakeUnion(c, [||]) :?> 'T), c.Name)
            cases
    in
        cases

(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiHTTPUtils

let split_and_strip (c : char) (count : int) (s : string) : string list =
    s.Split([|c|], count, System.StringSplitOptions.None)
        |> List.ofArray
        |> List.map (fun s -> s.Trim ())

let parse_date (s : string) : Date.DateTime option =
    None

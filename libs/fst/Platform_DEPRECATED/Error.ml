type ('a,'b) optResult =
    | Error of 'a
    | Correct of 'b

let perror (file:string) (line:int) (text:string) =
    text

let correct x = Correct x

let unexpected info = failwith info
let unreachable info = failwith info
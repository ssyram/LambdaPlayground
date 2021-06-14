module LambdaPlayground.Global

// programming helping functions
let ($) = (<|)
let ifNone f v =
    if v = None then f () else v
let (=>>) v f = v |> ifNone f
let (>>=) v f =
    match v with
    | Some v -> f v
    | None -> None

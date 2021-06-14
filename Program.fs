// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp

#light "off"

open System
open System.Collections.Generic
open LambdaPlayground

// Define a function to construct a message to print
let from whom =
    sprintf "from %s" whom
    
let rec numberDefString n =
    let pre = $"let {n} = \\f x." in
    let rec fPrinter =
        function
        | 0u -> "x"
        | 1u -> "f x"
        | n -> "f (" + fPrinter (n - 1u) + ")"
    in
    pre + fPrinter n

[<EntryPoint>]
let main argv =
    let _ =
        try
            Analysis.AnalyseCommandLine <| List.ofArray argv
        with
        | e -> eprintfn $"{e.Message}"
////    let rec printer n =
////        let _ = printfn $"{numberDefString n}" in
////        if n > 0u then printer (n - 1u) else ()
////    in
////    let _ = for s in argv do printfn $"{s}" done in
////    let _ = printfn $"Amount of vars: {argv.Length}" in
////    let _ = printer 100u in
////    let _ = printfn $"""{" \tabc a  \n\r\t".Trim ()}""" in
////    let _ = Char.IsWhiteSpace in
////    let _ = printfn $"""{"abc".[..1]}""" in
//    let _ = Analysis.stringAnalyser "
//    let True = \x y.x
//    let False = \x y.y  // == 0
//    let and = \x y.x y False
//    let or = \x y.x True y
//    let not = \x.x False True
//    let xor = \x y.x (not y) y
//    let eq = \x y.x y (not y)  // == not xor
//    let imply = \x y.x y True
//
//    let mid && = and
//    let mid || = or
//    let ~ = not
//    let mid ^ = xor
//    let mid ?= = eq
//
//    let de_morgan = \x y.(~ (x && y)) ?= (~ x) || (~ y)
//
//    // prove de_morgan by computation -- `and` all possible values
//    de_morgan False False \
//    && \
//    de_morgan False True \
//    && \
//    de_morgan True False \
//    && \
//    de_morgan True True
//    "
    in
    0 // return an integer exit code
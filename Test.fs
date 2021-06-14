module LambdaPlayground.Test

open System.IO
open LambdaPlayground.LambdaCalculus
open Lexer
open FSharp.Text.Lexing

#light "off"

let testLambdaParsing lambdaString =
    let lexbuf = LexBuffer<char>.FromString lambdaString
    in
    let lt = Parser.lambda_line token lexbuf
    in
    printfn $"{lt}"
    
let testCommentRemoval () =
    let s =
        use sr = new StreamReader("../../../sample files/nat.lp") in
        sr.ReadToEnd ()
    in
    printfn $"{Analysis.commentRemoval s}"

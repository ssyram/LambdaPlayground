module LambdaPlayground.ParserSupport

open LambdaPlayground.LambdaCalculus

let runLambda lt =
    failwith "todo"
    
let runPi pt =
    failwith "todo"
    
let runCommand cs =
    failwith "todo"
    
let recordBinding name term =
    failwith "todo"

let recordMidOpBinding midOp term =
    failwith "todo"
    
let recordNormalOpBinding op term =
    failwith "todo"
    
let rec buildLambda idList term =
    match idList with
    | v :: l ->
        LTAbstract (v, buildLambda l term)
    | [] -> term

let err str =
    failwith "todo"

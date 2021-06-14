module LambdaPlayground.Lambda2PiConversion

open System.Collections.Generic
open LambdaPlayground.LambdaCalculus
open LambdaPlayground.PiCalculus

let rec callByNameConversion<'v>
    lt u (newNameList : IEnumerable<'v>) = 1
//    match lt with
//    | LTVar x -> PTSend (x, u, PTZero)
//    | LTAbstract (x, t) ->
//        let nn = newNameList.GetEnumerator ()
//        PTRead (u, x, PTRead (u, u, PTZero))
//        

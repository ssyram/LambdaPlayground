module LambdaPlayground.LambdaCalculus

open System
open System.Collections
open System.Collections.Generic
open Global

type ReductionStrategy =
    | CallByValue
    | CallByName

type LambdaTerm<'var when 'var : comparison> =
    | LTVar of 'var
    | LTApply of LambdaTerm<'var> * LambdaTerm<'var>
    | LTAbstract of 'var * LambdaTerm<'var>
    
    member x.ToString formatter =
        match x with
        | LTVar v -> formatter v
        | LTApply (m, n) ->
            let m =
                match m with
                | LTAbstract _ -> $"({m})"
                | _ -> $"{m}"
            in
            match n with
            | LTVar _ -> $"{m} {n}"
            | _ -> $"{m} ({n})"
        | LTAbstract (v, t) -> $"\\{v}.{t}"
    
    override x.ToString () = x.ToString (fun v -> $"{v}")

type DeBruijnLambdaTerm =
    | DLTVar of uint
    | DLTApp of DeBruijnLambdaTerm * DeBruijnLambdaTerm
    | DLTAbs of DeBruijnLambdaTerm
    
type AnnotatedDeBruijnLambdaTerm<'var when 'var : comparison> = LambdaTerm<'var * uint>
/// support types for term searching
type DFVVarType<'v> =
    | DFVVQualifiedVar of uint
    | DFVVFreeVar of 'v
/// this type is convenient, because it can compare totally the equivalence with convenience from
/// both De Bruijn notation and also free vars
/// this type should never be used to perform reduction directly
type DeBruijnLambdaTermWithFreeVars<'v when 'v : comparison> = LambdaTerm<DFVVarType<'v>>

module LambdaTerm = begin
    #light "off"
//    /// 'log must be monoid, with (*) and Pure, the latter will return unit
//    /// This is a writer monad
//    type ReductionContext<
//        'tt, 'log
//        when 'log : (static member (*) : 'log -> 'log -> 'log)
//        and 'log : (static member Pure : unit -> 'log)
//    > = {
//        term : 'tt;
//        log : 'log;
//    }
//    with
//        static member (>>=) (v : ReductionContext<_, _>, f) =
//            let ctx : ReductionContext<_, _> = f v.term in
//            {
//                ctx with log = ctx.log * v.log
//            }
//    end
    
    /// returns the DeBruijn Lambda Term and an array of free vars whose index is the outer index - 1
    /// (outer index count from 1)
    let ToDeBruijnLambdaNotation (lt : LambdaTerm<'v>) =
        let freeMap = Hashtable () in
        let findInFreeMap k =
            if freeMap.ContainsKey k then Some (freeMap.[k] :?> uint) else None
        in
        let rec impl lt bindMap stackCount =
            let recall lt = impl lt bindMap stackCount in
            match lt with
            | LTVar v ->
                DLTVar (
                Option.get (
                (Map.tryFind v bindMap)
                =>> (fun () -> findInFreeMap v >>= (fun outerId -> Some $ outerId + stackCount))
                =>> (fun () ->
                    let nf = uint freeMap.Count in
                    let _ = freeMap.Add(v, nf + 1u) in
                    Some $ nf + stackCount)))
            | LTApply (t1, t2) -> DLTApp (recall t1, recall t2)
            | LTAbstract (x, t) ->
                let stackCount = stackCount + 1u in
                DLTAbs $ impl t (Map.add x stackCount bindMap) stackCount
        in
        let getFreeVarArray () =
            Map.ofSeq $ seq {
                for entry in freeMap do
                    let entry = entry :?> DictionaryEntry in
                    yield entry.Key :?> 'v, entry.Value :?> uint
                done
            }
            |> Map.toArray
            |> Array.sortBy snd
            |> Array.unzip
            |> fst
        in
        impl lt Map.empty 0u, getFreeVarArray ()
        
    let ToAnnotatedDeBruijnNotation lt : AnnotatedDeBruijnLambdaTerm<_> =
        let t = fst $ ToDeBruijnLambdaNotation lt in
        let rec impl t lt =
            match t, lt with
            | DLTVar n, LTVar v -> LTVar (v, n)
            | DLTApp (t1, t2), LTApply (lt1, lt2) -> LTApply (impl t1 lt1, impl t2 lt2)
            | DLTAbs t, LTAbstract (x, lt) -> LTAbstract ((x, 0u), impl t lt)
            | _ -> failwith "IMPOSSIBLE"
        in
        impl t lt
        
    let ToDeBruijnWithFreeVars lt : DeBruijnLambdaTermWithFreeVars<_> =
        let dlt, freeVars = ToDeBruijnLambdaNotation lt in
        let rec construct dlt sc =
            match dlt with
            | DLTVar v ->
                if v <= sc then LTVar $ DFVVQualifiedVar v
                else LTVar $ DFVVFreeVar freeVars.[int $ v - sc - 1u]
            | DLTApp (t1, t2) ->
                LTApply (construct t1 sc, construct t2 sc)
            | DLTAbs t ->
                /// the quantified variable is not important at all
                LTAbstract (DFVVQualifiedVar 0u, construct t $ sc + 1u)
        in
        construct dlt 0u
        
    let RenameFreeVarsInDeBruijnLambdaTerm lt permuteMap =
        let rec impl lt sc =
            match lt with
            | DLTVar n ->
                if n <= sc then lt
                else DLTVar $ Option.get (Map.tryFind n permuteMap =>> (fun () -> Some n))
            | DLTApp (t1, t2) -> DLTApp (impl t1 sc, impl t2 sc)
            | DLTAbs t -> impl t $ sc + 1u
        in
        impl lt 0u
    
    /// a helpful renaming function for renaming strings
    let stringRenaming (str : string) =
        if String.IsNullOrEmpty str then "NewRenamedVar"
        else
            let rec numStartFrom n =
                if n > -1 && Char.IsNumber str.[n] then
                    numStartFrom $ n - 1
                else n
            in
            match numStartFrom $ str.Length - 1 with
            | -1 ->
                // it's a pure number
                str + "_0"
            | x when x = str.Length - 1 ->
                // no number
                str + "_0"
            | x when str.[x] = '_' ->
                // it should be regarded as having been renamed
                str.[..x] + $"{Int32.Parse str.[x + 1..]}"
            | _ ->
                // no number
                str + "_0"
    /// Note that this function may return
    let GetFreeVars lt =
        let rec getFreeVars lt qVars =
            match lt with
            | LTVar v ->
                Set.ofList $ if not $ Set.contains v qVars then [v] else []
            | LTApply (t1, t2) ->
                Set.union (getFreeVars t1 qVars) (getFreeVars t2 qVars)
            | LTAbstract (v, t) ->
                getFreeVars t $ Set.add v qVars
        in
        getFreeVars lt Set.empty
    
    /// \x.t => \nx.t[nx/x]
    /// returns t[nx/x]
    ///
    /// NOTE: will not check whether nx is originally a free name of t or not
    let rec unsafe_AlphaConversion x t nx =
        match t with
        | LTVar v -> LTVar <| if v = x then nx else v
        | LTApply (t1, t2) ->
            LTApply (unsafe_AlphaConversion x t1 nx,
                     unsafe_AlphaConversion x t2 nx)
        | LTAbstract (v, t') ->
            // naming overlapping appeared
            if v = x then t
            else LTAbstract (v, unsafe_AlphaConversion x t' nx)
            
//    /// just safely rename a term with an unpredictable new name of x
//    let RenameATerm x t rename =
//        let x' =
//            let freeVars = GetFreeVars t in
//            let rec findAName x =
//                if Set.contains x freeVars then
//                    findAName (rename x)
//                else x
//            in
//            findAName (rename x)
//        in
//        unsafe_AlphaConversion x t x'
//        
    /// only instant formal equivalence is checked, without any expansion of bindings and other things
    let CheckAlphaEquivalence t t' =
        let t, t' = ToDeBruijnLambdaNotation t, ToDeBruijnLambdaNotation t' in
        let rec impl t t' =
            match t, t' with
            | DLTVar v, DLTVar v' -> v = v'
            | DLTApp (t1, t2), DLTApp (t1', t2') ->
                impl t1 t1' && impl t2 t2'
            | DLTAbs t, DLTAbs t' ->
                impl t t'
            | _ -> false
        in
        impl (fst t) (fst t')
    
    /// this is a supporting function for renaming and substitution
    /// this function returns all names that "x" should not be renamed to
    let rec getAllNonPossibleNames x t =
        let ret = HashSet<_> () in
        let rec findNames t =
            match t with
            | LTVar v ->
                // use its current name is OK
                if v <> x then ret.Add v |> ignore
            | LTApply (t1, t2) ->
                findNames t1;
                findNames t2
            | LTAbstract (v, t) ->
                // if naming overlapping occurs, that means renaming of x will have no impact on t
                if v <> x then findNames t
        in
        findNames t;
        Set.ofSeq ret
    
    /// (\x.t) v => t[v/x]
    ///
    /// MAY USE "rename" function to rename some of the possible binding variables
    let rec SubstituteVarInTerm t v x rename =
        let recall t = SubstituteVarInTerm t v x rename in
        match t with
        | LTVar x' ->
            if x = x' then v
            else t
        | LTApply (t1, t2) ->
            LTApply (recall t1, recall t2)
        | LTAbstract (x', t') ->
            if x = x' then t
            else
                // get true x' and t' that avoids conflicting with v
                let x', t' =
                    let vFreeVars = GetFreeVars v in
                    if not <| Set.contains x' vFreeVars then x', t'
                    else
                        let nonPossibleNames = getAllNonPossibleNames x' t' in
                        let freeVars = Set.union vFreeVars nonPossibleNames in
                        let rec pickASafeNameFrom x =
                            if Set.contains x freeVars then
                                pickASafeNameFrom $ rename x
                            else x
                        in
                        let newX = pickASafeNameFrom $ rename x' in
                        newX, unsafe_AlphaConversion x' t' newX
                in
                LTAbstract (x', recall t')
    
    // essentially, reduction strategy is simply about finding a focus
    // reduction functions will not treat bindings differently, if one wants to expand, please preprocess
    // the term
    //
    // recVal ask if one needs to get a recursive value -- the function body should also be a value
    
    let rec IsCallByValueVal lt =
        let recall = IsCallByValueVal in
        match lt with
        | LTApply (t1, t2) -> begin
            match t1 with
            | LTAbstract _ -> false
            | _ -> recall t1 && recall t2
            end
        | _ -> true
    
    let rec IsRecursiveVal lt =
        match lt with
        | LTVar _ -> true
        | LTApply (t1, t2) -> begin
            match t1 with
            | LTAbstract _ -> false
            | _ -> IsRecursiveVal t1 && IsRecursiveVal t2
            end
        | LTAbstract (_, t) -> IsRecursiveVal t
        
    let rec IsCallByNameVal lt =
        match lt with
        | LTApply (t, _) -> begin
            match t with
            | LTAbstract _ -> false
            | _ -> IsCallByNameVal t
            end
        | _ -> true
    
    /// if it is a value, just return None
    let rec CallByValueReduction recVal rename lt =
        let recall = CallByValueReduction recVal rename in
        let recall' = CallByValueReduction false rename in
        match lt with
        | LTVar _ -> None
        | LTApply (t1, t2) ->
            // try reducing t2 in non-recVal mode
            (Option.map (fun t2 -> LTApply (t1, t2)) (recall' t2))
            =>> (fun () ->
                match t1 with
                | LTAbstract (x, t) -> Some $ SubstituteVarInTerm t t2 x rename
                | _ -> None)
            // try reducing t1 in non-recVal mode, because if none, t2 should be reduce with recVal first
            =>> (fun () -> (Option.map (fun t1 -> LTApply (t1, t2)) $ recall' t1))
            =>> (fun () ->
                if recVal then
                    (Option.map (fun t2 -> LTApply (t1, t2)) $ recall t2)
                    =>> (fun () -> Option.map (fun t1 -> LTApply (t1, t2)) $ recall t1)
                else None)
        | LTAbstract (x, t) ->
            (if recVal then recall t else None) >>= (fun t -> Some $ LTAbstract (x, t))
                            
    
    /// to reduce a term with bindings and a renaming function for getting naming conflicts resolve
    let rec CallByNameReduction recVal rename lt =
        let recall = CallByNameReduction recVal rename in
        match lt with
        | LTVar _ -> None
        | LTApply (t1, t2) ->
            (match t1 with
             | LTAbstract (x, t) -> Some $ SubstituteVarInTerm t t2 x rename
             | _ -> None)
            =>> (fun () -> recall t1 >>= (fun t1 -> Some $ LTApply (t1, t2)))
            =>> (fun () -> recall t2 >>= (fun t2 -> Some $ LTApply (t1, t2)))
        | LTAbstract (x, t) ->
            (if recVal then recall t else None) >>= (fun t -> Some $ LTAbstract (x, t))
    
    let Reduction strategy =
        match strategy with
        | CallByName -> CallByNameReduction
        | CallByValue -> CallByValueReduction
    
    /// map over free variables of a lambda term
    let rec MapFreeVars f lt =
        let rec innerMapFree lt qualifiedVars =
            match lt with
            | LTVar v ->
                if Set.contains v qualifiedVars then LTVar v
                else f v
            | LTApply (t1, t2) ->
                LTApply (innerMapFree t1 qualifiedVars,
                         innerMapFree t2 qualifiedVars)
            | LTAbstract (v, t) ->
                LTAbstract (v, innerMapFree t (Set.add v qualifiedVars))
        in
        innerMapFree lt Set.empty
    
    /// check whether the term is a closed term
    let rec CheckClose x =
        let rec checkClose t envSet =
            match t with
            | LTVar v -> Set.contains v envSet
            | LTApply (m, n) -> checkClose m envSet && checkClose n envSet
            | LTAbstract (v, t) -> checkClose t (Set.add v envSet)
        in
        checkClose x Set.empty
    
    /// expand one level of binding
    let rec ExpandOneLevel binderFinder =
        // should only expand free variables -- naming overlapping
        MapFreeVars
            (fun v ->
                match binderFinder v with
                | Some t -> t
                | None -> LTVar v)
        
    let rec CheckCloseWithBinderFinder x nameInBinder =
        Set.isEmpty $ Set.filter (fun x -> not $ nameInBinder x) (GetFreeVars x)
end
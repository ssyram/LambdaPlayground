(*
This file describes how to cope with text input.
There are three kinds of them:
    1. direct run as parameter of program
    2. interactive run, where a file can also be load in this environment
    3. run a file
    
The core of the program is "line".
File should be preprocessed and turned into meaningful consequent lines, and then put into the analyser.
*)

#light "off"

module LambdaPlayground.Analysis

open System
open System.Collections
open System.IO
open FSharp.Text.Lexing
open LambdaCalculus
open PiCalculus
open Parser
open Global

// ---------------------------- Ended Supporting Part ----------------------------
// ----------------------------- Start Content Part ------------------------------

/// the mark of returning
exception ReturnMark

module Flags = begin
    type ModeType =
        | LambdaMode
        | PiMode
    type EtaMode =
        | EtaExpansion
        | EtaContraction
        | DoNothing
    type LambdaTermOperationMode =
        | LTMReduction
        | LTMSimplify   // simplify to user define string
        | LTMComparison
    type RunType =
        | RunAString of string
        | RunAFile of string
        | RunInteractive
    let mutable INPUT_MODE = LambdaMode
    let mutable IN_INTERACTIVE = false
    let mutable RUN_MODE = RunInteractive
    module LambdaOptions = begin
        let mutable MAXIMUM_REDUCTION : uint64 option = Some 1000uL
        let mutable ETA_MODE = DoNothing
        let mutable RECURSIVE_VALUE_MODE = false
        /// just display result, no process
        let mutable RESULT_ONLY = false
        let mutable REDUCTION_METHOD = CallByValue
        /// have values:
        /// Some t => t : the term waiting for comparison
        /// None : mode has not been triggerred
        let mutable TERM_FOR_COMPARISON = None
        let mutable COPY_DEF = false
        /// if it is file input
        /// make definition response silent, use in file input context
        let mutable SILENT_MODE = false
        let mutable OPERATION_MODE = LTMReduction
        let mutable IGNORE_REPEAT_DEFINITION = false
        let mutable SIMPLIFY_EVERY_STEP = true
    end
end

let printFreeVarWarning lt =
    if Flags.LambdaOptions.SILENT_MODE |> not then
        let freeVars = LambdaTerm.GetFreeVars lt in
        if freeVars.IsEmpty |> not then
            let s =
                Set.map (fun s -> $"\"{s}\"") freeVars
                |> String.concat ", "
            in
            printfn $"Warning: Contains Free Variables: {s}"

let analyseStrWith str parseFunc =
    let lexbuf = LexBuffer<char>.FromString str in
    parseFunc Lexer.token lexbuf
    
// remove all (**) and // comments in str
let commentRemoval (str : string) =
    let rec impl (restStr : string) =
        if String.IsNullOrEmpty restStr then ""
        else
        let nearCommentIdx, nearCommentType =
            match (restStr.IndexOf "(*", '*'), (restStr.IndexOf "//", '/') with
            | (-1, _), a -> a
            | a, (-1, _) -> a
            | x, y -> List.minBy fst [x; y]
        in
        let prefix, rst =
            if nearCommentIdx = -1 then restStr, ""
            else restStr.[..nearCommentIdx - 1], restStr.[nearCommentIdx..] in
        let rst =
            if nearCommentType = '*' then
                let backIdx = rst.IndexOf "*)" in
                (if backIdx = -1 then failwith "Incomplete comment, expecting \"*)\"");
                rst.[(backIdx+2)..]
            else
                let backIdx = rst.IndexOf "\n" in
                if backIdx = -1 then ""
                else rst.[backIdx..]  // not removing '\n'
        in
        String.concat "" [prefix; impl rst]
    in
    impl str

/// remove comment and re-append lines, reformat the whole string
let preprocess (str : string) =
    let str = commentRemoval str in
    let str = str.Replace("\\\n", "") in
    let str = str.Replace("\\\r\n", "") in
    let ss = str.Split([|"\n"; "\r\n"|], StringSplitOptions.TrimEntries) in
    Array.map (fun (s : string) -> s.Trim ()) ss

// first of all: some global conditional issues
/// type :: Map<string, LambdaTerm<string>>
let mutable nameTermBinding = Hashtable ()
/// type :: Map<LambdaTerm<string>, string>
let mutable termNameBinding = Hashtable ()
let searchBindingByName name =
    let res = nameTermBinding.[name] in
    if res = null then None
    else Some (res :?> LambdaTerm<string>)
let searchBindingByTerm (term : LambdaTerm<string>) =
    let tt = LambdaTerm.ToDeBruijnWithFreeVars term in
    let res = termNameBinding.[tt] in
    if res = null then None
    else Some (res :?> string)
/// add a new binding, possibly replace the original ones
/// returns message list, possibly to be printed
let addBinding name term =
    let fullTerm = LambdaTerm.ExpandOneLevel searchBindingByName term in
    let _ = printFreeVarWarning fullTerm in
    let msgLst =
        match nameTermBinding.[name] with
        | null ->
            // this is the first time binding this element
            nameTermBinding.Add(name, fullTerm);
            [$"Created binding with name: \"{name}\" and term: \"{term}\""]
        | oriTerm ->
            let oriTerm = oriTerm :?> LambdaTerm<string> in
            let msgLst = [$"Replaced original name \"{name}\" of term \"{oriTerm}\" with new term \"{fullTerm}\""]in
            termNameBinding.Remove $ LambdaTerm.ToDeBruijnWithFreeVars oriTerm;
            msgLst
    in
    let fullTerm' = LambdaTerm.ToDeBruijnWithFreeVars fullTerm in
    try
        termNameBinding.Add(fullTerm', name);
        msgLst
    with
    | :? ArgumentException ->
        termNameBinding.[fullTerm'] <- name;
        List.append msgLst [$"Term \"{fullTerm}\" will now use a new name \"{name}\""]

/// if found, return Some with the simplified version, otherwise, return None
///
/// Note that this function is just a sound one, but no guarantee for completeness
let rec findUserDefinedNameRepresentation lt =
    (searchBindingByTerm lt >>= (fun s -> Some $ LTVar s))
    =>> (fun () ->
        match lt with
        | LTApply (t1, t2) -> begin
            match findUserDefinedNameRepresentation t1, findUserDefinedNameRepresentation t2 with
            | None, None -> None
            | x, y -> Some $ LTApply (Option.defaultValue t1 x, Option.defaultValue t2 y)
        end
        | LTAbstract (x, t) ->
            findUserDefinedNameRepresentation t >>= (fun t -> Some $ LTAbstract (x, t))
        | _ -> None)

/// a framework function of multistep lambda reduction
///
/// returns whether the final result is a value
let FrameWork_LambdaReduction
    notify
    (lt : LambdaTerm<string>)
    times =
    let mutable times = times in
    let mutable lt = Some lt in
    while lt <> None && times <> Some 0uL do
        let tlt = Option.get lt in
        let nextStepTerm =
            LambdaTerm.Reduction
                Flags.LambdaOptions.REDUCTION_METHOD
                Flags.LambdaOptions.RECURSIVE_VALUE_MODE
                LambdaTerm.stringRenaming
                tlt
        in
        let _ =
            match nextStepTerm with
            | Some nlt ->
                lt <- Some nlt;
                notify nlt
            | None -> lt <- None
        in
        times <- times >>= (fun tt -> Some $ tt - 1uL)
    done;
    lt = None
    ;;

/// non-lazy reduction sequence finder
let lambdaReduction lt times =
    let mutable ret = [lt] in
    FrameWork_LambdaReduction (fun nlt -> ret <- nlt :: ret) lt times |> ignore;
    List.rev ret

let lambdaAnalyser (lt : LambdaTerm<string>) : unit =
    // expand one level is enough for any definition will only have at most one level of var
    let lt = LambdaTerm.ExpandOneLevel searchBindingByName lt in
    let _ = printFreeVarWarning lt in
    /// consider simplification, terms may get simplified with user-defined names
    /// this function encapsulates this process and returns the term that should be printed
    let getTermToPrint lt =
        if Flags.LambdaOptions.SIMPLIFY_EVERY_STEP then
            Option.defaultValue lt $ findUserDefinedNameRepresentation lt
        else
            lt
    in
    /// adopt lazy eval to reduce use of space
    let reduction times =
        /// cache the latest term to search
        let mutable nlt = lt in
        /// cache the time of reduction to print
        let mutable actualTime = 1uL in
        let _ =
            if Flags.LambdaOptions.COPY_DEF then printfn $"{getTermToPrint lt}"
        in
        let isVal =
            FrameWork_LambdaReduction
                (fun nlt' ->
                    nlt <- nlt';
                    (if not Flags.LambdaOptions.RESULT_ONLY then
                        printfn $"{actualTime} : -> {getTermToPrint nlt'}");
                    actualTime <- actualTime + 1uL)
                lt times
        in
        let _ = if isVal && not Flags.LambdaOptions.RESULT_ONLY then printfn "-/->"
        in
        (if Flags.LambdaOptions.RESULT_ONLY then printfn $"{nlt} ");
        Option.iter (fun v -> printfn $"= {v}") $ findUserDefinedNameRepresentation nlt
    in
    let simplification () =
        match findUserDefinedNameRepresentation lt with
        | Some lt -> printfn $"Simplified Term: {lt}"
        | None -> printfn "No Simplification Available."
    in
    let comparison () =
        match Flags.LambdaOptions.TERM_FOR_COMPARISON with
        | None ->
            Flags.LambdaOptions.TERM_FOR_COMPARISON <- Some $ LambdaTerm.ToDeBruijnWithFreeVars lt
        | Some t ->
            if LambdaTerm.ToDeBruijnWithFreeVars lt = t then
                printfn "True"
            else
                printfn "False"
    in
    let modeChoice () =
        match Flags.LambdaOptions.OPERATION_MODE with
        | Flags.LTMReduction -> reduction Flags.LambdaOptions.MAXIMUM_REDUCTION
        | Flags.LTMSimplify -> simplification ()
        | Flags.LTMComparison -> comparison ()
    in
    modeChoice ()
    
let piAnalyser (pt : PiTerm<string>) : unit =
    failwith "todo"

let printHelper () =
    printfn
"help: printing out help strings
quit/exit: exit the interactive mode
rv: recursive value mode
cbn: adopt call-by-name reduction strategy
cnv: adopt call-by-value reduction strategy
clear: clear all bindings
to_value: reduction all the way to value, may lead to infinite evaluation and thus printing
max_steps <num>: in contrast to to_value, this command specify a maximum reduction number
expand: while reduction, expand all elements
sim_step: in contrast to expand, try printing out the term in user-defined strings
silent: silent mode, not printing out all strings
file/f <file path>: load a file (in interactive mode) or execute a file (in argument)
run <formula>: run a formula as command line and not triggering interactive mode
result_only: display only the result, ignoring the process of computation"

let rec commandAnalyser (commands : string list) : unit =
    // extract the first command
    let commands =
        match commands with
        | [] -> []
        | hd :: lst ->
            if hd.Length < 1 then
                (eprintfn "Not a valid Command String"; [])
            elif (Flags.IN_INTERACTIVE && hd.[0] <> '%') then (
                    eprintfn $"Not a valid Command Format {hd}";
                    []
                )
            elif  (not Flags.IN_INTERACTIVE && hd.[0] <> '-') then (
                    eprintfn $"Not a valid Command Format {hd}";
                    []
                )
            else
                hd.[1..] :: lst
    in
    let recall lst =
        (if Flags.IN_INTERACTIVE && lst <> [] then
            eprintfn $"""Invalid commands {String.concat " " commands}""");
        commandAnalyser lst
    in
    let triggerValues lst' modifier =
        match lst' with
        | "rv" :: lst | "recursive" :: "value" :: "mode" :: lst | "recursive_value_mode" :: lst ->
            Flags.LambdaOptions.RECURSIVE_VALUE_MODE <- modifier true;
            recall lst
        | "simplify_step" :: lst | "simplify" :: "step" :: lst | "sim_step" :: lst | "sim" :: "step" :: lst ->
            Flags.LambdaOptions.SIMPLIFY_EVERY_STEP <- modifier true;
            recall lst
        | "mute" :: lst | "silent" :: lst ->
            Flags.LambdaOptions.SILENT_MODE <- modifier true;
            recall lst
        | ("result_only" | "only_result") :: lst ->
            Flags.LambdaOptions.RESULT_ONLY <- modifier true;
            recall lst
        | "expand" :: lst ->
            Flags.LambdaOptions.SIMPLIFY_EVERY_STEP <- modifier false;
            recall lst
        | x :: lst ->
            eprintfn $"Invalid command: \"%%{x}\"";
            recall lst
        | [] -> ()
    in
    match commands with
    | "2v" :: lst | "toval" :: lst | "2val" :: lst | "tov" :: lst | "reduce" :: "to" :: "value" :: lst |
        "tovalue" :: lst | "2value" :: lst | "reduce_to_value" :: lst | "rtv" :: lst | "r2v" :: lst |
        "to_value" :: lst | "to" :: "value" :: lst
        ->
        Flags.LambdaOptions.MAXIMUM_REDUCTION <- None;
        recall lst
    | ("show_def" | "show" | "definitions") :: lst ->
        for e in nameTermBinding do
            let e = e :?> DictionaryEntry in
            let name, term = e.Key :?> string, e.Value :?> LambdaTerm<string> in
            if name.StartsWith '(' then
                printfn $"let mid {name.[1..(name.Length - 2)]} = {term}"
            else
                printfn $"let {name} = {term}"
        done;
        recall lst
    | ("max_steps" | "ms" | "maximum_steps") :: num :: lst | ("maximum" | "max") :: ("steps" | "step") :: num :: lst
        -> begin
        try
            Flags.LambdaOptions.MAXIMUM_REDUCTION <- Some $ UInt64.Parse num
        with
        | _ -> eprintfn "Warning: Invalid command, expected number specification after maximum reduction step command."
        end;
        recall lst
    | "cmp" :: lst | "compare" :: lst | "comparison" :: lst | "term_cmp" :: lst | "term_compare" :: lst | "term_comparison" :: lst |
        "term" :: ("cmp" :: lst | "compare" :: lst | "comparison" :: lst)
        ->
        Flags.LambdaOptions.OPERATION_MODE <- Flags.LTMComparison;
        recall lst
    | ("red" | "reduction" | "reduce") :: lst ->
        Flags.LambdaOptions.OPERATION_MODE <- Flags.LTMReduction;
        recall lst
    | "cbn" :: lst | "callbyname" :: lst | "call" :: "by" :: "name" :: lst | "call_by_name" :: lst ->
        Flags.LambdaOptions.REDUCTION_METHOD <- CallByName;
        recall lst
    | "cbv" :: lst | "callbyvalue" :: lst | "call" :: "by" :: "value" :: lst | "call_by_value" :: lst ->
        Flags.LambdaOptions.REDUCTION_METHOD <- CallByValue;
        recall lst
    | ("f" | "file") :: filePath :: lst ->
        (if Flags.IN_INTERACTIVE then fileAnalyser filePath
        else Flags.RUN_MODE <- Flags.RunAFile filePath);
        recall lst
    | ("load" | "file_load" | "load_file" | "fileload" | "loadfile") :: filePath :: lst ->
        fileAnalyser filePath;
        recall lst
    | ("run" | "instantrun" | "instant" | "instant_run" | "runinstant" | "run_instant") :: formula :: lst ->
        (if not Flags.IN_INTERACTIVE then (
            Flags.INPUT_MODE <- Flags.LambdaMode;
            Flags.RUN_MODE <- Flags.RunAString formula)
        else lineAnalyser formula);
        recall lst
    | ("clear" | "c") :: lst ->
        nameTermBinding.Clear ();
        termNameBinding.Clear ();
        recall lst
    | "help" :: lst ->
        printHelper ();
        recall lst
    | "quit" :: _ | "exit" :: _ ->
        raise ReturnMark
    | "not" :: lst ->
        triggerValues lst not
    | lst -> triggerValues lst id
    
/// analyse the command string, used in interactive mode, split the string
and commandStrAnalyser (commandStr : string) =
    let commandStr = commandStr.Replace("\\ ", "\n") in
    let commandStr = commandStr.Trim () in
    commandStr.Split ' '
    |> Array.map (fun (str : string) -> str.Replace("\n", " "))
    |> List.ofArray
    |> List.filter (String.IsNullOrEmpty >> not)
    |> List.map (fun (s : string) -> s.ToLower ())
    |> commandAnalyser

and lineAnalyser (lineStr : string) : unit =
    let lineStr = lineStr.Trim () in
    if String.IsNullOrEmpty lineStr then ()
    elif lineStr.[0] = '%' then commandStrAnalyser lineStr
    elif lineStr.Trim().StartsWith "let" then begin
        let msgs = analyseStrWith lineStr let_line ||> addBinding in
        if Flags.LambdaOptions.SILENT_MODE |> not then
            for msg in msgs do eprintfn $"{msg}" done
    end
    elif Flags.INPUT_MODE = Flags.ModeType.LambdaMode then
        lambdaAnalyser $ analyseStrWith lineStr lambda_line
    elif Flags.INPUT_MODE = Flags.ModeType.PiMode then piAnalyser $ analyseStrWith lineStr pi_line
    else ()

and stringAnalyser (str : string) : unit =
    let lines = preprocess str in
    let lines =
        Array.map (fun (s : string) -> s.Trim ()) lines
        |> Array.filter (String.IsNullOrEmpty >> not)
    in
    for lineStr in lines do
        try
            lineAnalyser $ lineStr.Trim ()
        with
        | e -> eprintfn $"{e.Message}"
    done
    
and fileAnalyser (filePath : string) : unit =
    let s =
        use ss = new StreamReader(filePath) in
        ss.ReadToEnd ()
    in
    stringAnalyser s

let AnalyseCommandLine args =
    commandAnalyser args;
    match Flags.RUN_MODE with
    | Flags.RunAFile filePath -> fileAnalyser filePath
    | Flags.RunAString str -> stringAnalyser str
    | Flags.RunInteractive ->
        Flags.IN_INTERACTIVE <- true;
        printfn "Interactive Mode, use %%exit or %%quit to exit, %%help to get more information";
        try
            while true do
                printf " - : ";
                let mutable input = Console.ReadLine () in
                let _ =
                    while input.EndsWith '\\' do
                        input <- input.[..(input.Length - 2)] + " " + Console.ReadLine ()
                    done
                in
                try
                    lineAnalyser input
                with
                | :? ReturnMark -> reraise ()
                | e -> eprintfn $"{e.Message}"
            done
        with
        | :? ReturnMark -> ()

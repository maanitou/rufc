module Interpreter

open Ast
open SymTab
open Tools
open Inverter

exception InterpreterError of string

let error str = raise (InterpreterError str)

let mutable write_output_filename = "output.txt"

type QValue = Qualifier * Value

type State =
    { mutable FromLabel: Label
      mutable ToLabel: Label
      mutable Ftab: SymTab<Proc>
      mutable Vtab: SymTab<QValue> }

    member this.IsHalting() = this.ToLabel.StartsWith "Halt"

let isConst (vtab: SymTab<QValue>) (lvalue: LVal) =
    let name = lvalue.Identifier
    match lookup name vtab with
    | (Const, _) -> true
    | _ -> false

/// Verify that all parameters qualified by `qual` are  bound to a zeroed value
let assertParamsAreZeroed tab qual pars =
    match pars
          |> List.tryFind
              (fun (q, _, n) ->
                  q = qual
                  && not (lookup n tab |> fun (_, x: Value) -> x.IsZeroed)) with
    | None -> ()
    | Some (_, _, n') -> error $"{qual} parameter {n'} is not zeroed {lookup n' tab}"

/// Evaluates an expression
let rec evalExpr (vtab: SymTab<QValue>) expr : Value =
    match expr with
    | Constant v -> IntVal v
    | LVal (Var name) ->
        match tryLookup name vtab with
        | None -> error $"variable {name} is not defined yet"
        | Some value -> value |> snd
    | LVal (Index (name, e)) ->
        match (tryLookup name vtab) with
        | None -> error $"array {name} is not defined yet"
        | Some (_, ArrayVal arr) ->
            match evalExpr vtab e with
            | IntVal (_, idx) -> arr.[idx] |> IntVal
            | _ -> error "Index: index must be an integer value"
        | Some _ -> error "Index: index lookup in array values only"

    | BinOp (op, e1, e2) ->
        match (evalExpr vtab e1, evalExpr vtab e2) with
        | (IntVal (_, v1), IntVal (_, v2)) -> (applyBinOp op v1 v2) |> fun v -> IntVal("", v)
        | (_) -> error "BinOp: can only apply binary operator to integer values"

    | Not e ->
        match evalExpr vtab e with
        | IntVal (_, 0) -> IntVal("", 1)
        | IntVal _ -> IntVal("", 0)
        | _ -> error "Not: can only be applied to an interer value"

    | Top (Var stackName) ->
        match lookup stackName vtab with
        | (_, StackVal []) -> error "Top: stack is empty"
        | (_, StackVal (hd :: _)) -> IntVal hd
        | _ -> error "Top: cannot apply top to non-stack"
    | Top _ -> error "Top: cannot apply top to array element"

    | Empty (Var stackName) ->
        match lookup stackName vtab with
        | (_, StackVal []) -> IntVal("", 1)
        | (_, StackVal _) -> IntVal("", 0)
        | _ -> error "Empty: cannot apply empty to non-stack"
    | Empty _ -> error "Empty: cannot apply top to array element"


/// Evaluates a sequence of statements
let rec evalStatements (state: State) (stmts: Statement list) = //(ftab: SymTab<Proc>) vtab  =
    (state, stmts) ||> List.fold evalStmt

/// Evaluates a statement
and evalStmt (state: State) stmt : State =
    match stmt with
    | AssignOp (op, lval, e) -> { state with Vtab = assign state.Vtab op lval e }
    | Skip -> state
    | Swap (lval1, lval2) ->
        match (lookup lval1.Identifier state.Vtab, lookup lval2.Identifier state.Vtab) with
        | ((Const, _), _) -> error "cannot swap const l-value"
        | (_, (Const, _)) -> error "cannot swap const l-value"
        | (qval1, qval2) ->
            { state with Vtab = updateLVal lval2 qval1 (updateLVal lval1 qval2 state.Vtab) }

    | Call (procName, concreteArgs) ->
        match tryLookup procName state.Ftab with
        | None -> error $"Call: procedure {procName} is not defined"
        | Some proc ->
            let (ftab', vtab') =
                evalProc state.Ftab state.Vtab concreteArgs proc
            { state with Ftab = ftab'; Vtab = vtab' }

    | Uncall (procName, concreteArgs) ->
        // Uncalling is equivalent to Calling the inverse procedure
        match tryLookup procName state.Ftab with
        | None -> raise (InterpreterError $"Uncall: procedure {procName} is not defined")
        | Some proc ->

            let procNameInv = invertProcName procName

            match tryLookup procNameInv state.Ftab with
            | None -> // The inversed procedure has not been added to ftab yet

                // NOTE: The Inverter has two purposes:
                //   1) Invert programs in order to produce an inverted program that can be
                //      evaluated as a separate entity.
                //   2) Uncall a procedure by calling its inverse.

                let local = true // We are uncalling a proc, not inverting a program.

                let procInv = invertProc local proc

                let ftab' =
                    bind (procInv |> getProcName) procInv state.Ftab

                evalStmt { state with Ftab = ftab' } (Call(procNameInv, concreteArgs))

            | Some _ ->
                // If the inversed procedure has already been added to ftab, then call it
                evalStmt state (Call(procNameInv, concreteArgs))


    | Push (lval, (Var stackName)) ->
        match lookup stackName state.Vtab with
        | (q, StackVal stack) ->
            match evalExpr state.Vtab (LVal lval) with
            | IntVal n ->
                // update stack with pushed value
                let vtab' =
                    updateLVal (Var stackName) (q, StackVal(n :: stack)) state.Vtab

                // nullify the pushed l-val
                let (q1, _) = lookup lval.Identifier vtab'

                { state with Vtab = updateLVal lval (q1, IntVal("", 0)) vtab' }

            | _ -> error "Push: can only push integer values"
        | _ -> error "Push: can only push to a stack"
    | Push _ -> error "Push: array elements cannot be stacks"

    | Pop (lval1, (Var stackName)) ->
        match evalExpr state.Vtab (LVal lval1) with
        | IntVal (_, 0) ->
            match lookup stackName state.Vtab with
            | (q, StackVal []) -> error "Pop: empty stack"
            | (q, StackVal (hd :: tl)) ->
                let (q1, _) = lookup lval1.Identifier state.Vtab
                let vtab' =
                    updateLVal lval1 (q1, IntVal hd) state.Vtab
                { state with Vtab = updateLVal (Var stackName) (q, StackVal tl) vtab' }

            | _ -> error "Pop: can only pop from a stack"
        | IntVal _ -> error "Pop: destination is not zero-cleared"
        | _ -> error "Pop: destination must be a variable or an array element"
    | Pop _ -> error "Pop: array elements cannot be stacks"

    | Write name ->
        let number2str =
            function
            | ("", v) -> v |> string
            | (tag, _) -> tag

        let output' =
            match lookup name state.Vtab with
            | (_, IntVal n) -> n |> number2str

            | (_, ArrayVal arr) ->
                [ for x in arr do
                      yield $"{x |> number2str}" ]
                |> String.concat " "
            | (_, StackVal stack) ->
                "S{"
                + ([ for x in stack do
                         yield $"{x |> number2str}" ]
                   |> String.concat " ")
                + "}"

        let output = $"{name}={output'}"

        if write_output_filename = "" then
            printfn $"{output}\n"
        else
            System.IO.File.AppendAllText(write_output_filename, $"{output}\n")

        state

    | BLocal (t, id, n) ->
        // Bind a block-local to the vtab
        { state with Vtab = bind id (BlockLocal, IntVal n) state.Vtab }

    | BDelocal (t, id, n) ->
        // Unbind a block-local from the vtab after asserting that it equals the expected value
        match tryLookup id state.Vtab with
        | None -> error $"trying to block-delocal {id} that is not defined yet"
        | Some (BlockLocal, v) ->
            let expected = (BlockLocal, IntVal n)
            let actual = (BlockLocal, v)

            if actual <> expected then
                error $"bdelocal: expected {expected} does not match actual {actual}"
        | Some (_, _) ->
            error $"bdelocal: trying to block-delocal a variable {id} which is not block-local"

        { state with Vtab = unbind id state.Vtab }


/// Evaluates an assignment, op=
and assign vtab op lval e =
    match lval with
    | Var id -> assignVar vtab op id e
    | Index (id, idx) -> assignIndex vtab op id idx e

and assignVar vtab op name (e: Expr) : SymTab<Qualifier * Value> =
    match (lookup name vtab, evalExpr vtab e) with
    | ((q1, IntVal (_, v1)), IntVal (_, v2)) ->
        match q1 with
        | Const -> error $"Cannot assign the CONST variable {name}"
        | _ -> update name (q1, applyAssignOp op v1 v2 |> fun v -> IntVal("", v)) vtab
    | _ -> error "AssigVar: lhs and rhs must be integer values"

and assignIndex vtab op name e1 e2 =
    match lookup name vtab with
    | (q, ArrayVal arr) ->
        match (q, evalExpr vtab e1) with
        | (Const, _) -> error $"Cannot assign element in CONST array {name}"
        | (q, IntVal (_, idx)) ->
            match (arr.[idx], evalExpr vtab e2) with
            | ((_, v1), IntVal (_, v2)) ->
                Array.set arr idx (applyAssignOp op v1 v2 |> fun v -> ("", v))
                update name (q, ArrayVal arr) vtab
            | _ -> error "AssignAdd: array elements must be integers"
        | _ -> error "AssignAdd: array index must be an integer value"

    | _ -> error "AssignAdd: index lookups can only be made in arrays"


/// Update l-value. Used in swap, push, and pop.
and updateLVal
    (lhs: LVal)
    (qvalue: Qualifier * Value)
    (vtab: SymTab<Qualifier * Value>)
    : SymTab<Qualifier * Value> =
    match qvalue with
    | (q, IntVal v) ->
        match lhs with
        | Var name -> update name (q, IntVal v) vtab
        | Index (name, idx) ->
            match (lookup name vtab, evalExpr vtab idx) with
            | ((_, ArrayVal arr), IntVal (_, i)) ->
                arr.[i] <- v
                update name (q, ArrayVal arr) vtab
            | ((_, ArrayVal _), _) -> failwith "internal error: an index must be an integer"
            | ((_, StackVal _), _) -> failwith $"internal error: stack `{name}` is used as an array"
            | ((_, IntVal _), _) ->
                failwith $"internal error: variable `{name}` is used as an array"
    | (q, ArrayVal v) ->
        match lhs with
        | Var name -> update name (q, ArrayVal v) vtab
        | Index (_, _) -> error "internal error: array elements cannot be arrays" // No 2-dim arrays
    | (q, StackVal v) ->
        match lhs with
        | Var name -> update name (q, StackVal v) vtab
        | Index (_, _) -> error "internal error: array elements cannot be stacks"


/// Evaluates a block
and evalBlock (state: State) (Block (label, arrival, statements, departure)) =

    if (state.ToLabel <> label) then
        error
            $"Inconsistent state: '{state.ToLabel}' is different from current block label '{label}'"

    match arrival with
    | Entry -> 0
    | From lab when lab = state.FromLabel -> 0
    | From lab ->
        error $"In block '{label}': expected to come from '{state.FromLabel}', but  came from {lab}"
    | FiFrom (e, lab) ->
        match (evalExpr state.Vtab e) with
        | IntVal (_, 0) -> error $"In block '{label}': entry condition must evaluate to true"
        | IntVal _ when lab = state.FromLabel -> 0
        | _ -> error $"In block '{label}': entry condition must be an integer value"
    | FiFromElse (e, labT, labF) ->
        match (evalExpr state.Vtab e, state.FromLabel) with
        | (IntVal (_, 0), lab) when lab = labF -> 0
        | (IntVal (_, 0), lab) ->
            error $"In block '{label}': expected to come from '{labF}', but  came from '{lab}'"
        | (IntVal _, lab) when lab = labT -> 0
        | (IntVal _, lab) ->
            error $"In block '{label}': expected to come from '{labT}', but  came from '{lab}'"
        | _ -> error "FiFromElse: condition must be an integer value"
    |> ignore

    match state.Vtab
          |> SymTab.toList
          |> List.filter (fun (id, (q, v)) -> q = BlockLocal) with
    | [] -> ()
    | (id, (q, v)) :: _ ->
        error
            $"block-local {id} should not be present on the vtab when entering {label} from {state.FromLabel}"

    let state' = evalStatements state statements

    match state'.Vtab
          |> SymTab.toList
          |> List.filter (fun (id, (q, v)) -> q = BlockLocal) with
    | [] -> ()
    | (id, (q, v)) :: _ ->
        error $"block-local {id} has not been delocalled before leaving block {label}"

    match departure with
    | Exit -> { state' with FromLabel = label; ToLabel = $"Halt" }
    | Goto lab -> { state' with FromLabel = label; ToLabel = lab }
    | IfGoto (e, lab) ->
        match evalExpr state'.Vtab e with
        | IntVal (_, 0) -> error $"In block '{label}': departure condition must evaluate to true"
        | IntVal _ -> { state' with FromLabel = label; ToLabel = lab }
        | _ -> error $"In block '{label}': departure condition must be an integer value"
    | IfGotoElse (e, labT, labF) ->
        match evalExpr state'.Vtab e with
        | IntVal (_, 0) -> { state' with FromLabel = label; ToLabel = labF }
        | IntVal _ -> { state' with FromLabel = label; ToLabel = labT }
        | _ -> error "IfGotoElse: condition must be an integer value"


/// Jump to the block specified by the current state
and jumpTo blockMap (state: State) =
    match tryLookup state.ToLabel blockMap with
    | None -> error $"jumping no non-existing label: {state.ToLabel}"
    | Some b -> evalBlock state b

/// Creates a mapping of labels to blocks, and returns the entry point
and createBlockMap blocks =
    let rec loop blks entry map =
        match blks with
        | [] ->
            if (entry = "") then
                error "program has no entry point"

            (entry, map)

        | hd :: tl ->
            match hd with
            | Block (label, arrival, _, _) ->
                if label = entry then
                    error "multiple entry points"

                let entry' = if arrival = Entry then label else entry
                loop tl entry' ((label, hd) :: map)

    loop blocks "" []
    |> fun (entry, map) -> (entry, map |> Map.ofList |> SymTab)

/// Update vtab of caller when callee exits
and restoreVTab
    (formalToConcrete: List<Identifier * Identifier>)
    (vtabCallee: SymTab<Qualifier * Value>)
    (vtabCaller: SymTab<Qualifier * Value>)
    : SymTab<Qualifier * Value> =

    let updater (f: Identifier) (c: Identifier) vtabC =
        match (lookup f vtabCallee, lookup c vtabC) with
        | ((Const, _), (_, _)) -> vtabC //Note: can only bind Const arguments to formal Const parameters
        | ((_, IntVal vf), (qC, IntVal _)) -> update c (qC, IntVal vf) vtabC
        | ((_, ArrayVal arrf), (qC, ArrayVal _)) -> update c (qC, ArrayVal arrf) vtabC
        | ((_, StackVal stackf), (qC, StackVal _)) -> update c (qC, StackVal stackf) vtabC
        | _ -> error "restoreVTab: type mismatch"

    List.fold (fun acc (f, c) -> updater f c acc) vtabCaller formalToConcrete


/// Returns:
///  - New VTab binding formal parameters to the concrete parameter values
///  - Mapping from formal parameters to concrete parameters
and bindConcreteArgs (concreteArgs: Arg list) (formalParams: Param list) =

    match (List.length concreteArgs, List.length formalParams) with
    | (m, n) when m <> n ->
        error $"Number of  concrete and formal parameters do not match: {m} <> {n}"
    | _ -> ()

    let assertPreserveConst concrete formal =
        match (concrete, formal) with
        | ((cq, _, _), (fq, _, _)) ->
            if cq = Const && fq <> Const then
                error "Cannot bind a const argument to a non-const formal parameter"

    let bindSafely tab concrete formal =
        match (concrete, formal) with
        | ((_, IntVal cv, _), (fq, Int, fid)) -> bind fid (fq, IntVal cv) tab
        | ((_, ArrayVal cv, _), (fq, Array, fid)) -> bind fid (fq, ArrayVal cv) tab
        | ((_, StackVal cv, _), (fq, Stack, fid)) -> bind fid (fq, StackVal cv) tab
        | ((_, cv, _), (_, ft, _)) ->
            error $"Formal and concrete parameter type mismatch: {cv} is not an {ft}"

    let procVTab =
        (empty, concreteArgs, formalParams)
        |||> List.fold2
                 (fun tab c f ->
                     assertPreserveConst c f
                     bindSafely tab c f)

    let fcMap =
        (formalParams, concreteArgs)
        ||> List.map2 (fun (_, _, fn) (_, _, cn) -> (fn, cn))

    (procVTab, fcMap)


/// Evaluates a procedure
and evalProc
    ftab
    (vtab: SymTab<Qualifier * Value>)
    arguments
    (Proc (procName, formalParams, locals, blocks, delocals))
    =

    // Retrieves concrete values and qualifiers from the vtab
    // Note that the concrete argument list is passed separately, mainly to preserved
    // the order of the concrete arguments used at the procedure call.
    let concreteArgs =
        arguments
        |> List.map
            (fun id ->
                let (q, v) = lookup id vtab
                (q, v, id))

    // vtabIn: Symbol table in which formal parameters are bound to the concrete argument values
    // fcMap: Maps formal parameter names to concrete argument names
    let (vtabProcIn, fcMap) =
        bindConcreteArgs concreteArgs formalParams

    // Verify that all OUT parameters are bound to a zeroed value.
    (Out, formalParams)
    ||> assertParamsAreZeroed vtabProcIn

    // Bind locals to var table
    // Note that a local may be defined in terms of other already defined locals
    let vtabProcInWithLocals =
        (vtabProcIn, locals)
        ||> List.fold
                (fun tab (t, id, e) ->
                    match e with
                    | Constant number -> bind id (Local, IntVal number) tab
                    | LVal (Var name) ->
                        match tryLookup name vtabProcIn with
                        | None -> error $"variable {name} has not been defined yet"
                        | Some (_, IntVal v) -> bind id (Local, IntVal v) tab
                        | _ -> error $"local {id} must be integer valued"
                    | _ -> error $"not implemented: assigning an array element to a local ")


    // Asser that procedure has exactly one entry block
    match blocks
          |> List.filter (fun (Block (_, a, _, _)) -> a = Entry) with
    | [] -> error $"proc {procName} has no entry block"
    | _hd1 :: _hd2 :: _ -> error $"proc {procName} has multiple entry blocks"
    | _hd :: _ -> ()

    // Create a block map which is local to the current procedure
    let (entryLabel, blockMap) = createBlockMap blocks

    let mutable state: State =
        { FromLabel = entryLabel; ToLabel = entryLabel; Ftab = ftab; Vtab = vtabProcInWithLocals }

    while not (state.IsHalting()) do
        state <- jumpTo blockMap state

    let (SymTab vtabOut') = state.Vtab
    let ftabOut = state.Ftab

    let removeTag (_, n) = ("", n)

    let assertDelocal tab (_, id, e) =
        match (lookup id tab, evalExpr tab e) with
        | ((_, IntVal (_, n)), IntVal (_, m)) when m = n -> ()
        | ((_, IntVal (_, n)), IntVal (_, m)) ->
            error $"delocal: {id} expected to be {m} but was {n}"
        | ((_, IntVal (_, n)), _) -> error $"delocal {id}: expected value must be an integer"
        | (_, _) -> error $"delocal {id}: only integer values are authorized"

    delocals
    |> List.iter (fun dloc -> assertDelocal (vtabOut' |> SymTab) dloc)
    |> ignore

    // Un-bind locals from var table
    let vtabOut =
        Map.filter (fun id (k, v) -> k <> Local) vtabOut'
        |> SymTab

    // Verify that all IN parameters are bound to a zeroed value
    (In, formalParams)
    ||> assertParamsAreZeroed vtabOut

    let updatedVTab = restoreVTab fcMap vtabOut vtab
    (ftabOut, updatedVTab)


/// Evaluates a program.
let rec evalProgram writeFileName (args: (string * Value) list) (Program (defs, procs): Program) =

    System.IO.File.WriteAllText(writeFileName, "")

    write_output_filename <- writeFileName

    // Resolve the main procedure
    let mainProc: Proc =
        match List.filter (fun (Proc (n, _, _, _, _)) -> n = "main") procs with
        | [] -> error "no main procedure"
        | hd :: [] -> hd
        | _ -> error "more than one main procedure"

    // Construct the vtab. Initial concrete arguments are classified as locals (we need a qualifier).
    // Whether their values are in accordance with the formal parameter qualifiers
    // will be checked when executing the procedure body.
    // Also, the initial concrete argument names should match the formal parameter
    // name of the main procedure.
    let vtab: SymTab<Qualifier * Value> =
        List.map (fun (k, v) -> (k, (Local, v))) args
        |> SymTab.ofList

    // Construct the procedure table
    let ftab: SymTab<Proc> =
        procs
        |> List.fold (fun acc p -> ((getProcName p, p) :: acc)) []
        |> SymTab.ofList

    //printfn $"vtab in:\n {vtab}\n"

    let vtabOut =
        evalProc
            ftab
            vtab
            (getProcParams mainProc
             |> List.map (fun (q, t, n) -> n))
            mainProc

    vtabOut

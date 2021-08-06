module Divisor

open Ast
open SymTab
open Tools

/// Binding is either Static or Dynamic
type Division = SymTab<Binding>

exception DivisorError of string
let error str = DivisorError str |> raise

type State() =
    let mutable mapping =
        Map.empty<string * Division, Division option>

    member _.Get() = mapping
    member this.AddKey(k) =
        if not <| (Map.containsKey k mapping) then
            mapping <- Map.add k None mapping
        this

    member this.Add(k, v) =
        mapping <- Map.add k v mapping
        this

    member _.TryPickEmpty() =
        mapping
        |> Map.tryPick
            (fun k v ->
                match v with
                | None -> Some k
                | Some _ -> None)

/// Returns the binding, either static or dynamic, of an expression.
let rec divExpr (div: Division) =
    function
    | Constant _ -> S
    | LVal (Var id) -> lookup id div
    | LVal (Index (id, idx)) ->
        match (lookup id div, divExpr div idx) with
        | (S, S) -> S
        | _ -> D
    | BinOp (_, e1, e2) ->
        match (divExpr div e1, divExpr div e2) with
        | (S, S) -> S
        | _ -> D
    | Not e -> divExpr div e
    | Top (Var stack) -> lookup stack div
    | Top _ -> error "cannot apply `top` to array element"
    | Empty (Var stack) -> lookup stack div
    | Empty _ -> error "cannot apply `empty` to array element"

/// Returns an updated division resulting from evaluating a statement
let rec divStatement
    (ftab: SymTab<Proc>)
    (div: Division)
    (stmt: Statement)
    (state: State)
    : Division * SymTab<Proc> * State =
    match stmt with
    | AssignOp (_, Var name, e) ->
        let div' =
            match (lookup name div, divExpr div e) with
            | (S, D) -> update name D div
            | _ -> div
        (div', ftab, state)

    | AssignOp (_, Index (name, idx), e) ->
        let div' =
            match (lookup name div, divExpr div idx, divExpr div e) with
            // An array index by a dynamic index expression is dynamic [Mogensen]
            | (S, D, _) -> update name D div
            // If at least one element of an array is dynamic, then all elements of the array
            // (i.e. the array itself) are dynamic.
            | (S, _, D) -> update name D div
            | _ -> div
        (div', ftab, state)

    | Skip -> (div, ftab, state)

    | Swap (lval1, lval2) ->
        let div' =
            match (divExpr div (LVal lval1), divExpr div (LVal lval2)) with
            | (S, S) -> div
            | (S, D) -> update (lval1 |> getLValId) D div
            | (D, S) -> update (lval2 |> getLValId) D div
            | (D, D) -> div
        (div', ftab, state)

    | Call (procName, concreteArgs) ->
        match tryLookup procName ftab with
        | None -> error $"procedure {procName} is not defined"
        | Some (Proc (pid, formalPars, _, _, _) as proc) ->

            // Division of the concrete arguments
            let concreteArgsDiv: (Identifier * Binding) list =
                concreteArgs
                |> List.map (fun id -> (id, lookup id div))

            // Raw original binding of the formal parameters.
            let rawFormalParamsDiv: Division =
                (concreteArgsDiv, formalPars)
                ||> List.map2 (fun (cid, d) (q, t, fid) -> (fid, d))
                |> SymTab.ofList

            // If all input arguments are static, then static arguments passed to InOut and Out parameters are allowed to remain static, in other terms, the division is unchanged.
            let isCallDynamic: bool =
                (concreteArgsDiv, formalPars)
                ||> List.map2 (fun (cid, d) (q, t, fid) -> (d, q))
                |> List.exists (fun (d, q) -> d = D && (q = In || q = InOut || q = Const))

            // Division of local variables right after the procedure call.
            let divOut: Division =
                match isCallDynamic with
                | false ->
                    // If the call is static, the call statement will be eliminated, leaving
                    // the divison unaltered.
                    div
                | true ->
                    (div, concreteArgsDiv, formalPars)
                    |||> List.fold2
                             (fun acc (cid, d) (q, _, _) ->
                                 match (d, q) with
                                 | (_, BlockLocal) ->
                                     error "call: formal parameter cannot be BlockLocal."
                                 | (_, Local) -> error "call: formal parameter cannot be Local."
                                 | (D, _) -> update cid D acc //TODO: Should be D already?
                                 | (S, Const) -> acc
                                 | (S, In) -> acc
                                 | (S, InOut) -> update cid D acc
                                 | (S, Out) -> update cid D acc)

            (divOut, ftab, state.AddKey((pid, rawFormalParamsDiv)))


    | Uncall (procName, concreteArgs) ->
        match tryLookup procName ftab with
        | None -> error $"procedure {procName} is not defined"
        | Some proc ->
            let procNameInv = invertProcName procName

            match tryLookup procNameInv ftab with
            | None ->
                // The inversed procedure has not been added to ftab yet
                let local = true // We are uncalling a proc, not inverting a program.

                let procInv = Inverter.invertProc local proc

                let ftab' = bind procInv.Name procInv ftab

                divStatement ftab' div (Call(procNameInv, concreteArgs)) state

            | Some _ ->
                // If the inversed procedure has already been added to ftab, then call it
                divStatement ftab div (Call(procNameInv, concreteArgs)) state

    | Push (lval, stack) ->
        // Here, we assume that stack is a Var, but we don't have to
        let div' =
            match (divExpr div (LVal lval), lookup (stack |> getLValId) div) with
            | (D, S) ->
                printfn "pushing dynamic value to static stack"
                update (stack |> getLValId) D div // If a dynamic element is pushed onto the stack, the stack is  dynamic
            | _ -> div

        (div', ftab, state)

    | Pop (lval, stack) ->
        let div' =
            match (divExpr div (LVal lval), lookup (stack |> getLValId) div) with
            | (S, D) -> update (lval |> getLValId) D div // Popped elements from a dynamic stack are also dynamic
            | _ -> div

        (div', ftab, state)

    | Write _ -> (div, ftab, state)

    | BLocal (t, id, number) -> (div, ftab, state)
    | BDelocal _ -> (div, ftab, state)

and divBlock (ftab: SymTab<Proc>) (div: Division) (Block (_, _, stmts, _)) (state: State) =
    let (div', ftab', state') =
        ((div, ftab, state), stmts)
        ||> List.fold (fun (d, tab, s) stmt -> divStatement tab d stmt s)

    (div', ftab', state')

/// Computes the SD-division of a procedure given an initial division
and uniformDivProc
    (state: State)
    ftab
    (intialParamsDiv: Division)
    (Proc (pid, pars, locals, blocks, delocals))
    =

    let isCallDynamic: bool =
        pars
        |> List.exists
            (fun (q, t, n) ->
                let d = lookup n intialParamsDiv
                d = D && (q = In || q = InOut || q = Const))

    // If all input parameters are static according to the initial division, then all parameters will be static locally to the procedure body. In other words, we will be able to fully evaluate the procedure.
    let actualInitialParamsDiv: Division =
        match isCallDynamic with
        | true -> intialParamsDiv
        | false ->
            let parNames = pars |> List.map (fun (q, t, n) -> n)

            List.zip parNames (List.replicate (List.length pars) S)
            |> SymTab.ofList

    // Combine division of formal parameters with the locals, which are initially all static.
    let initialDivNoBlockLocals: SymTab<Binding> =
        (actualInitialParamsDiv, locals)
        ||> List.fold (fun tab (t, id, n) -> bind id S tab)

    // Combining division with block-locals, which are also static.
    let initialDiv =
        (initialDivNoBlockLocals, getBlockLocals blocks)
        ||> List.fold (fun tab id -> bind id S tab)

    // Procedure calls that have been collected.
    let mutable state_mut = state
    let mutable ftab_mut = ftab
    let mutable div_mut = initialDiv
    let mutable div_old = empty

    let mutable i = 1

    while div_old <> div_mut do
        i <- i + 1
        div_old <- div_mut

        let (div_mut', ftab_mut', state_mut') =
            ((div_mut, ftab_mut, state_mut), blocks)
            ||> List.fold (fun (d, tab, s) b -> divBlock tab d b s)

        div_mut <- div_mut'
        ftab_mut <- ftab_mut'
        state_mut <- state_mut'

    (ftab_mut, state_mut.Add((pid, intialParamsDiv), Some div_mut))

and getBlockLocals blocks =

    let getLocalVarsInBlock
        (Block (label, _, stmts, _) as block)
        : Label * Identifier list * Identifier list =
        let (locals, delocals) =
            (([], []), stmts)
            ||> List.fold
                    (fun (acc1, acc2) stmt ->
                        match stmt with
                        | BLocal (t, id, number) -> (id :: acc1, acc2)
                        | BDelocal (t, id, number) -> (acc1, id :: acc2)
                        | _ -> (acc1, acc2))

        (label, locals, delocals)

    blocks
    |> List.collect (
        getLocalVarsInBlock
        >> (fun (label, locals, delocals) ->
            let set1 = Set.ofList locals
            let set2 = Set.ofList delocals

            if set1.Count <> locals.Length then
                error $"block-local names must be unique within a procedure"

            if set2.Count <> delocals.Length then
                error $"block-delocal names must be unique within a procedure"

            if (not (Set.isSubset set1 set2))
               || (not (Set.isSubset set2 set1)) then
                error $"block-local and block-delocal in block {label} do not match"

            locals)
    )




/// Computes the uniform division of a program
let uniformDivision (initialDiv: SymTab<Binding>) (Program (decls, procs)) : State =

    let mainId = "main"

    // Resolve the main procedure
    let mainProc: Proc =
        match List.filter (fun (proc: Proc) -> proc.Name = mainId) procs with
        | [] -> error "no main procedure"
        | [ hd ] -> hd
        | _ -> error "more than one main procedure"

    // Construct the procedure table
    let ftab: SymTab<Proc> =
        procs
        |> List.fold (fun acc proc -> (proc.Name, proc) :: acc) []
        |> Map.ofList
        |> SymTab

    let mainInitialDiv: Division =
        (SymTab.empty, mainProc.Params)
        ||> List.fold (fun acc (q, t, fid) -> bind fid (lookup fid initialDiv) acc)


    let rec loop tab (state: State) =
        match state.TryPickEmpty() with
        | None -> state
        | Some (currentProcId, currentInitialDiv) ->
            let proc =
                match tryLookup currentProcId tab with
                | None -> error $"{currentProcId} not found in Ftab"
                | Some p -> p

            let newFtab, newState =
                uniformDivProc state tab currentInitialDiv proc

            loop newFtab newState

    let state = State().AddKey((mainId, mainInitialDiv))

    loop ftab state

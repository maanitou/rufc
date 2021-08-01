module Divisor

open Ast
open SymTab
open Tools

/// Binding is either Static or Dynamic
type Division = SymTab<Binding>

exception DivisorError of string
let error str = DivisorError str |> raise

let mutable globalFTab: SymTab<Proc> = empty

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

/// Returns an updated division resulting from evaluating an expression
let rec divStatement (ftab: SymTab<Proc>) (div: Division) stmt procs : Division * (list<Identifier * Division>) =
    match stmt with
    | AssignOp (_, Var name, e) ->
        let div' =
            match (lookup name div, divExpr div e) with
            | (S, D) -> update name D div
            | _ -> div

        (div', procs)
    | AssignOp (_, Index (name, idx), e) ->
        let div' =
            match (lookup name div, divExpr div idx, divExpr div e) with
            | (S, D, _) -> update name D div // An array index by a dynamic index expression is dynamic [Mogensen]
            | (S, _, D) -> update name D div // If one element of an array is (or becomes) dynamic, all elements of the array (i.. the array itself) are dynamic.
            | _ -> div

        (div', procs)

    | Skip -> (div, procs)

    | Swap (lval1, lval2) ->
        let div' =
            match (divExpr div (LVal lval1), divExpr div (LVal lval2)) with
            | (S, S) -> div
            | (S, D) -> update (lval1 |> getLValId) D div
            | (D, S) -> update (lval2 |> getLValId) D div
            | (D, D) -> div

        (div', procs)


    | Call (procName, concreteArgs) ->
        match tryLookup procName ftab with
        | None -> error $"procedure {procName} is not defined"
        | Some (Proc (pid, formalPars, _, _, _) as proc) ->

            // Division of the concrete arguments
            let concreteArgsDiv: (Identifier * Binding) list =
                concreteArgs
                |> List.map (fun id -> (id, lookup id div))

            // Raw original binding of the formal parameters
            let rawFormalParamsDiv: Division =
                (concreteArgsDiv, formalPars)
                ||> List.map2 (fun (cid, d) (q, t, fid) -> (fid, d))
                |> SymTab.ofList

            // if all input arguments are static, then static arguments passed to InOut and Out parameters are allowed to remain tatic, in other terms, the division is unchanged
            let isCallDynamic: bool =
                (concreteArgsDiv, formalPars)
                ||> List.map2 (fun (cid, d) (q, t, fid) -> (d, q))
                |> List.exists (fun (d, q) -> d = D && (q = In || q = InOut || q = Const))

            let divOut: Division =
                match isCallDynamic with
                | false ->
                    // if the call is static, the call statement will be eliminated, leaving unaltered the divison
                    // of the caller variables.
                    div
                | true ->
                    (div, concreteArgsDiv, formalPars)
                    |||> List.fold2
                             (fun acc (cid, d) (q, _, _) ->
                                 match (d, q) with
                                 | (_, BlockLocal) -> error "call: formal parameter cannot be BlockLocal."
                                 | (_, Local) -> error "call: formal parameter cannot be Local."
                                 | (D, _) -> update cid D acc
                                 | (S, Const) -> acc
                                 | (S, In) -> acc
                                 | (S, InOut) -> update cid D acc
                                 | (S, Out) -> update cid D acc)

            (divOut, (pid, rawFormalParamsDiv) :: procs)


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

                let ftab' =
                    bind (procInv |> getProcName) procInv ftab

                globalFTab <- ftab'
                divStatement ftab' div (Call(procNameInv, concreteArgs)) procs

            | Some _ ->
                // If the inversed procedure has already been added to ftab, then call it
                divStatement ftab div (Call(procNameInv, concreteArgs)) procs

    | Push (lval, stack) ->
        // Here, we assume that stack is a Var, but we don't have to
        let div' =
            match (divExpr div (LVal lval), lookup (stack |> getLValId) div) with
            | (D, S) ->
                printfn "pushing dynamic value to static stack"
                update (stack |> getLValId) D div // If a dynamic element is pushed onto the stack, the stack is  dynamic
            | _ -> div

        (div', procs)

    | Pop (lval, stack) ->
        let div' =
            match (divExpr div (LVal lval), lookup (stack |> getLValId) div) with
            | (S, D) -> update (lval |> getLValId) D div // Popped elements from a dynamic stack are also dynamic
            | _ -> div

        (div', procs)

    | Write _ -> (div, procs)

    | BLocal (t, id, number) -> (div, procs)
    | BDelocal _ -> (div, procs)

and divBlock (ftab: SymTab<Proc>) (div: Division) (Block (_, _, stmts, _)) procs =
    let (div', procs') =
        ((div, procs), stmts)
        ||> List.fold (fun (d, p) stmt -> divStatement ftab d stmt p)

    (div', procs')

/// Computes the SD-division of a procedure given an initial division
and uniformDivProc ftab (intialParamsDiv: Division) (Proc (pid, pars, locals, blocks, delocals)) =

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

    // // Combining division with block-locals, which are also static.
    let initialDiv =
        (initialDivNoBlockLocals, getBlockLocals blocks)
        ||> List.fold (fun tab id -> bind id S tab)

    // Procedure calls that have been collected.
    let mutable procs_found: list<Identifier * Division> = []

    let mutable div = initialDiv
    let mutable div' = empty

    let mutable i = 1

    while div' <> div do
        //printfn $"procedure body {pid}: iteration {i}"
        i <- i + 1
        div' <- div

        let (div''', procs_found''') =
            ((div, []), blocks)
            ||> List.fold (fun (d, p) b -> divBlock ftab d b p)

        div <- div'''
        procs_found <- procs_found'''

    let unprocessedProcs: list<Identifier * Division> = List.distinct procs_found

    (div, unprocessedProcs)

and getBlockLocals blocks =

    let getLocalVarsInBlock (Block (label, _, stmts, _) as block) : Label * Identifier list * Identifier list =
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
    |> List.map (fun b -> getLocalVarsInBlock b)
    |> List.map
        (fun (label, lst1, lst2) ->
            let set1 = Set.ofList lst1
            let set2 = Set.ofList lst2

            if Set.count set1 <> List.length lst1 then
                error $"block-local names must be unique within a procedure"

            if Set.count set2 <> List.length lst2 then
                error $"block-delocal names must be unique within a procedure"

            if (not (Set.isSubset set1 set2))
               || (not (Set.isSubset set2 set1)) then
                error $"block-local and block-delocal in block {label} do not match"

            lst1)
    |> List.concat



/// Computes the uniform division of a program
let uniformDivision (initialDiv: SymTab<Binding>) (Program (decls, procs)) =

    let mainId = "main"

    // Resolve the main procedure
    let mainProc: Proc =
        match List.filter (fun (Proc (n, _, _, _, _)) -> n = mainId) procs with
        | [] -> error "no main procedure"
        | hd :: [] -> hd
        | _ -> error "more than one main procedure"

    // Construct the procedure table
    let ftab: SymTab<Proc> =
        procs
        |> List.fold (fun acc (Proc (n, a, loc, b, deloc)) -> (n, Proc(n, a, loc, b, deloc)) :: acc) []
        |> Map.ofList
        |> SymTab

    globalFTab <- ftab

    let mainInitialDiv: Division =
        (empty, mainProc |> getProcParams)
        ||> List.fold (fun acc (q, t, fid) -> bind fid (lookup fid initialDiv) acc)

    let rec loop seenBefore pending =
        match pending with
        | [] -> seenBefore
        | (currentProcId, currentInitialDiv) :: leftPending ->

            let hasNotBeenSeenBefore =
                seenBefore
                |> List.filter (fun (id, initDiv, _) -> id = currentProcId && initDiv = currentInitialDiv)
                |> List.isEmpty

            if hasNotBeenSeenBefore then
                let proc =
                    match tryLookup currentProcId globalFTab with
                    | None -> error $"{currentProcId} not found in ftab"
                    | Some p -> p

                let (finalDiv, newPendingProcs) =
                    uniformDivProc globalFTab currentInitialDiv proc

                let seenBefore' =
                    (currentProcId, currentInitialDiv, finalDiv)
                    :: seenBefore

                let pending' = newPendingProcs @ leftPending
                loop seenBefore' pending'
            else
                loop seenBefore leftPending

    let pendingProcs = [ (mainId, mainInitialDiv) ]
    let seenBeforeProcs = []

    let allProcs: list<Identifier * Division * Division> = loop seenBeforeProcs pendingProcs

    allProcs

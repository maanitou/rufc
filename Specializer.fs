module Specializer

open Ast
open SymTab
open Tools
open CodeGen
open Optimizer
open System.Collections.Generic

exception SpecializerError of string
let error str = raise (SpecializerError str)

[<AbstractClass; Sealed>]
type NumGen private () =
    static let mutable counter: uint = 0u

    static member Generate() =
        counter <- counter + 1u
        counter

    static member Reset() = counter <- 0u



type Division = SymTab<Binding>

type SDValue =
    | S of Value
    | D of Expr

type QSDValue = Qualifier * SDValue

let mutable globalFTab: SymTab<Proc> = empty

let mutable globalHashTable =
    new Dictionary<list<Identifier * QSDValue>, uint>()

type State = State of Label * SymTab<QSDValue>

let mutable pendingProcs = []

let updateProcName newPid (Proc (pid, pars, locals, stmts, delocals)) =
    (Proc(newPid, pars, locals, stmts, delocals))

let updateProcPars newPars (Proc (pid, pars, locals, stmts, delocals)) =
    (Proc(pid, newPars, locals, stmts, delocals))


/// Extend labels using the value of all static variables
let extendLabel (SymTab vtab: SymTab<QSDValue>) (label: Label) =

    let sortedTab =
        vtab
        |> Map.toList
        |> List.sortBy (fun (name, _) -> name)

    let varExt =
        sortedTab
        |> List.map
            (fun (name, qsdv) ->
                match qsdv with
                | (Const, S (IntVal (tag, n))) -> ""
                | (q, S (IntVal (tag, n))) -> $"{name}_{n}"
                | (q, S (ArrayVal _)) -> ""
                | (q, S (StackVal _)) -> ""
                | (q, D _) -> "")
        |> concatNotEmpty "_"

    [ label; varExt ] |> concatNotEmpty "_"


/// Extends the name of a procedure using the value of all static variables AND arrays.
let extendProcName (SymTab vtab) procName : Identifier =
    if procName = "main" then
        "main"
    else
        let sortedTab =
            vtab
            |> Map.toList
            |> List.sortBy (fun (name, _) -> name)

        let staticArrays: list<Identifier * QSDValue> =
            sortedTab
            |> List.filter
                (fun (id, (q, sdv)) ->
                    match sdv with
                    | S (ArrayVal _) -> true
                    | _ -> false)

        let arrExt =
            match staticArrays with
            | [] -> ""
            | _ ->
                let mutable arrayTag: uint = 0u

                if not (globalHashTable.TryGetValue(staticArrays, &arrayTag)) then
                    arrayTag <- NumGen.Generate()
                    globalHashTable.Add(staticArrays, arrayTag)

                $"{arrayTag}"

        let varExt =
            sortedTab
            |> List.map
                (fun (name, qsdv) ->
                    match qsdv with
                    | (q, S (IntVal (tag, n))) -> $"{name}_{n}"
                    | (q, S (ArrayVal _)) -> ""
                    | (q, S (StackVal _)) -> ""
                    | (q, D _) -> "")
            |> concatNotEmpty "_"

        [ procName; varExt; arrExt ] |> concatNotEmpty "_"

let getBinding (qsdVal: QSDValue) =
    match qsdVal with
    | (_, S _) -> Binding.S
    | (_, D _) -> Binding.D


/// Binds concrete arguments to formal parameters
let peBinder
    (callerVtab: SymTab<QSDValue>)
    (arguments: Identifier list)
    (Proc (pid, formalParams, locals, _, _) as proc)
    (divMapping: list<Identifier * Division * Division>)
    =

    // Concrete arguments with binding according to the caller division
    let args: list<Qualifier * SDValue * Identifier> =
        arguments
        |> List.map
            (fun id ->
                let (q, sdVal) = lookup id callerVtab
                (q, sdVal, id))

    // Division of the concrete arguments
    let concreteArgsDiv: (Identifier * Binding) list =
        args
        |> List.map (fun (q, sdVal, id) -> (id, (q, sdVal) |> getBinding))

    // Raw original binding of the formal parameters. The division of the formal parameters and local
    // variables of the callee depends on the division of the concrete arguments that were passed to
    // the procedure. In other terms, the division of variables in a procedure does depend of the context
    // in which the procedure was called.
    let pars': list<Binding * Qualifier * Type * Identifier> =
        (concreteArgsDiv, formalParams)
        ||> List.map2 (fun (cid, d) (q, t, fid) -> (d, q, t, fid))

    let key =
        (pid,
         pars'
         |> List.map (fun (b, q, t, id) -> (id, b))
         |> Map.ofList
         |> SymTab)

    let (SymTab parsDiv): SymTab<Binding> =
        divMapping
        |> List.find (fun (id, div1, div2) -> (id, div1) = key)
        |> fun (_, _, z) -> z

    //printfn $"Special binder for {pid}:\n{SymTab parsDiv |> ppTab}"

    // Formal parameters bound in accordance with the division mapping.
    let pars =
        formalParams
        |> List.map (fun (q, t, id) -> (lookup id (SymTab parsDiv), q, t, id))

    // Particular case when all parameters are static
    if parsDiv |> Map.forall (fun k v -> v = Binding.S) then
        printfn $"WARNING: all parameters of {pid} are static, it can be evaluated."

        let vtabDummy =
            (args, pars)
            ||> List.map2
                    (fun (q, sdv, id) (_, qf, tf, idf) ->
                        match sdv with
                        | S v -> (id, (qf, v))
                        | D _ -> (id, (qf, IntVal("", 0))))

        let (ftab', SymTab resVtab): SymTab<Proc> * SymTab<Qualifier * Value> =
            Interpreter.evalProc
                { Interpreter.State.Default() with
                      Ftab = globalFTab
                      Vtab = vtabDummy |> Map.ofList |> SymTab }
                arguments
                proc

        let xxx =
            args
            |> List.map
                (fun (qa, sdv, ida) ->
                    match (Map.find ida resVtab, sdv) with
                    | ((q, v), S _) -> ([], (ida, (q, S v))) //if caller variable is static, update it.
                    | ((q, IntVal v), D _) ->
                        let extraStmt = AssignOp(AssignAdd, Var ida, Constant v)
                        ([ extraStmt ], (ida, (q, sdv))) //id caller variable is dynamic, do not update it.
                    | (_, D _) ->
                        error
                            "not implemented: cannot pass non-integer dynamic arguments to static parameters.")

        let newStatements: Statement list = xxx |> List.unzip |> fst |> List.concat
        let vtabOut = xxx |> List.unzip |> snd
        //printfn $"WARNING: evaluation yields:\n {vtabOut |> SymTab.ofList |> ppTab}"
        //printfn $"WARNING: new statements: {newStatements}"
        (newStatements, vtabOut, [])

    else
        let magic arg par =
            match (arg, par) with
            | ((Const, _, _), (_, qf, _, _)) when qf <> Const ->
                error "const cannot be passed to non-const"
            | (_, (_, Local, _, _)) -> error "parameters cannot be qualified as Local"
            | (_, (_, BlockLocal, _, _)) -> error "parameters cannot be qualified as BlockLocal"

            // Binding static arguments to static parameters
            | ((qa, S (IntVal a0), a), (Binding.S, In, Int, x)) ->
                ([], (x, (In, IntVal a0 |> S)), (a, (qa, IntVal("", 0) |> S)))
            | ((qa, S (ArrayVal a0), a), (Binding.S, In, Array, x)) ->
                ([], (x, (In, ArrayVal a0 |> S)), (a, (qa, ArrayVal [||] |> S)))
            | ((qa, S (StackVal a0), a), (Binding.S, In, Stack, x)) ->
                ([], (x, (In, StackVal a0 |> S)), (a, (qa, StackVal List.empty |> S)))

            | ((_, S _, a), (Binding.S, In, _, x)) ->
                error $"type of arg {a} and param {x} mismatch"
            | ((qa, S a0, a), (Binding.S, Const, t, x)) ->
                ([], (x, (Const, S a0)), (a, (qa, a0 |> S)))
            | ((_, S _, a), (Binding.S, Out, t, x)) -> error "OUT param should not be static"
            | ((_, S _, a), (Binding.S, InOut, t, x)) -> error "INOUT param should not be static"

            // Binding static arguments to dynamic parameters
            | ((qa, S a0, a), (Binding.D, In, t, x)) ->
                ([ (Some a0, a, x) ], (x, (In, LVal(Var x) |> D)), (a, (qa, IntVal("", 0) |> S)))
            //error "not implemented: static variable passed to dynamic IN parameter"
            | ((_, S a0, a), (Binding.D, Const, t, x)) ->
                error "CONST param cannot go from static to dynamic"
            | ((_, S a0, a), (Binding.D, Out, t, x)) ->
                error "static arg should not be bound to dynamic OUT param"
            | ((_, S a0, a), (Binding.D, InOut, t, x)) ->
                error "static arg should not be bound to dynamic INOUT param"

            // Binding dynamic arguments to static parameters
            | ((_, D _, a), (Binding.S, In, t, x)) ->
                error "dynamic argument cannot be bound to static IN param"
            | ((_, D _, a), (Binding.S, Const, t, x)) ->
                error "CONST param cannot go from dynamic to static"
            | ((_, D _, a), (Binding.S, Out, t, x)) -> error "OUT param should not be static"
            | ((_, D _, a), (Binding.S, InOut, t, x)) -> error "INOUT param should not be static"

            // Binding dynamic arguments to dynamic parameters
            | ((qa, D (LVal (Var _)), a), (Binding.D, qx, t, x)) ->
                ([ (None, a, x) ], (x, (qx, LVal(Var x) |> D)), (a, (qa, LVal(Var a) |> D)))
            | ((_, D _, a), (Binding.D, _, t, x)) ->
                error "dynamic expr should be LVal(Var) when passed to a function"


        let (afMap', tabProcIn, vtabOut) =
            ([], args, pars)
            |||> List.fold2 (fun acc a p -> (magic a p) :: acc)
            |> List.unzip3

        let (extra, afMap) =
            afMap'
            |> List.concat
            |> List.map
                (fun (x, y, z) ->
                    match x with
                    | None -> ((y, x), (y, z))
                    | Some a0 ->
                        let tag = NumGen.Generate()
                        (($"{y}_{tag}", x), ($"{y}_{tag}", z)))
            |> List.rev
            |> List.unzip

        let vtabProcIn = tabProcIn |> SymTab.ofList

        let vtabProcInWithLocals =
            (vtabProcIn, locals)
            ||> List.fold
                    (fun acc (t, id, e) ->
                        match lookup id (SymTab parsDiv) with
                        | Binding.S ->
                            match e with
                            | Constant n -> bind id (Local, IntVal n |> S) acc
                            | LVal (Var name) ->
                                match tryLookup name vtabProcIn with
                                | Some (_, S (IntVal n)) -> bind id (Local, S(IntVal n)) acc
                                | Some _ -> error $"local {id} must be integer valued"
                                | None -> error $"variable {name} is not defined"
                            | _ -> error $"local {id} must be integer valued"
                        | Binding.D -> bind id (Local, LVal(Var id) |> D) acc)

        let pid' = extendProcName vtabProcInWithLocals pid
        let args' = afMap |> List.unzip |> fst

        let newCallStmt =
            ([ Call(pid', args') ], extra)
            ||> List.fold
                    (fun acc (a, optV) ->
                        match optV with
                        | None -> acc
                        | Some (IntVal a0) ->
                            [ BLocal(Int, a, a0) ]
                            @ acc @ [ BDelocal(Int, a, ("", 0)) ]
                        | Some _ ->
                            error "not implemented: passing static arrays to dynamic in parameters")

        let pars' =
            pars
            |> List.filter (fun (b, q, t, id) -> b = Binding.D)
            |> List.map (fun (_, q, t, id) -> (q, t, id))

        let newProcToPartiallyEvaluate =
            [ (pid', pars', proc, vtabProcInWithLocals, parsDiv |> SymTab) ]

        (newCallStmt, vtabOut, newProcToPartiallyEvaluate)


/// Specializes an expression.
let rec onpeExpr (vtab: SymTab<QSDValue>) expr : SDValue =
    match expr with
    | Constant (tag, number) -> S(IntVal(tag, number))
    | LVal (Var name) ->
        match tryLookup name vtab with
        | Some (tag, sdv) -> sdv
        | None -> error $"Var: variable {name} has not been defined yet"
    | LVal (Index (name, idxExpr)) ->

        let idxPe =
            match onpeExpr vtab idxExpr with
            | S idx ->
                match idx with
                | IntVal n -> n |> IntVal |> S
                | _ -> error "Index: index must be an integer value"
            | D idxPe -> D idxPe

        // If the index is static, the index expression can be partially evaluated
        match (lookup name vtab, idxPe) with
        | ((_, S (ArrayVal arr)), S (IntVal (_, i))) -> arr.[i] |> IntVal |> S
        | ((_, S (ArrayVal _)), S _) -> error "Index: index must be an integer value"
        | ((_, S (IntVal _)), _) -> error "Index: cannot index lookup a variable"
        | ((_, S (StackVal _)), _) -> error "Index: cannot index lookup a stack"

        | ((_, D _), S idx) ->
            match idx with
            | IntVal n -> Index(name, Constant n) |> LVal |> D
            | _ -> error "Index: index must be an integer value"

        | (_, D e') -> Index(name, e') |> LVal |> D

    | BinOp (op, e1, e2) ->
        match (onpeExpr vtab e1, onpeExpr vtab e2) with
        | (S (IntVal (_, n1)), S (IntVal (_, n2))) ->
            applyBinOp op n1 n2 |> fun v -> IntVal("", v) |> S
        | (D e, S (IntVal (tag, n))) ->
            match op with
            | And when n = 0 -> IntVal("", 0) |> S
            | Or when n <> 0 -> IntVal("", 1) |> S
            | _ -> (op, e, Constant((tag, n))) |> BinOp |> D
        | (S (IntVal (tag, n)), D e) ->
            match op with
            | And when n = 0 -> IntVal("", 0) |> S
            | Or when n <> 0 -> IntVal("", 1) |> S
            | _ -> (op, e, Constant((tag, n))) |> BinOp |> D
        | (D e1', D e2') -> BinOp(op, e1', e2') |> D
        | _ -> error "BinOp: can only apply binary operator to integer values"

    | Not e -> onpeExpr vtab e

    | Empty lval -> Empty lval |> D
    | Top lval -> Top lval |> D


/// Specializes a statement.
let rec onpeStmt (ftab: SymTab<Proc>) (vtab: SymTab<QSDValue>) (currentDiv: Division) divMapping =
    function
    | AssignOp (op, lval, e) -> assign vtab op lval e |> fun (x, y) -> (x, y, [])
    | Skip -> (vtab, [ Skip ], [])
    | Swap (lval1, lval2) ->
        match (onpeExpr vtab (LVal lval1), onpeExpr vtab (LVal lval2)) with
        | (S _, S _) ->
            // TODO: Swap for array elements.
            match (lookup (lval1 |> getLValId) vtab, lookup (lval2 |> getLValId) vtab) with
            | ((q1, sdv1), (q2, sdv2)) ->
                let vtab' =
                    update (lval1 |> getLValId) (q1, sdv2) vtab

                let vtab'' =
                    update (lval2 |> getLValId) (q2, sdv1) vtab'

                (vtab'', [], [])
        // If either one of them is dynamic then both become dynamic
        | _ -> (vtab, [ Swap(lval1, lval2) ], [])

    | Call (pid, args) ->
        let (vtabInProc, vtabCallerRest) = SymTab.split vtab args

        let (newStatements, vtabOutProc, newProcToPartiallyEvaluate) =
            match tryLookup pid ftab with
            | None -> error $"Call: proc {pid} is not defined in ftab"
            | Some p -> peBinder vtabInProc args p divMapping

        let vtabOutCaller =
            SymTab.merge vtabCallerRest (vtabOutProc |> SymTab.ofList)

        (vtabOutCaller, newStatements, newProcToPartiallyEvaluate)


    | Uncall (procName, args) ->

        match tryLookup procName ftab with
        | None -> error $"Call: proc {procName} is not defined in ftab"
        | Some proc ->
            let procNameInv = invertProcName procName

            match tryLookup procNameInv globalFTab with
            | None -> // The inversed procedure has not been added to ftab yet
                let local = true
                let procInv = Inverter.invertProc local proc

                globalFTab <- bind procInv.Name procInv ftab
                onpeStmt globalFTab vtab currentDiv divMapping (Call(procNameInv, args))

            | Some _ -> onpeStmt globalFTab vtab currentDiv divMapping (Call(procNameInv, args))



    | Push (lval, stack) -> (vtab, [ Push(lval, stack) ], [])
    | Pop (lval, stack) -> (vtab, [ Pop(lval, stack) ], [])

    | Write str -> (vtab, [ Write str ], [])
    | BLocal (t, id, n) ->
        match lookup id currentDiv with
        | Binding.D -> (bind id (BlockLocal, Var id |> LVal |> D) vtab, [ BLocal(t, id, n) ], [])
        | Binding.S -> (bind id (BlockLocal, IntVal n |> S) vtab, [], [])

    | BDelocal (t, id, n) ->
        match lookup id currentDiv with
        | Binding.D -> (unbind id vtab, [ BDelocal(t, id, n) ], [])
        | Binding.S ->
            // TODO: check the correct value
            (unbind id vtab, [], [])

and assign vtab op lval rhsExpr : SymTab<QSDValue> * Statement list =
    match lval with
    | Var name -> assignVar vtab op name rhsExpr
    | Index (name, idx) -> assignIndex vtab op name idx rhsExpr

and assignVar vtab op name (e: Expr) : SymTab<QSDValue> * Statement list =
    match (lookup name vtab, onpeExpr vtab e) with
    | ((q1, S (IntVal (_, n1))), S (IntVal (_, n2))) ->
        match q1 with
        | Const -> error $"cannot assign a new value to the CONST variable {name}"
        | _ ->
            let v = S(IntVal("", applyAssignOp op n1 n2))
            (update name (q1, v) vtab, [])
    // For dynamic assigments, we defer CONST checking to the interpreter
    | ((q1, D _), S (IntVal n)) -> (vtab, [ AssignOp(op, Var name, Constant n) ])
    | ((q1, S _), D e2) ->
        (update name (q1, LVal(Var name) |> D) vtab, [ AssignOp(op, Var name, e2) ])
    | ((_, D _), D e2) -> (vtab, [ AssignOp(op, Var name, e2) ])
    | _ -> error "AssigVar: lhs and rhs must be integer values"

and assignIndex (vtab: SymTab<QSDValue>) op arrId idxExpr rhsExpr =
    match onpeExpr vtab rhsExpr with

    | S (IntVal (tag2, v2)) ->
        // rhs is static
        match (lookup arrId vtab, onpeExpr vtab idxExpr) with
        | ((Const, _), _) ->
            // array is const, so error
            error $"Cannot assign element in CONST array {arrId}"
        | ((q, S (ArrayVal arr)), S (IntVal (_, idx))) ->
            // array, index, and rhs are all static
            let (tag, v1) = arr.[idx]
            // NOTE: should create an applyAssignOp function that takes tagged values instead
            Array.set arr idx (applyAssignOp op v1 v2 |> fun v -> ("", v))
            let vtab' = update arrId (q, S(ArrayVal arr)) vtab
            (vtab', [])
        | ((q, S (ArrayVal arr)), D _) ->
            // index is dynamic, so array must be made dynamic
            let vtab' =
                update arrId (q, D(LVal(Var arrId))) vtab
            // rhs in residual statement is partially evaluated
            (vtab', [ AssignOp(op, Index(arrId, idxExpr), Constant(tag2, v2)) ])
        | ((q, D _), S (IntVal idx)) ->
            // index is static in dynamic array, so we partially evaluate the index
            // and the rhs in a new residual assignment.
            (vtab, [ AssignOp(op, Index(arrId, Constant idx), Constant(tag2, v2)) ])
        | ((q, D _), D _) -> (vtab, [ AssignOp(op, Index(arrId, idxExpr), rhsExpr) ])

    | D _ ->
        // rhs is dynamic
        match (lookup arrId vtab, onpeExpr vtab idxExpr) with
        | ((Const, _), _) ->
            // array is const, so error. Could defer to interpreter.
            error $"Cannot assign element in CONST array {arrId}"
        | ((q, S (ArrayVal arr)), S (IntVal idx)) ->
            let vtab' =
                update arrId (q, D(LVal(Var arrId))) vtab

            (vtab', [ AssignOp(op, Index(arrId, Constant idx), rhsExpr) ])
        | ((q, D _), S (IntVal idx)) ->
            (vtab, [ AssignOp(op, Index(arrId, Constant idx), rhsExpr) ])
        | ((q, S (ArrayVal arr)), D _) ->
            let vtab' =
                update arrId (q, D(LVal(Var arrId))) vtab

            (vtab', [ AssignOp(op, Index(arrId, idxExpr), rhsExpr) ])
        | ((q, D _), D _) -> (vtab, [ AssignOp(op, Index(arrId, idxExpr), rhsExpr) ])



/// Partial evaluation of a block.
and onpeBlock
    (links: SymTab<Label list>)
    ftab
    vtab
    currentDiv
    divMapping
    (Block (label, arr, stmts, dep))
    =

    let labelExt: Label = extendLabel vtab label

    let pePreArrivalCode = onpePreArrival vtab arr

    // Computes the partially evaluated block statements, and the resulting vtab.
    let (vtab', peStmtsCode) =
        ((vtab, []), stmts)
        ||> List.fold
                (fun (tab, pec) s ->
                    let (tab', pec', newProc) =
                        onpeStmt ftab tab currentDiv divMapping s

                    pendingProcs <- newProc @ pendingProcs
                    (tab', pec @ pec'))

    let (destLabels: Label list, peDepartureCode) = onpeDeparture vtab' dep

    let newStates: State list =
        List.map (fun l -> State(l, vtab')) destLabels

    // Add the newly created links to the link-list. Again, the links could
    // be extended with the specialized procedure name when returning from
    // the present block pe.
    let links' =
        bind labelExt (destLabels |> List.map (extendLabel vtab')) links

    // Specialization of the Arrival is deferred to the post-processing phase
    // using the link list.
    (links', newStates, Block(labelExt, pePreArrivalCode, peStmtsCode, peDepartureCode))

/// Returns the partially evaluated Destination statement and the list of destination labels.
and onpeDeparture (vtab: SymTab<QSDValue>) =
    // Note: There does not seem to be any valid reason to not extend the destination labels here
    // rather than postponing the label extension to when we construct the link. The code
    // here would be simplified.
    function
    | Exit -> ([ "EXIT" ], Exit)
    | Goto lab -> ([ lab ], Goto(lab |> extendLabel vtab))
    | IfGoto (e, lab) ->
        match (onpeExpr vtab e) with
        | S (IntVal (tag, 0)) -> error "IfGoto: static condition must be true"
        | S (IntVal _) -> ([ lab ], Goto(lab |> extendLabel vtab))
        | S _ -> error "IfGoto: static condition must be an integer value"
        | D e' -> ([ lab ], IfGoto(e', lab |> extendLabel vtab))

    | IfGotoElse (e, labT, labF) ->
        match (onpeExpr vtab e) with
        | S (IntVal (tag, 0)) -> ([ labF ], Goto(labF |> extendLabel vtab))
        | S (IntVal _) -> ([ labT ], Goto(labT |> extendLabel vtab))
        | S _ -> error "IfGotoElse: static condition must be an integer value"
        | D e' ->
            let extLabT = extendLabel vtab labT
            let extLabF = extendLabel vtab labF
            ([ labT; labF ], IfGotoElse(e', extLabT, extLabF))

/// Returns the pre-processed partial evaluation of the Arrival statment.
and onpePreArrival (vtab: SymTab<QSDValue>) (arr: Arrival) : Arrival =
    let suffix = ""

    match arr with
    | Entry -> Entry
    | From lab -> From(lab + suffix)
    | FiFrom (e, lab) ->
        match (onpeExpr vtab e) with
        | S (IntVal (tag, 0)) -> error "FiFrom: static condition must be true"
        | S (IntVal _) -> From(lab + suffix)
        | S _ -> error "FiFrom: static condition must be an integer value"
        | D e' -> FiFrom(e', lab + suffix)

    | FiFromElse (e, labT, labF) ->
        match (onpeExpr vtab e) with
        | S (IntVal (_, 0)) -> From(labF + suffix)
        | S (IntVal _) -> From(labT + suffix)
        | S _ -> error "FiFromElse: static condition must be an integer value"
        | D e' ->
            let extLabT = labT + suffix
            let extLabF = labF + suffix
            FiFromElse(e', extLabT, extLabF)


/// Returns the partially evaluated arrival statement using the link-list constructed in the
/// pre-processing phase.
and onpePostArrival (SymTab links: SymTab<Label list>) (Block (blockLabel, arr, _, _)) =

    /// Find the parent block labels of a given block by using the link-list.
    let parents =
        links
        |> Map.toList
        |> List.filter (fun (_, valueLst) -> List.contains blockLabel valueLst)
        |> List.map (fun (k, _) -> k)

    match arr with
    | Entry -> Entry

    | From lab ->
        match parents with
        | [ plab ] when plab.StartsWith lab -> From plab
        | otherwise ->
            error
                $"In block {blockLabel}, From: Could not find parent corresponding to {lab}, but found {otherwise}"

    | FiFrom (e, lab) ->
        match parents with
        | [ plab ] when plab.StartsWith lab -> FiFrom(e, plab)
        | _ -> error $"In block {blockLabel}, FiFrom: Could not find parent corresponding to {lab}"

    | FiFromElse (e, labT, labF) ->
        match parents with
        | plab1 :: [ plab2 ] ->
            if plab1.StartsWith labT && plab2.StartsWith labF then
                FiFromElse(e, plab1, plab2)
            else if plab1.StartsWith labF && plab2.StartsWith labT then
                FiFromElse(e, plab2, plab1)
            else
                error (
                    $"In block {blockLabel},"
                    + $"FiFromElse: could not find parents corresponding to {labT} and {labF}"
                )
        | [ plab ] ->
            if plab.StartsWith labT then
                FiFrom(e, plab)
            else if plab.StartsWith labF then
                FiFrom(Not e, plab)
            else
                error $"In block {blockLabel}, FiFromElse: single parent, but it was not found"

        | otherwise ->
            error (
                $"In block {blockLabel}, "
                + $"FiFromElse: Expected one or two parents for {blockLabel}, but found {otherwise}"
            )

and finishBlock links (Block (label, arr, stmts, dep)) =
    let arr' =
        onpePostArrival links (Block(label, arr, stmts, dep))

    Block(label, arr', stmts, dep)




///  Returns a partially evaluated procedure
and onpeProc
    ftab
    vtabProcIn
    currentDiv
    divMapping
    (Proc (pid, formalParams, locals, blocks, delocals) as proc)
    =

    let isStatic =
        function
        | S _ -> true
        | D _ -> false

    let isZeroed =
        function
        | S (IntVal (_, 0)) -> true
        | S (ArrayVal [||]) -> true
        | S (StackVal []) -> true
        | _ -> false

    let areAllInParametersZero (SymTab tab: SymTab<QSDValue>) : bool =
        tab
        |> Map.exists (fun _ (q, sdv) -> q = In && isStatic sdv && not (isZeroed sdv))
        |> not

    let isAnExitBlock (Block (_, _, _, dep)) =
        match dep with
        | Exit -> true
        | _ -> false

    let (entryLabel: Label, blockMap: SymTab<Block>) = createBlockMap blocks

    /// Returns true if the current state corresponds to a return statement.
    let isExiting (State (label, _)) = label.StartsWith "EXIT"

    let residualLocals: Local list =
        List.collect
            (fun (t, id, e) ->
                match (onpeExpr vtabProcIn e, lookup id vtabProcIn) with
                | (S (IntVal (_, n)), (Local, S (IntVal (_, n')))) when n = n' -> []
                | (S (IntVal (_, n)), (Local, S (IntVal (_, n')))) ->
                    error $"local {id} expected to be {n} but was {n'}"
                | (_, (Local, S _)) -> error "local {id} must be an integer value"
                | (D _, (Local, D _)) -> [ (t, id, e) ]
                | (S (IntVal n), (Local, D _)) -> [ (t, id, Constant n) ]
                | _ -> error $"local {id}: something is wrong with the local declaration")
            locals

    let rec loop
        links
        (seenBefore: State list)
        (pending: State list)
        (residual: Block list)
        exitTab
        =
        match pending with
        | [] -> (links, residual, exitTab)
        | (State (label, tab)) as currentState :: leftPending ->
            if not (List.contains currentState seenBefore) then
                // The current state has not been seen before
                if isExiting currentState then
                    // We have just processed the Exit block, continue with the
                    // remaining pending blocks in this procedure.
                    loop links (currentState :: seenBefore) leftPending residual tab
                else

                    match tryLookup label blockMap with
                    | Some b ->
                        // If this is an EXIT block, check that all static IN parameters are 0, otherwise back off!
                        if
                            isAnExitBlock b
                            && not (areAllInParametersZero tab)
                        then
                            printfn
                                $"WARNING: Specializer in proc {pid} tries to create an exit block with non-zero IN param"

                            loop links (currentState :: seenBefore) leftPending residual tab
                        else
                            let (links', newStates: State list, newPeBlock: Block) =
                                onpeBlock links ftab tab currentDiv divMapping b

                            loop
                                links'
                                (currentState :: seenBefore)
                                (newStates @ leftPending)
                                (newPeBlock :: residual)
                                tab


                    | None -> error $"jumping to non-existing label `{label}`"
            else
                // If the current state has been seen before, proceed to the next pending block
                loop links seenBefore leftPending residual tab


    let initialLinks: SymTab<Label list> = empty
    let initialSeenBefore = []
    let initialPending = [ State(entryLabel, vtabProcIn) ]
    let residualCode = []

    let (SymTab links, residualBlocks, SymTab exitTab) =
        loop initialLinks initialSeenBefore initialPending residualCode empty

    let residualDelocals: Delocal list =
        List.collect
            (fun (t, id, e) ->
                match (onpeExpr (SymTab exitTab) e, tryLookup id (SymTab exitTab)) with
                | (_, None) -> error $"{id} is not found in vtab {exitTab}"
                | (S (IntVal (_, n)), Some (Local, S (IntVal (_, n')))) when n = n' -> []
                | (S (IntVal (_, n)), Some (Local, S (IntVal _))) ->
                    error "local {id} expected to be {n} but was {n'}"
                | (_, Some (Local, S _)) ->
                    error "local {id} is not expected to be an integer value"
                | (D _, Some (Local, D _)) -> [ (t, id, e) ]
                | (S (IntVal n), Some (Local, D _)) -> [ (t, id, Constant n) ]
                | _ -> error $"delocal {id}: something is wrong with the local declaration")
            delocals

    // printfn $"LINKS for {pid}:\n"

    // [ for link in links do
    //       printfn $"{link}" ]
    // |> ignore

    let preProcessedProc =
        Proc(pid, formalParams, residualLocals, residualBlocks |> List.rev, residualDelocals)

    // Post-processing all block arrivals using the link table
    let postProcessedProc =
        postProcessArrivals (SymTab links) preProcessedProc

    //printfn $"{postProcessedProc}"

    let remainingBlocks =
        filterOutDeadBlocks (getBlocks postProcessedProc)

    let prunedProc =
        postProcessedProc |> setBlocks remainingBlocks

    let compressedProc = compressTransitions links prunedProc

    // printfn $"COMPRESSED LINKS for {pid}:\n{compressedLinks |> ppTab}"

    //Un-bind locals from var table
    let vtabOut =
        Map.filter (fun id (k, v) -> k <> Local) exitTab

    let orderedBlocks = reorderBlocks (getBlocks compressedProc)

    let finalProc =
        compressedProc |> setBlocks orderedBlocks

    (finalProc, vtabOut)

and removeFormalParameters parNames =
    function
    | Proc (pid, pars, locals, blocks, delocals) ->
        let pars' =
            pars
            |> List.filter (fun (q, t, n) -> not (List.contains n parNames))

        Proc(pid, pars', locals, blocks, delocals)


/// Post processing of all block arrivals
and postProcessArrivals (links: SymTab<Label list>) (Proc (pid, pars, locals, blocks, delocals)) =
    let blocks' = List.map (finishBlock links) blocks
    Proc(pid, pars, locals, blocks', delocals)

/// Creates a mapping of labels to blocks, and returns the entry point
/// NOTE: This is basically copied code from the Interpreter
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


/// Partially evaluates a program
let onpeProgram (args: (Identifier * SDValue) list) (Program (defs, procs) as prog) =

    let mainProc =
        match resolveMainProc prog with
        | (None, message) -> error message
        | (Some p, _) -> p

    // Construct the vtab which is passed to the main procedure.
    let vtab: SymTab<QSDValue> =
        List.map (fun (argName, argValue) -> (argName, (Local, argValue))) args
        |> SymTab.ofList

    // Construct the proc table which is passed to the main procedure.
    let ftab: SymTab<Proc> =
        procs
        |> List.fold (fun acc p -> (p.Name, p) :: acc) []
        |> SymTab.ofList

    globalFTab <- ftab

    // We assume that the argument names are identical to the parameter names
    // of the main procedure
    let argNames =
        (mainProc.Params |> List.map (fun (q, t, n) -> n))

    let initialDiv =
        args
        |> List.map
            (fun (id, sdVal) ->
                match sdVal with
                | S _ -> (id, Binding.S)
                | D _ -> (id, Binding.D))
        |> SymTab.ofList

    let divMapping =
        Divisor.uniformDivision initialDiv prog
        |> Map.toList
        |> List.map
            (fun ((x, y), z) ->
                match z with
                | Some z' -> (x, y, z')
                | None -> error "Division incomplete.")


    //printfn $"\ndivMapping:"

    // [ for (id, d0, d) in divMapping do
    //       yield $"{id}({d0 |> ppDiv}): {d |> ppDiv}" ]
    // |> String.concat "\n"
    // |> printfn "%s"

    // Get the unique division for main
    let mainDiv: Division =
        divMapping
        |> List.pick (fun (pid, d0, d) -> if pid = "main" then Some d else None)

    pendingProcs <- []

    let (vtabOut, newStatement, pending) =
        onpeStmt ftab vtab mainDiv divMapping (Call("main", argNames))

    pendingProcs <- pending
    //printfn $"ONPE_PROGRAM, PENDING PROCS: {pendingProcs}"

    let mutable processedProcs = []
    let mutable seenBeforeProcs = []

    while not (pendingProcs.IsEmpty) do
        let (current, rest) =
            pendingProcs
            |> (fun lst -> (List.head lst, List.tail lst))

        pendingProcs <- rest

        if not (List.contains current seenBeforeProcs) then
            seenBeforeProcs <- current :: seenBeforeProcs

            let (pendingId, pendingPars, pendingProc, pendingVtabProcIn, pendingProcUniformDiv) =
                current
            //printfn $"PENDING:\n{pendingId} {(pendingVtabIn)}"

            let (processedProc, vtabOut) =
                onpeProc ftab pendingVtabProcIn pendingProcUniformDiv divMapping pendingProc

            let peCurrent =
                processedProc
                |> updateProcName pendingId
                |> updateProcPars pendingPars

            processedProcs <- peCurrent :: processedProcs


    Program(defs, processedProcs |> List.rev)

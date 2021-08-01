module Inverter

open Ast

let invertOp =
    function
    | AssignAdd -> AssignSub
    | AssignSub -> AssignAdd
    | AssignXor -> AssignXor

let invertQualifier =
    function
    | In -> Out
    | Out -> In
    | q -> q

let rec invertStatements (local: bool) (statements: Statement list) =

    List.map (invertStmt local) statements |> List.rev

and invertStmt (local: bool) =
    function
    | AssignOp (op, id, e) -> AssignOp(invertOp op, id, e)
    | Push (id, stack) -> Pop(id, stack)
    | Pop (id, stack) -> Push(id, stack)
    | Swap (id1, id2) -> Swap(id1, id2)
    | Skip -> Skip
    | Write str -> Write str

    | Call (id, concreteArgs) ->
        if local then
            // A Call has been met during uncalling a procedure
            Uncall(id, concreteArgs)
        else
            // A Call has been met during inverting a program.
            // Uncall proc = Call inv(Proc)
            Call(invertProcName id, concreteArgs)

    | Uncall (id, concreteArgs) ->
        if local then
            // An Uncall has been met during uncalling a procedure
            Call(id, concreteArgs)
        else
            // An Uncall has been met during inverting a program.
            // Call proc = Uncall inv(Proc)
            Uncall(invertProcName id, concreteArgs)

    | BLocal (t, id, number) -> BDelocal (t, id, number)
    | BDelocal (t, id, number) -> BLocal (t, id, number)

let invertArrival =
    function
    | Entry -> Exit
    | From lab -> Goto lab
    | FiFrom (e, lab) -> IfGoto(e, lab)
    | FiFromElse (e, labT, labF) -> IfGotoElse(e, labT, labF)

let invertDeparture =
    function
    | Exit -> Entry
    | Goto lab -> From lab
    | IfGoto (e, lab) -> FiFrom(e, lab)
    | IfGotoElse (e, labT, labF) -> FiFromElse(e, labT, labF)

let invertBlock (local: bool) =
    function
    | Block (label, arr, statmts, depart) ->
        Block(label, invertDeparture depart, invertStatements local statmts, invertArrival arr)


let invertParam (q, id, value) = (invertQualifier q, id, value)

let invertProc (local: bool) (Proc (procName, pars, locals, blocks, delocals)) =
    let procNameInv =
        if procName = "main" then
            "main"
        else
            invertProcName procName

    let localsInv = delocals
    let delocalsInv = locals
    let blocksInv = List.map (invertBlock local) blocks

    let parsInv = List.map invertParam pars

    Proc(procNameInv, parsInv, localsInv, blocksInv, delocalsInv)

let invertProgram (Program (defs, procs)) =
    let local = false // We are inverting a program, not uncalling a proc.
    (defs, List.map (invertProc local) procs) |> Program

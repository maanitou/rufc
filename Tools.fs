module Tools

open Ast

let bool2int =
    function
    | true -> 1
    | false -> 0

let int2bool =
    function
    | 0 -> false
    | _ -> true

let applyAssignOp (op: AssignOp) (v1: int32) (v2: int32) : int =
    match op with
    | AssignAdd -> (+) v1 v2
    | AssignSub -> (-) v1 v2
    | AssignXor -> (^^^) v1 v2

let applyBinOp (op: BinOp) (v1: int32) (v2: int32) : int =
    match op with
    | And -> bool2int (int2bool v1 && int2bool v2)
    | Or -> bool2int (int2bool v1 || int2bool v2)
    | Eq -> v1 = v2 |> bool2int
    | Lt -> v1 < v2 |> bool2int
    | Gt -> v1 > v2 |> bool2int
    | Leq -> v1 <= v2 |> bool2int
    | Geq -> v1 >= v2 |> bool2int
    | Neq -> v1 <> v2 |> bool2int

    | Add -> (+) v1 v2
    | Sub -> (-) v1 v2
    | Mul -> (*) v1 v2
    | Div -> (/) v1 v2
    | Mod -> if v1 < 0 then v1 % v2 + v2 else v1 % v2
    | Frac -> (int64) v2 * (int64) v1 >>> 32 |> int32

let getProcName =
    function
    | Proc (id, _, _, _, _) -> id

let getProcParams (Proc (_, pars, _, _, _)) = pars

let getBlockLabel (Block (label, _, _, _)) = label

let getBlocks (Proc (_, _, _, blocks, _)) = blocks
let setBlocks blocks (Proc (w, x, y, _, z)) = Proc(w, x, y, blocks, z)

let setDeparture dep (Block (lab, arr, stmts, _)) = Block(lab, arr, stmts, dep)

let getLValId =
    function
    | Var id -> id
    | Index (id, _) -> id

/// Resolve the main procedure
let resolveMainProc (Program (decls, procs)) : Proc option * string =
    match List.filter (fun (Proc (n, _, _, _, _)) -> n = "main") procs with
    | [] -> (None, "no main procedure")
    | hd :: [] -> (Some hd, "ok")
    | _ -> (None, "more than one main procedure")


/// Return a new string by concatenating strings with separator sep, after having filtered
/// out all empty strings.
let concatNotEmpty (sep: string) (strings: string list) =
    strings
    |> List.filter (fun str -> str <> "")
    |> String.concat sep

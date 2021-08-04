module CodeGen

open Ast
open SymTab
open Tools

let createTab ntab = (String.replicate ntab "  ")

let ppType =
    function
    | Int -> "int"
    | Array -> "array"
    | Stack -> "stack"

let ppQualififier =
    function
    | In -> "in"
    | Out -> "out"
    | InOut -> "inout"
    | Const -> "const"
    | Local -> "local"
    | BlockLocal -> "blocal"

let ppNumber number =
    match number with
    | (tag, n) when tag = "" -> string n
    | (tag, n) -> tag

let rec ppExpr (expr: Expr) =
    match expr with
    | Constant number -> number |> ppNumber
    | LVal id -> ppLval id
    | BinOp (op, e1, e2) -> $"{ppExpr e1} {op |> symb} {ppExpr e2}"
    | Not e -> $"not ({ppExpr e})"
    | Empty lval -> $"empty {ppLval lval}"
    | Top lval -> $"empty {ppLval lval}"

and ppLval (lval: LVal) =
    match lval with
    | Var name -> $"{name}"
    | Index (name, e) -> $"{name}[{ppExpr e}]"

let rec ppStats ntab stats =
    let lst = List.map (ppStat ntab) stats
    lst |> String.concat ";\n"

and ppStat ntab statm =
    let tab = String.replicate ntab "  "

    match statm with
    | AssignOp (op, lval, e) -> $"{tab}{ppLval lval} {op |> assignmentSymb} {ppExpr e}"
    | Swap (lval1, lval2) -> $"{tab}{ppLval lval1} <=> {ppLval lval2}"
    | Call (pid, args) ->
        let argsStr = args |> String.concat ", "
        $"{tab}call {pid}({argsStr})"
    | Uncall (pid, args) ->
        let argsStr = args |> String.concat ", "
        $"{tab}uncall {pid}({argsStr})"
    | Push (lval1, lval2) -> $"{tab}push {ppLval lval1} {ppLval lval2}"
    | Pop (lval1, lval2) -> $"{tab}pop {ppLval lval1} {ppLval lval2}"
    | Skip -> $"{tab}skip"
    | Write str -> $"{tab}write {str}"
    | BLocal (t, id, n) -> $"{tab}blocal {t |> ppType} {id}={n |> ppNumber}"
    | BDelocal (t, id, n) -> $"{tab}bdelocal {t |> ppType} {id}={n |> ppNumber}"

let rec ppBlock ntab block =
    let tab = createTab ntab

    match block with
    | Block (lab, arr, stmts, dep) ->
        [ $"{tab}{lab}:"
          $"{tab}{tab}{ppArrival arr}"
          $"{ppStats (ntab + 1) stmts}"
          $"{tab}{tab}{ppDeparture dep}" ]
        |> concatNotEmpty "\n"

and ppArrival arr =
    match arr with
    | Entry -> $"entry"
    | From lab -> $"from {lab}"
    | FiFrom (e, lab) -> $"fi {ppExpr e} from {lab}"
    | FiFromElse (e, labT, labF) -> $"fi {ppExpr e} from {labT} else {labF}"

and ppDeparture dep =
    match dep with
    | Exit -> $"exit"
    | Goto lab -> $"goto {lab}"
    | IfGoto (e, lab) -> $"if {ppExpr e} goto {lab}"
    | IfGotoElse (e, labT, labF) -> $"if {ppExpr e} goto {labT} else {labF}"


let ppParam ((q, t, id): Param) =
    $"{q |> ppQualififier} {t |> ppType} {id}"

let ppLocal ((t, id, e): Local) = $"{t |> ppType} {id}={e |> ppExpr}"

let ppProc ntab (Proc (pid, pars, locals, blocks, delocals)) =
    let tab = createTab ntab

    let parsStr =
        pars |> List.map ppParam |> String.concat ", "

    let localStr =
        match locals with
        | [] -> ""
        | _ ->
            "local "
            + (locals |> List.map ppLocal |> String.concat ", ")

    let blocksStr =
        blocks
        |> List.map (ppBlock ntab)
        |> concatNotEmpty "\n\n"

    let delocalStr =
        match delocals with
        | [] -> ""
        | _ ->
            "delocal "
            + (delocals |> List.map ppLocal |> String.concat ", ")

    [ $"proc {pid}({parsStr})"
      $"{tab}{localStr}"
      $"{blocksStr}"
      $"{tab}{delocalStr}" ]
    |> concatNotEmpty "\n"


let ppDef ((id, v): ConstDecl) = $"define  {id}  {v}"

let ppProgram (Program (defs, procs)) =
    let defsString =
        (List.map ppDef defs |> String.concat "\n")

    let procsString =
        (List.map (ppProc 1) procs |> String.concat "\n\n")

    [ defsString; procsString ]
    |> concatNotEmpty "\n\n\n"


let ppVtab (SymTab vtab: SymTab<Qualifier * Value>) =

    let number2str =
        function
        | ("", v) -> v |> string
        | (tag, _) -> tag

    ("", Map.toList vtab)
    ||> List.fold
            (fun acc (k, v) ->
                let valueStr =
                    match v with
                    | (_, IntVal v) -> $"{v |> number2str}"
                    | (_, ArrayVal arr) -> (String.concat " " (Seq.map number2str arr))
                    | (_, StackVal lst) ->
                        "stack "
                        + (String.concat " " (Seq.map number2str lst))

                $"{k}: " + valueStr + "\n;\n" + acc)



let ppMap map =
    [ for entry in map |> Map.toList do
          yield $"{entry}" ]
    |> String.concat "\n"


let ppTab (SymTab tab) = ppMap tab

let ppList lst =
    [ for entry in lst do
          yield $"{entry}" ]
    |> String.concat "\n"

module Ast

type Binding =
  | S   // static binding
  | D   // dynamic binding

type BinOp =
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | Frac
    | And
    | Or
    | Lt
    | Gt
    | Leq
    | Geq
    | Eq
    | Neq

type AssignOp =
    | AssignAdd
    | AssignSub
    | AssignXor

type Type =
    | Int
    | Array
    | Stack

type Qualifier =
    | BlockLocal
    | Local
    | Const
    | InOut
    | In
    | Out

type Tag = string

type Number = Tag * int32

type Value =
    | IntVal of Number
    | ArrayVal of Number []
    | StackVal of Number list

type Identifier = string

type Expr =
    | Constant of Number
    | LVal of LVal
    | BinOp of BinOp * Expr * Expr
    | Not of Expr
    | Top of LVal
    | Empty of LVal

and LVal =
    | Var of Identifier
    | Index of Identifier * Expr

and Statement =
    | AssignOp of AssignOp * LVal * Expr
    | Pop of LVal * LVal
    | Push of LVal * LVal
    | Skip
    | Swap of LVal * LVal
    | Call of Identifier * Identifier list
    | Uncall of Identifier * Identifier list
    | Write of string
    | BLocal of Type * Identifier * Number
    | BDelocal of Type * Identifier * Number

type Label = string

type Arrival =
    | From of Label
    | FiFromElse of Expr * Label * Label
    | FiFrom of Expr * Label
    | Entry

type Departure =
    | Goto of Label
    | IfGotoElse of Expr * Label * Label
    | IfGoto of Expr * Label
    | Exit

type Block = Block of Label * Arrival * Statement list * Departure

type Arg = Qualifier * Value * Identifier
type Param = Qualifier * Type * Identifier

type Local = Type * Identifier * Expr
type Delocal = Type * Identifier * Expr

type Body = Local list * Block list * Delocal list

type Proc = Proc of Identifier * Param list * Local list * Block list * Delocal list

type ConstDecl = Identifier * int32

type Program = Program of ConstDecl list * Proc list

type Operator =
    | AssignmentOperator
    | BinaryOperator

type AssignmentOperator = { Symb: string; Op: AssignOp }

let assignmentOperators =
    [ { Symb = "+="; Op = AssignAdd }; { Symb = "-="; Op = AssignSub }; { Symb = "^="; Op = AssignXor } ]

type BinaryOperator = { Symb: string; Prec: int; Op: BinOp }

let binaryOperators =
    [ { Symb = "&&"; Prec = 2; Op = And }
      { Symb = "||"; Prec = 2; Op = Or }
      { Symb = "="; Prec = 3; Op = Eq }
      { Symb = "<"; Prec = 3; Op = Lt }
      { Symb = ">"; Prec = 3; Op = Gt }
      { Symb = "<="; Prec = 3; Op = Leq }
      { Symb = ">="; Prec = 3; Op = Geq }
      { Symb = "!="; Prec = 3; Op = Neq }
      { Symb = "+"; Prec = 4; Op = Add }
      { Symb = "-"; Prec = 4; Op = Sub }
      { Symb = "*"; Prec = 5; Op = Mul }
      { Symb = "/"; Prec = 5; Op = Div }
      { Symb = "%"; Prec = 5; Op = Mod }
      { Symb = "*/"; Prec = 5; Op = Frac } ]

/// Returns the string symbol of a binary operator
let symb (op: BinOp) =
    let rec loop =
        function
        | [] -> failwith $"Unknown binary operator: {op}"
        | { Symb = s; Prec = _; Op = op' } :: _ when op' = op -> s
        | _ :: tl -> loop tl

    loop binaryOperators


/// Returns the string symbol of an assignment operator
let assignmentSymb (op: AssignOp) =
    let rec loop =
        function
        | [] -> failwith $"Unknown assignment operator: {op}"
        | { Symb = s
            AssignmentOperator.Op = op' } :: _ when op' = op -> s
        | _ :: tl -> loop tl

    loop assignmentOperators

/// Transform a procedure identifier for procedure inversion.
/// Call procName = Uncall procName__Inv
/// Uncall procName = Call procName__Inv
/// TODO: Make sure in parser that no function name ends with __Inv
let invertProcName (procName: string) =
    let suffix = "__Inv"

    if procName.EndsWith suffix then
        procName.Remove(procName.Length - suffix.Length)
    else
        $"{procName}{suffix}"

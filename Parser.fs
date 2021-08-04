module Parser

open FParsec

open Ast

type UserState = Number list

type Parser<'a> = Parser<'a, UserState>

/// Parses comments.
let pcomment: Parser<unit> =
    spaces
    .>> many ((pstring "#") >>. skipRestOfLine true .>> spaces)

let ws = pcomment
let str_ws s = pstring s .>> ws

let keywords =
    [ [ "push"; "pop"; "skip"; "call"; "uncall"; "write" ] // statements
      [ "entry"; "exit"; "if"; "fi"; "goto"; "from"; "else" ] // control
      [ "not"; "top"; "empty" ] // expressions
      [ "int"; "stack" ] // type
      [ "proc"; "const"; "in"; "out"; "inout" ] // functions
      [ "define"; "local"; "delocal"; "blocal"; "bdelocal" ] ] // variables and constants
    |> List.concat

let isKeyword str = List.contains str keywords


/// Parses a string literal.
let pstringLiteral: Parser<string> =
    many1Satisfy2 isAsciiLetter (fun c -> isAsciiLetter c || isDigit c || c = '_')
    .>> ws

/// Parses a number literal.
let pnumberLiteral: Parser<int32> =
    pipe2
        (pstring "-" |> opt)
        (many1Satisfy isDigit .>> ws)
        (fun optSign n ->
            match optSign with
            | None -> n
            | Some _ -> "-" + n)
    |>> int32

/// Parses a valid identifier string.
let pidentifierString: Parser<string> =
    fun stream ->
        let oldState = stream.State

        let reply =
            stream
            |> (many1Satisfy2
                    (fun c -> c = '_' || isAsciiLetter c)
                    (fun c -> c = '_' || isAsciiLetter c || isDigit c)
                .>> ws)

        if (reply.Status = Ok && reply.Result |> isKeyword) then
            stream.BacktrackTo(oldState)
            Reply(Error, expected "identifier")
        else
            reply

/// Parses the tag of an already defined tagged number.
let ptag: Parser<Tag * int32> =

    let getTag (tag, _) = tag

    let rec look name lst =
        match lst with
        | [] -> failwith "cannot find defined constant in user state"
        | (tag, v) :: _ when tag = name -> (tag, v)
        | _ :: tl -> look name tl

    pidentifierString
    >>=? fun name ->
             userStateSatisfies (fun state -> List.contains name (state |> List.map getTag))
             >>. getUserState
             >>= fun state ->
                     let (k, v) = look name state
                     preturn (name, v)

/// Parses a number, i.e a tagged value of the form ("",7) or (ID, 8).
let pnumber =
    (pnumberLiteral |>> fun s -> ("", s)) <|> ptag

/// Parses a stack identifier.
let pstackString: Parser<string> = pidentifierString
// >>= fun name ->
//         updateUserState (fun state -> Set.add (name, StackVal []) state)
//         >>% name


let opp =
    new OperatorPrecedenceParser<Expr, unit, UserState>()

/// Parses an expression.
let pexpr: Parser<Expr> = opp.ExpressionParser

// Add all binary operators to the Operator Precedence Parser.
binaryOperators
|> List.iter
    (fun op ->
        opp.AddOperator(
            InfixOperator(op.Symb, ws, op.Prec, Associativity.Left, (fun x y -> BinOp(op.Op, x, y)))
        ))

// Assign lowest precedence to operator `not`.
opp.AddOperator(PrefixOperator("not", ws, 1, true, Not))

/// Parses an L-value.
let plval: Parser<LVal> =
    pipe2
        pidentifierString
        (between (str_ws "[") (str_ws "]") pexpr |> opt)
        (fun name indexOpt ->
            match indexOpt with
            | None -> Var name
            | Some e -> Index(name, e))

let ptop: Parser<Expr> =
    str_ws "top" >>. pidentifierString |>> Var |>> Top

let pempty: Parser<Expr> =
    str_ws "empty" >>. pidentifierString
    |>> Var
    |>> Empty

opp.TermParser <-
    (between (str_ws "(") (str_ws ")") pexpr)
    <|> ptop
    <|> pempty
    <|> (pnumber <?> "number" |>> Constant)
    <|> (plval |>> (fun x -> LVal(x)))


/// Parses a statement.
let pstmt, pstmtRef = createParserForwardedToRef ()

let passignAdd: Parser<Statement> =
    plval .>>.? (str_ws "+=" >>. pexpr)
    |>> fun (x, y) -> AssignOp(AssignAdd, x, y)

let passignSub: Parser<Statement> =
    plval .>>.? (str_ws "-=" >>. pexpr)
    |>> fun (x, y) -> AssignOp(AssignSub, x, y)

let passignXor: Parser<Statement> =
    plval .>>.? (str_ws "^=" >>. pexpr)
    |>> fun (x, y) -> AssignOp(AssignXor, x, y)

let ppush: Parser<Statement> =
    pipe2 (str_ws "push" >>. plval) pstackString (fun x s -> Push(x, s |> Var))

let ppop: Parser<Statement> =
    pipe2 (str_ws "pop" >>. plval) pstackString (fun x s -> Pop(x, s |> Var))

let pswap: Parser<Statement> =
    plval .>>.? (str_ws "<=>" >>. plval)
    |>> fun (x, y) -> Swap(x, y)

let pskip: Parser<Statement> = str_ws "skip" >>% Skip

let pwrite: Parser<Statement> =
    str_ws "write" >>. pidentifierString |>> Write

let pcall: Parser<Statement> =
    (str_ws "call" >>. pidentifierString)
    .>>. (between (str_ws "(") (str_ws ")") (sepBy pidentifierString (str_ws ",")))
    |>> Call

let puncall: Parser<Statement> =
    (str_ws "uncall" >>. pidentifierString)
    .>>. (between (str_ws "(") (str_ws ")") (sepBy pidentifierString (str_ws ",")))
    |>> Uncall


let plocalIntDecl: Parser<_> =
    (str_ws "int" >>. pidentifierString)
    .>>. (str_ws "=" >>. pnumber)
    |>> fun (id, n) -> (Int, id, n)

let pblocal: Parser<Statement> =
    str_ws "blocal" >>. plocalIntDecl |>> BLocal

let pbdelocal: Parser<Statement> =
    str_ws "bdelocal" >>. plocalIntDecl |>> BDelocal

do
    pstmtRef
    := choice [ passignAdd
                passignSub
                passignXor
                ppush
                ppop
                pswap
                pskip
                pwrite
                pcall
                puncall
                pblocal
                pbdelocal ]

/// Parses a sequence of statements.
let pstatements: Parser<Statement list> = sepBy pstmt (str_ws ";")

/// Parses a label.
let plabel: Parser<Label> = pidentifierString <?> "label"

/// Parses an arrival assertion.
let rec pArrival: Parser<Arrival> =
    fun stream -> (pfrom <|> pfifromelse <|> pentry <?> "Arrival") stream

and pfrom: Parser<Arrival> = str_ws "from" >>. plabel |>> From

and pfifromelse: Parser<Arrival> =
    tuple3 (str_ws "fi" >>. pexpr) (str_ws "from" >>. plabel) (opt (str_ws "else" >>. plabel))
    |>> (fun (x, y, elseOpt) ->
        match elseOpt with
        | Some z -> FiFromElse(x, y, z)
        | None -> FiFrom(x, y))

and pentry: Parser<Arrival> = str_ws "entry" >>% Entry

/// Parses a departure assertion
let rec pDeparture: Parser<Departure> =
    fun stream -> (pgoto <|> pifgotoelse <|> pexit <?> "Departure") stream

and pgoto: Parser<Departure> = str_ws "goto" >>. plabel |>> Goto

and pifgotoelse: Parser<Departure> =
    tuple3 (str_ws "if" >>. pexpr) (str_ws "goto" >>. plabel) (opt (str_ws "else" >>. plabel))
    |>> (fun (x, y, elseOpt) ->
        match elseOpt with
        | Some z -> IfGotoElse(x, y, z)
        | None -> IfGoto(x, y))

and pexit: Parser<Departure> = str_ws "exit" >>% Exit

/// Parses a block
let pblock: Parser<Block> =
    tuple4 (plabel .>> str_ws ":") pArrival pstatements pDeparture
    |>> Block

/// Parses a procedure
let pprocedure: Parser<Proc> =
    let pqualifier: Parser<Qualifier> =
        choice [ (str_ws "const" >>% Const)
                 (str_ws "inout" >>% InOut)
                 (str_ws "in" >>% In)
                 (str_ws "out" >>% Out) ]

    let ptype: Parser<Type> =
        choice [ (str_ws "stack" >>% Stack)

                 (pstring "int") >>. (opt (str_ws "[]")) .>> ws
                 |>> fun optBracket ->
                         match optBracket with
                         | None -> Int
                         | Some _ -> Array ]

    let pparam: Parser<Param> =
        tuple3 pqualifier ptype pidentifierString
        |>> Param

    let plocalIntDeclWithExpr: Parser<_> =
        (str_ws "int" >>. pidentifierString)
        .>>. (str_ws "=" >>. pexpr)
        |>> fun (id, e) -> (Int, id, e)

    let plocal: Parser<Local list> =
        (opt (
            str_ws "local"
            >>. sepBy1 plocalIntDeclWithExpr (str_ws ",")
        ))
        |>> fun optLocal ->
                match optLocal with
                | None -> []
                | Some lst -> lst

    let pdelocal: Parser<Delocal list> =
        (opt (
            str_ws "delocal"
            >>. sepBy1 plocalIntDeclWithExpr (str_ws ",")
        ))
        |>> fun optLocal ->
                match optLocal with
                | None -> []
                | Some lst -> lst

    tuple5
        (str_ws "proc" >>. pidentifierString)
        (between (str_ws "(") (str_ws ")") (sepBy pparam (str_ws ",")))
        plocal
        (many1 pblock)
        pdelocal
    |>> Proc

/// Parses a global constants definition (the `define` directive)
let pdefine: Parser<Identifier * int32> =
    tuple2 (str_ws "define" >>. pidentifierString) (pnumberLiteral)
    >>= fun (id, v) ->
            updateUserState (fun state -> (id, v) :: state)
            >>% (id, v)

/// Parses a program
let pprogram: Parser<Program> =
    ws >>. (many pdefine .>>. many1 pprocedure)
    .>> ws
    .>> eof
    |>> Program

module InterpreterTest

open System.IO
open Xunit
open Ast
open Parser
open Interpreter

[<Fact>]
let interpreter_global_constants_are_immutable () =

    let source =
        @"
  define A 7
  proc main()
  local int x=3
  lab0:
    entry
    x += A;
    A += 1
    goto lab1
  lab1:
    from lab0
    exit
  delocal int x=10
  "
    let func =
        fun () ->
            Test.parse pprogram source
            |> evalProgram "output.txt" []
            |> ignore

    Assert.Throws<InterpreterError>(func) |> ignore

[<Fact>]
let interpreter_fib_test () =
    let content =
        System.IO.File.ReadAllText(Path.Join(Test.root, "Samples", "fib", "fib.rufc"))

    let prog = Test.parse pprogram content

    let vtab =
        [ ("a", IntVal("", 0)); ("b", IntVal("", 0)); ("n", IntVal("", 10)) ]

    try
        let (_, res) = evalProgram "output.txt" vtab prog

        let expected =
            SymTab.ofList [ ("a", (Local, IntVal("", 89)))
                            ("b", (Local, IntVal("", 144)))
                            ("n", (Local, IntVal("", 0))) ]

        Assert.Equal(expected, res)
    with
    | InterpreterError msg -> printfn $"error:{msg}"

[<Fact>]
let interpreter_mult_test () =
    let content =
        System.IO.File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult.rufc"))

    let prog = Test.parse pprogram content

    let vtab =
        [ ("a", IntVal("", 11)); ("b", IntVal("", 13)); ("prod", IntVal("", 0)) ]

    try
        let (_, res) = evalProgram "output.txt" vtab prog

        let expected =
            SymTab.ofList [ ("a", (Local, IntVal("", 0)))
                            ("b", (Local, IntVal("", 13)))
                            ("prod", (Local, IntVal("", 143))) ]

        Assert.Equal(expected, res)
    with
    | InterpreterError msg -> printfn $"error:{msg}"


[<Fact>]
let interpreter_mult_indirect_test () =
    let content =
        System.IO.File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult_indirect.rufc"))

    let prog = Test.parse pprogram content

    let vtab =
        [ ("a", IntVal("", 11)); ("b", IntVal("", 13)); ("prod", IntVal("", 0)) ]

    try
        let (_, res) = evalProgram "output.txt" vtab prog

        let expected =
            SymTab.ofList [ ("a", (Local, IntVal("", 0)))
                            ("b", (Local, IntVal("", 13)))
                            ("prod", (Local, IntVal("", 143))) ]

        Assert.Equal(expected, res)
    with
    | InterpreterError msg -> printfn $"error:{msg}"

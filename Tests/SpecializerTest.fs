module SpecializerTest

open System.IO

open Xunit
open Ast
open Parser
open Specializer
open Test
open Interpreter
open CodeGen
open Optimizer
open InputParser

[<Fact>]
let specializer_mult_indirect_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult_indirect.rufc"))

    let mult = parse pprogram content

    let args =
        [ ("a", IntVal("", 5) |> S)
          ("b", (LVal(Var "b")) |> D)
          ("prod", (LVal(Var "prod")) |> D) ]

    try
        let resProg = onpeProgram args mult

        let (_, vtabOut) =
            evalProgram "write_test.txt" [ ("b", IntVal("", 9)); ("prod", IntVal("", 0)) ] resProg

        ()

    with
    | SpecializerError msg -> Assert.True(false, $"error: {msg}")
    | InterpreterError msg -> Assert.True(false, $"error: {msg}")

[<Fact>]
let specializer_mult_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult.rufc"))

    let mult = parse pprogram content

    let args =
        [ ("a", IntVal("", 5) |> S)
          ("b", (LVal(Var "b")) |> D)
          ("prod", (LVal(Var "prod")) |> D) ]

    try
        let residualProg = onpeProgram args mult

        let pe_expected: string =
            File.ReadAllText(Path.Join(Test.root, "Tests", "mult", "pe_expected.rufc"))

        Assert.Equal(pe_expected, residualProg |> ppProgram)

        let (_, vtabOut) =
            evalProgram
                "write_test.txt"
                [ ("b", IntVal("", 9)); ("prod", IntVal("", 0)) ]
                residualProg

        let expectedVtabOut =
            [ ("b", (Local, IntVal("", 9))); ("prod", (Local, IntVal("", 45))) ]
            |> SymTab.ofList

        Assert.Equal(expectedVtabOut, vtabOut)

    with
    | OptimizerError msg -> Assert.True(false, $"error: {msg}")
    | SpecializerError msg -> Assert.True(false, $"error: {msg}")
    | InterpreterError msg -> Assert.True(false, $"error: {msg}")


[<Fact>]
let specializer_fib_test () =

    let content =
        System.IO.File.ReadAllText(Path.Join(Test.root, "Samples", "fib", "fib.rufc"))

    let fib = parse pprogram content

    let args =
        [ ("a", (LVal(Var "a")) |> D)
          ("b", (LVal(Var "b")) |> D)
          //("n", (LVal(Var "n")) |> D)
          // ("a", IntVal("", 0) |> S)
          // ("b", IntVal("", 0) |> S)
          ("n", IntVal("", 5) |> S) ]

    try
        let residualProg = onpeProgram args fib
        ()

    with
    | SpecializerError msg -> Assert.True(false, $"error: {msg}")
    | InterpreterError msg -> Assert.True(false, $"error: {msg}")


[<Fact>]
let specializer_rtm_interpreter_test () =
    // dotnet test --filter specializer_rtm_interpreter_test ./Tests

    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "rtm_interpreter", "rtm_interpreter.rufc"))

    let (rtm_interpreter, userState) = Test.parseWithState pprogram content

    let staticArgs =
        (match readParameterFile (Path.Join(root, "Tests", "rtm_interpreter", "vtab_static.in")) with
         | None -> failwith "unable to read file"
         | Some lst -> lst)
        |> List.map
            (fun (id, v) ->
                let (id', v') =
                    updateValueUsingUserState userState (id, v)

                (id', S(v')))

    let dynamicArgs =
        [ ("s", LVal(Var "s") |> D)
          ("left", LVal(Var "left") |> D)
          ("right", LVal(Var "right") |> D) ]

    let args = staticArgs @ dynamicArgs

    try
        let residualProg = onpeProgram args rtm_interpreter

        let directory =
            Path.Join(Test.root, "Tests", "rtm_interpreter")

        let pe_expected: string =
            System.IO.File.ReadAllText(Path.Join(directory, "pe_expected.rufc"))

        Assert.Equal(pe_expected, residualProg |> ppProgram)

        let dynamicTab =
            [ ("s", IntVal("BLANK", 2))
              ("left", StackVal List.empty)
              ("right",
               StackVal [ ("", 1)
                          ("", 1)
                          ("", 0)
                          ("", 1) ]) ]

        let (resProg, residualTabOut) =
            evalProgram $"write_test.txt" dynamicTab residualProg

        let expectedResidualTabOut =
            System.IO.File.ReadAllText(Path.Join(directory, "vtab_dynamic_forward_expected.out"))

        Assert.Equal(expectedResidualTabOut, residualTabOut |> ppVtab)

        let invertedResidualProg = Inverter.invertProgram residualProg

        let dynamicTabRev =
            [ ("s", IntVal("BLANK", 2))
              ("left", StackVal List.empty)
              ("right",
               StackVal [ ("", 0)
                          ("", 0)
                          ("", 1)
                          ("", 1) ]) ]

        let (invProg, invTabOut) =
            evalProgram $"write_test.txt" dynamicTabRev invertedResidualProg

        let expectedInvTabOut =
            System.IO.File.ReadAllText(Path.Join(directory, "vtab_dynamic_backward_expected.out"))

        Assert.Equal(expectedInvTabOut, invTabOut |> ppVtab)

    with
    | SpecializerError msg -> Assert.True(false, $"error: {msg}")
    | InterpreterError msg -> Assert.True(false, $"error: {msg}")
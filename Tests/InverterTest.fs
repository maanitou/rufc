module InverterTest

open System.IO
open Xunit
open Ast
open Parser
open Inverter
open Interpreter

[<Fact>]
let inv_fib_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "fib", "fib.rufc"))

    let prog = Test.parse pprogram content

    let vtab =
        [ ("a", IntVal("", 0)); ("b", IntVal("", 0)); ("n", IntVal("", 10)) ]

    try
        evalProgram "output.txt" vtab prog |> ignore
    with
    | InterpreterError msg -> printfn $"error:{msg}"

    let progInv = invertProgram prog

    let vtabInv =
        [ ("a", IntVal("", 89)); ("b", IntVal("", 144)); ("n", IntVal("", 0)) ]

    try
        evalProgram "output.txt" vtabInv progInv |> ignore
    with
    | InterpreterError msg -> printfn $"error:{msg}"

[<Fact>]
let inv_mult_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult.rufc"))

    let prog = Test.parse pprogram content

    let vtab =
        [ ("a", IntVal("", 11)); ("b", IntVal("", 13)); ("prod", IntVal("", 0)) ]

    try
        evalProgram "output.txt" vtab prog |> ignore
    with
    | InterpreterError msg -> printfn $"error:{msg}"

    let progInv = invertProgram prog

    let vtabInv =
        [ ("a", IntVal("", 0)); ("b", IntVal("", 13)); ("prod", IntVal("", 143)) ]

    try
        evalProgram "output.txt" vtabInv progInv |> ignore
    with
    | InterpreterError msg -> printfn $"error:{msg}"

module DivisorTest

open System.IO
open Xunit
open Ast
open SymTab
open Parser
open Divisor

let assertDivMatches div expected' =

    let expected =
        expected'
        |> List.map (fun (fname, lst) -> (fname, lst |> SymTab.ofList))
        |> Map.ofList

    let actual: Map<Identifier, Division> =
        div
        |> List.map (fun (x, _, z) -> (x, z))
        |> Map.ofList

    Assert.Equal(expected.Count, actual.Count)

    let keys =
        expected |> Map.toList |> List.unzip |> fst

    Assert.True(keys |> List.forall actual.ContainsKey)

    keys
    |> List.iter (fun key -> Assert.Equal(expected.Item(key), actual.Item(key)))


[<Fact>]
let div_mult_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult.rufc"))

    let prog = Test.parse pprogram content

    let initialDiv =
        [ ("a", S); ("b", D); ("prod", S) ]
        |> SymTab.ofList

    try
        let div = uniformDivision initialDiv prog

        let expected =
            [ ("main", [ ("a", S); ("b", D); ("prod", D); ("t", S); ("v", D) ]) ]

        assertDivMatches div expected

    with
    | DivisorError msg -> printfn $"error:{msg}"

[<Fact>]
let div_mult_indirect_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult_indirect.rufc"))

    let prog = Test.parse pprogram content

    let initialDiv =
        [ ("a", S); ("b", D); ("prod", S) ]
        |> SymTab.ofList

    try
        let div = uniformDivision initialDiv prog

        let expected =
            [ ("main", [ ("a", S); ("b", D); ("prod", D) ])
              ("mult", [ ("a", S); ("b", D); ("prod", D); ("t", S); ("v", D) ]) ]

        assertDivMatches div expected

    with
    | DivisorError msg -> printfn $"error:{msg}"

[<Fact>]
let div_mult_with_blocals_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "mult", "mult_with_blocals.rufc"))

    let prog = Test.parse pprogram content

    let initialDiv =
        [ ("a", S); ("b", D); ("prod", S) ]
        |> SymTab.ofList

    try
        let div = uniformDivision initialDiv prog

        let expected =
            [ ("main",
               [ ("a", S); ("b", D); ("prod", D); ("t0", S); ("t1", S); ("v0", D); ("v1", D) ]) ]

        assertDivMatches div expected

    with
    | DivisorError msg -> printfn $"error: {msg}"
    | SymTabError msg -> printfn $"error: {msg}"

[<Fact>]
let div_fib_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "fib", "fib.rufc"))

    let prog = Test.parse pprogram content

    let initialDiv =
        [ ("a", D); ("b", D); ("n", S) ] |> SymTab.ofList

    try
        let div = uniformDivision initialDiv prog

        let expected =
            [ ("main", [ ("a", S); ("b", S); ("n", S) ])
              ("fib", [ ("x1", S); ("x2", S); ("n", S); ("v", S) ]) ]

        assertDivMatches div expected

    with
    | DivisorError msg -> printfn $"error:{msg}"


[<Fact>]
let div_schrodinger_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "schrodinger", "schrodinger.rufc"))

    let prog = Test.parse pprogram content

    let initialDiv =
        [ ("X", D); ("Y", D); ("maxn", D); ("epsilon", S); ("alpha", S) ]
        |> SymTab.ofList

    try
        let div = uniformDivision initialDiv prog

        let expected =
            [ ("main",
               [ ("X", D); ("Y", D); ("alpha", S); ("epsilon", S); ("i", S); ("maxn", D); ("n", S) ]) ]

        assertDivMatches div expected

    with
    | DivisorError msg -> printfn $"error:{msg}"


[<Fact>]
let div_rtm_test () =
    let content =
        File.ReadAllText(Path.Join(Test.root, "Samples", "rtm_interpreter", "rtm_interpreter.rufc"))

    let prog = Test.parse pprogram content

    let initialDiv =
        [ ("q", S)
          ("left", S)
          ("s", D)
          ("right", S)
          ("q1", S)
          ("s1", S)
          ("s2", S)
          ("q2", S)
          ("pc", S)
          ("PC_MAX", S) ]
        |> Map.ofList
        |> SymTab

    try
        let div = uniformDivision initialDiv prog

        let expected =
            [ ("main",
               [ ("PC_MAX", S)
                 ("left", D)
                 ("right", D)
                 ("pc", S)
                 ("q", D)
                 ("s", D)
                 ("q1", S)
                 ("q2", S)
                 ("s1", S)
                 ("s2", S) ])
              ("inst",
               [ ("left", D)
                 ("right", D)
                 ("pc", S)
                 ("q", D)
                 ("s", D)
                 ("q1", S)
                 ("q2", S)
                 ("s1", S)
                 ("s2", S) ])
              ("pushtape", [ ("s", D); ("stk", D) ])
              ("pushtape__Inv", [ ("s", D); ("stk", D) ]) ]

        assertDivMatches div expected
    with
    | DivisorError msg -> printfn $"error:{msg}"

module ParserTest

open System.IO
open Xunit
open Ast
open Parser

[<Fact>]
let procedure_test () =

  let input =
    [ "proc main(in int a, out int b, inout int prod)"; "lab0:"; "entry"; "goto lab1" ]
    |> String.concat "\n"

  let actual = Test.parse pprocedure input

  let expected =
    Proc(
      "main",
      [ (In, Int, "a"); (Out, Int, "b"); (InOut, Int, "prod") ],
      [],
      [ Block("lab0", Entry, [], Goto "lab1") ],
      []
    )

  Assert.Equal(expected, actual)

  let input =
    [
      "proc main(const int[] q1, const int[] s1, inout stack right)";
      "lab0:";
      "entry";
      "goto lab1"
    ]
    |> String.concat "\n"

  let expected =
    Proc(
      "main",
      [ (Const, Array, "q1"); (Const, Array, "s1"); (InOut, Stack, "right") ],
      [],
      [ Block("lab0", Entry, [], Goto "lab1") ],
      []
    )

  let actual = Test.parse pprocedure input

  Assert.Equal(expected, actual)

[<Fact>]
let define_test () =
  let content =
    Path.Join(Test.root, "Samples", "rtm_interpreter", "rtm_interpreter.rufc")
    |> System.IO.File.ReadAllText

  Test.parse pprogram content |> ignore
  ()

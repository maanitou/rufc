module InputParserTest

open Xunit

open InputParser
open Test

[<Fact>]
let inputParser_noOptions_test () =

    Assert.Equal(
        { defaultCommandLineOption with
              role = Interpreter
              direction = Forward },
        parse (prole defaultCommandLineOption) "--interpreter"
    )

    Assert.Equal(
        { defaultCommandLineOption with
              role = Interpreter
              direction = Backward },
        parse (prole defaultCommandLineOption) "--interpreter --backward"
    )


    Assert.Equal(
        { defaultCommandLineOption with
              role = Inverter },
        parse (prole defaultCommandLineOption) "--inverter"
    )

    Assert.Equal(
        { defaultCommandLineOption with
              role = Specializer },
        parse (prole defaultCommandLineOption) "--specializer"
    )


[<Fact>]
let inputParser_withOptions_test () =

    let actual =
        parse pcommandline "rufc --interpreter --input=vtab.in"

    let expected =
        ("rufc",
         { defaultCommandLineOption with
               role = Interpreter
               direction = Forward
               inputTab = Some "vtab.in" },
         List.empty)

    Assert.Equal(expected, actual)

    Assert.Equal(
        ("rufc",
         { defaultCommandLineOption with
               role = Interpreter
               direction = Forward
               inputTab = Some "vtab.in" },
         []),
        parse pcommandline "rufc --interpreter --input=vtab.in"
    )

    Assert.Equal(
        ("rufc",
         { defaultCommandLineOption with
               role = Interpreter
               direction = Backward
               inputTab = Some "vtab.in"
               outputTab = Some "vtab.out"
               writeFile = Some "output.txt" },
         []),
        parse
            (pcommandline)
            "rufc --interpreter --backward --write = output.txt --output=vtab.out --input=vtab.in"
    )

    Assert.Equal(
        ("rufc",
         { defaultCommandLineOption with
               role = Specializer
               direction = Forward
               inputTab = Some "vtab.in"
               outputTab = Some "vtab.out"
               writeFile = Some "output.txt"
               outFile = Some "specialized.rufc" },
         []),
        parse
            (pcommandline)
            "rufc --specializer --out = specialized.rufc --write = output.txt --output=vtab.out --input=vtab.in"
    )


    assertEqual (
        ("rufc",
         { defaultCommandLineOption with
               role = Inverter
               direction = Forward
               outFile = Some "inverted.rufc"
               writeFile = Some "output.txt" },
         [ ("x", 5) ]),
        "rufc --inverter --write=output.txt --out=inverted.rufc x=5",
        pcommandline
    )

    assertEqual (
        ("rufc",
         { defaultCommandLineOption with
               role = Specializer },
         [ ("a", 3); ("b", 5); ("prod", 0) ]),
        "rufc --specializer  a=3 b=5 prod=0",
        pcommandline
    )

open FParsec

open Ast
open SymTab
open CodeGen
open Parser
open Interpreter
open Inverter
open InputParser

[<EntryPoint>]
let main argv =

    if (Array.isEmpty argv) then
        [ "usage\n"
          "dotnet run INPUT_PROGRAM"
          "| --interpret [--backward] [--input VTAB_FILE] [--output VTAB_FILE] [--write WRITE_FILE] [VAR=VALUE ...]"
          "| --specialize [--out SPECIALIZED_FILE] [--input VTAB_FILE] [--output VTAB_FILE] [--write WRITE_FILE] [VAR=VALUE ...]"
          "| --invert [--out INVERTED_FILE]" ]
        |> String.concat "\n"
        |> printfn "%s"

        -1
    else
        let (filename: string, options, args) =
            match runParserOnString pcommandline [] "" (argv |> String.concat " ") with
            | Success (result, _, _) -> result
            | Failure (error, _, _) -> failwith $"{error}"

        let suffix = "rufc"

        let basename =
            if filename.EndsWith($".{suffix}") then
                filename.Remove(filename.Length - (suffix.Length + 1))
            else
                filename

        let code =
            System.IO.File.ReadAllLines($"{basename}.{suffix}")
            |> String.concat "\n"


        let inputVtabFromFile =
            match options.inputTab with
            | Some inputFileName ->
                match readParameterFile inputFileName with
                | None -> failwith "unable to read the input parameter file"
                | Some tab -> tab |> Map.ofList |> SymTab
            | None -> Map.empty |> SymTab

        let inputVtabFromCmd: (string * Value) list =
            List.map (fun (name, value) -> (name, int32 value |> fun v -> IntVal("", v))) args

        let vtabOutFileName =
            match options.outputTab with
            | Some file -> file
            | None ->
                match options.direction with
                | Forward -> $"vtab_{basename}_forward.out"
                | Backward -> $"vtab_{basename}_backward.out"

        let writeFileName =
            match options.writeFile with
            | Some file -> file
            | None ->
                match options.direction with
                | Forward -> $"output_{basename}_forward.txt"
                | Backward -> $"output_{basename}_backward.txt"

        let outFileName =
            match options.outFile with
            | Some file -> file
            | None ->
                match options.role with
                | Inverter -> $"{basename}_inv.rufc"
                | Specializer -> $"{basename}_pe.rufc"
                | Interpreter -> $""


        try
            match options.role with
            | Interpreter ->
                printfn "Preparing interpreter..."

                if options.outFile <> None then
                    eprintfn "\nWARNING: --out file will not be used when using the interpreter.\n"

                let (SymTab vtabDict) =
                    (inputVtabFromFile, inputVtabFromCmd)
                    ||> List.fold (fun tab (k, v) -> bindOrUpdate k v tab)

                let vtab' = Map.toList vtabDict

                match runParserOnString pprogram [] "" code with
                | Failure (error, _, _) -> printfn $"error:{error}\n"
                | Success (Program (defs, procs), userState, _) ->

                    printfn $"User state:\n{pprintSet (Set.ofList userState)}\n"

                    (* Update vtab using the constant definitions stored in userState *)
                    let vtab: (string * Value) list =
                        List.map (updateValueUsingUserState userState) vtab'

                    let prog = Program(defs, procs)

                    let prog' =
                        match options.direction with
                        | Backward -> invertProgram prog
                        | Forward -> prog


                    let (ftabOut, vtabOut) = evalProgram writeFileName vtab prog'

                    System.IO.File.WriteAllText(vtabOutFileName, vtabOut |> ppVtab |> string)

                    vtabOut |> ppVtab |> printfn "Evaluation:\n%A\n"

                    ()


            | Inverter ->
                printfn "Preparing inverter..."

                if options.inputTab <> None
                   || options.outputTab <> None
                   || options.writeFile <> None
                   || inputVtabFromCmd <> [] then
                    printfn
                        "\nWARNING: --input, --output, --write files, and extra vtab arguments are not used for inversion.\n"

                match runParserOnString pprogram [] "" code with
                | Failure (error, _, _) -> printfn $"error: {error}\n"
                | Success (Program (defs, procs) as prog, userState, _) ->
                    let invertedProg = Inverter.invertProgram prog
                    System.IO.File.WriteAllText(outFileName, invertedProg |> ppProgram)
                    printfn $"Inverted program has been written to {outFileName}"



            | Specializer ->
                printfn "Preparing specializer..."

                let (SymTab vtabDict) =
                    (inputVtabFromFile, inputVtabFromCmd)
                    ||> List.fold (fun tab (k, v) -> bindOrUpdate k v tab)

                let vtab' = Map.toList vtabDict

                match runParserOnString pprogram [] "" code with
                | Failure (error, _, _) -> printfn $"error:{error}\n"
                | Success (Program (defs, procs) as prog, userState, _) ->

                    printfn $"User state:\n{pprintSet (Set.ofList userState)}\n"

                    (* Update vtab using the constant definitions stored in userState *)
                    let staticVtab: (Identifier * Specializer.SDValue) list =
                        List.map (updateValueUsingUserState userState) vtab'
                        |> List.map (fun (id, v) -> (id, Specializer.S v))

                    let mainParams =
                        match Tools.resolveMainProc prog with
                        | (None, message) -> error message
                        | (Some p, _) ->
                            p
                            |> Tools.getProcParams
                            |> List.map (fun (q, t, id) -> id)

                    let dynamicVtab: (Identifier * Specializer.SDValue) list =
                        mainParams
                        |> List.filter
                            (fun par ->
                                not
                                <| List.exists (fun (k, v) -> k = par) staticVtab)
                        |> List.map (fun id -> (id, LVal(Var id) |> Specializer.D))

                    let vtab = staticVtab @ dynamicVtab

                    [ for entry in vtab do
                          printfn $"{entry}" ]
                    |> ignore

                    match runParserOnString pprogram [] "" code with
                    | Failure (error, _, _) -> printfn $"error:{error}\n"
                    | Success (Program (defs, procs), userState, _) ->
                        let specializedProg = Specializer.onpeProgram vtab prog
                        System.IO.File.WriteAllText(outFileName, specializedProg |> ppProgram)

                    printfn $"Specialized program has been written to {outFileName}"
                    ()

        with
        | InterpreterError e -> printfn $"Interpreter error: {e}"
        | Specializer.SpecializerError e -> printfn $"Specializer error: {e}"
        | Optimizer.OptimizerError e -> printfn $"Optimizer error: {e}"
        | SymTabError e -> printfn $"SymTab error: {e}"

        0

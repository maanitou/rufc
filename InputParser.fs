module InputParser

open FParsec

open Ast
open Parser

(*
dotnet run INPUT_PROGRAM
  | [--interpret [--backward]] [--input VTAB_FILE] [--output VTAB_FILE] [--write WRITE_FILE] [VAR=VALUE ...]
  | --specialize [--out SPECIALIZED_FILE] [--input VTAB_FILE] [--output VTAB_FILE] [--write WRITE_FILE] [VAR=VALUE ...]
  | --invert [--out INVERTED_FILE]


invert: if the --out file is omitted, then the inverted sample.rufc is written to sample_inv.rufc

interpret, specialize:
  1) if the --output file is omitted, then output vtab is written to `vtab_forward.out` or `vtab_backward.out` depending on hether the --backward flag is used or not.
  2) if the --write file is omitted, then all output produced by a Write command is sent to sample_output.txt
  3) VAR=VALUE can be used to specify input parameters to the program or to override input parameters read in the input file.

Options:

dotnet run mult.rufc a=7 b=9 prod=0 // interpretation of 7*9   --> default output file
dotnet run mult.rufc --interpret a=7 b=9 prod=0 // interpretation of 7*9   --> default output file
dotnet run mult.rufc --partial a=7  // specialize mult wrt a=7 --> default output file
dotnet run mult.rufc -- partial --input vtab_mult.in
*)

type Direction =
    | Forward
    | Backward

type Role =
    | Interpreter
    | Specializer
    | Inverter

type CommandLineOption =
    { role: Role
      direction: Direction
      inputTab: string option
      outputTab: string option
      outFile: string option
      writeFile: string option }

/// Parse a filename
let pfilename: Parser<string> =
    many1Satisfy (fun c -> c <> ' ' && c <> '\t')
    .>> ws

(* Parse command line arguments *)
let parg: Parser<string * int32> =
    pidentifierString
    .>>. (str_ws "=" >>. pnumberLiteral .>> ws)

let defaultCommandLineOption =
    { role = Interpreter
      direction = Forward
      inputTab = None
      outputTab = None
      outFile = None
      writeFile = None }

let pinverter defaultCLO =
    (str_ws "--inverter")
    >>% { defaultCLO with role = Inverter }
// >>. (opt (str_ws "--out" >>. pfilename))
// |>> fun outFile ->
//         { defaultCLO with
//               role = Inverter
//               outFile = outFile }
// .>> (eof <?> "no more command line arguments")

let pinterpreter defaultCLO : Parser<CommandLineOption> =
    str_ws "--interpreter"
    >>. opt (str_ws "--backward")
    |>> (fun direction ->
        match direction with
        | Some _ -> { defaultCLO with direction = Backward }
        | None -> defaultCLO)

let pspecializer defaultCLO : Parser<CommandLineOption> =
    str_ws "--specializer"
    >>% { defaultCLO with role = Specializer }

let prole defaultCLO =
    choice [ pinverter defaultCLO
             pinterpreter defaultCLO
             pspecializer defaultCLO ]
//|>> function  newClo -> newClo


let parguments = many parg

let rec poptional (defaultCLO: CommandLineOption) =
    choice [ str_ws "--input" >>. (str_ws "=" >>. pfilename)
             |>> (fun file -> { defaultCLO with inputTab = Some file })
             str_ws "--output" >>. (str_ws "=" >>. pfilename)
             |>> (fun file ->
                 { defaultCLO with
                       outputTab = Some file })
             str_ws "--out" >>. (str_ws "=" >>. pfilename)
             |>> (fun file -> { defaultCLO with outFile = Some file })
             str_ws "--write" >>. (str_ws "=" >>. pfilename)
             |>> (fun file ->
                 { defaultCLO with
                       writeFile = Some file }) ]
    |> opt
    >>= fun newOptionOpt ->
            match newOptionOpt with
            | None -> preturn defaultCLO .>>. parguments
            | Some newOption -> poptional newOption
    <?> "--input, --output, --out, --write, or extra parameters"

let eoc = eof <?> "end of command line"

let pcommandline =
    pipe2
        pfilename
        (prole defaultCommandLineOption >>= poptional
         .>> eoc)
        (fun x (y, z) -> (x, y, z))

/// Read file of arguments
let readParameterFile filename : option<(string * Value) list> =

    let f name optStack (value: (string * int32) list) =
        match optStack with
        | None ->
            match value with
            | [] -> failwith "Incorrect parameter declaration. No value provided."
            | v :: [] -> (name, IntVal v)
            | _ -> (name, ArrayVal(Array.ofList value))
        | Some _ -> (name, StackVal value)

    let pparam =
        pipe3
            (pidentifierString .>> str_ws ":")
            (opt (str_ws "stack"))
            (manyTill
                ((pnumberLiteral |>> fun nn -> ("", int32 nn))
                 <|> (pidentifierString |>> fun str -> (str, int32 0)))
                (str_ws ";"))
            f

    let content =
        System.IO.File.ReadAllLines(filename)
        |> String.concat "\n"


    match runParserOnString (ws >>. many pparam .>> ws .>> eof) [] "" content with
    | Success (result, _, _) -> Some result
    | Failure (error, _, _) ->
        printfn "Error while parsing input parameters file:\n%s\n" error
        None

let updateValueUsingUserState (state: UserState) ((name, v): string * Value) =
    let map = state |> Map.ofList

    let v' =
        match v with
        | IntVal (tag, _) ->
            if tag = "" then
                v
            else
                IntVal(tag, Map.find tag map)
        | ArrayVal arr ->
            arr
            |> Array.map
                (fun (tag, ev) ->
                    if tag = "" then
                        (tag, ev)
                    else
                        (tag, Map.find tag map))
            |> ArrayVal
        | StackVal lst ->
            lst
            |> List.map
                (fun (tag, ev) ->
                    if tag = "" then
                        (tag, ev)
                    else
                        (tag, Map.find tag map))
            |> StackVal

    (name, v')

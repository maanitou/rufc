module Test

open System.IO
open Xunit
open FParsec

open Parser

exception TestError of string

let root = Path.Join("..","..","..","..")

let parse<'a> (p: Parser<'a>) input =
    match runParserOnString p [] "" input with
    | Success (result, _, _) -> result
    | Failure (error, _, _) ->
        printfn $"error: {error}"
        raise (TestError $"{error}")

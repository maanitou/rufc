module Test

open System.IO
open FParsec
open Xunit

open Parser

exception TestError of string

let root = Path.Join("..","..","..","..")

let parse<'a> (p: Parser<'a>) input =
    match runParserOnString p [] "" input with
    | Success (result, _, _) -> result
    | Failure (error, _, _) ->
        printfn $"error: {error}"
        raise (TestError $"{error}")

let parseWithState<'a> (p: Parser<'a>) input =
    match runParserOnString p [] "" input with
    | Success (result, userState, _) -> (result, userState)
    | Failure (error, _, _) ->
        printfn $"error: {error}"
        raise (TestError $"{error}")

let assertEqual<'a> (expected: 'a, input: string, p: Parser<'a>) =
    match runParserOnString p [] "" input with
    | Success (result, _, _) -> Assert.Equal(expected, result)
    | Failure (error, _, _) -> Assert.True(false, error)

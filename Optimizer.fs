module Optimizer

open Ast
open Tools
open SymTab
open CodeGen

exception OptimizerError of string
let error str = raise (OptimizerError str)


let createBlockMap blocks =
    blocks
    |> List.map
        (fun block ->
            match block with
            | Block (label, _, _, _) as block -> (label, block))
    |> Map.ofList

let blockListToBlockMap (blocks: Block list) : Map<Label, Block> =
    blocks
    |> List.map
        (fun blk ->
            match blk with
            | Block (lab, _, _, _) as blk -> (lab, blk))
    |> Map.ofList

let blockMapToBlockList (map: Map<Label, Block>) : Block list =
    map |> Map.toList |> List.unzip |> snd


/// Merge the statements of two blocks when there is a one-way link between lab1 to lab2
/// Note that the children of lab2 shoud no longer expect to be reached from lab2, but from lab1
let merge (Block (lab1, arr1, stmts1, dep1)) (Block (lab2, arr2, stmts2, dep2)) =
    match (dep1, arr2) with
    | (Goto lab2, From lab1) -> Block(lab1, arr1, stmts1 @ stmts2, dep2)
    | _ -> error $"block {lab1} cannot be merged with {lab2}: not an unconditional transition"

let tryFindBlock (lab: Label) (blocks: Block list) : Block option =
    List.tryFind (fun (Block (lab', _, _, _)) -> lab = lab') blocks

let getDestinationLabels (Block (_, _, _, dest)) =
    match dest with
    | Exit -> []
    | Goto lab -> [ lab ]
    | IfGoto (_, lab) -> [ lab ]
    | IfGotoElse (_, labT, labF) -> [ labT; labF ]

let mergeBlocksInDictionary lab1 lab2 (blocks: Map<Label, Block>) =

    let update k v map =
        Map.change
            k
            (fun lab1 ->
                match lab1 with
                | None -> failwith $"key {k} not found in the map"
                | Some _ -> Some v)
            map

    match (Map.tryFind lab1 blocks, Map.tryFind lab2 blocks) with
    | (Some block1, Some block2) ->
        let mergedBlock = merge block1 block2

        let blocks' =
            blocks
            |> update lab1 mergedBlock
            |> Map.remove lab2

        let grandChildren =
            List.map (fun lab -> Map.find lab blocks') (getDestinationLabels block2)

        let newGrandChildren =
            grandChildren
            |> List.map
                (fun (Block (x, arr, y, z)) ->
                    let newArrival =
                        match arr with
                        | Entry -> Entry
                        | From _ -> From lab1
                        | FiFrom (e, _) -> FiFrom(e, lab1)
                        | FiFromElse (e, labT, labF) when labT = lab2 -> FiFromElse(e, lab1, labF)
                        | FiFromElse (e, labT, labF) when labF = lab2 -> FiFromElse(e, labT, lab1)
                        | _ -> error ""

                    Block(x, newArrival, y, z))

        (blocks', newGrandChildren)
        ||> List.fold
                (fun acc b ->
                    match b with
                    | Block (lab, _, _, _) -> update lab b acc)

    | _ -> error ""

let rec tryFindCompressibleBlocks (blocks: Map<Label, Block>) =
    blocks
    |> Map.tryPick
        (fun _ (Block (lab, _, _, dep)) ->
            match dep with
            | Goto dest ->
                let (Block (lab', arr, _, _)) = Map.find dest blocks

                match arr with
                | From source when source = lab -> Some(lab, lab')
                | _ -> None
            | _ -> None)

let compressTransitions links (Proc (pid, pars, locals, blocks, delocals)) =

    let rec loop blks =
        match tryFindCompressibleBlocks blks with
        | None -> blks
        | Some (parent, child) ->

            let blks' =
                mergeBlocksInDictionary parent child blks

            loop blks'

    let compressedBlockList = loop (blocks |> blockListToBlockMap)

    (Proc(pid, pars, locals, compressedBlockList |> blockMapToBlockList, delocals))



/// Remove blocks that are dead ends and fix the departure of the remaining blocks.
let rec filterOutDeadBlocks blocks =
    let blockMap = createBlockMap blocks |> removeDeadEnds

    blockMap
    |> Map.map (fun _ blk -> postProcessDeparture blk blockMap)
    |> Map.toList
    |> List.unzip
    |> snd

and removeDeadEnds (blockMap: Map<Label, Block>) =

    let rec loop label (seenBefore: Label list) =
        if List.contains label seenBefore then
            seenBefore
        else
            let seenBefore' = label :: seenBefore
            let (Block (_, arr, _, _)) = Map.find label blockMap

            match arr with
            | Entry -> seenBefore'
            | From lab -> loop lab seenBefore'
            | FiFrom (_, lab) -> loop lab seenBefore'
            | FiFromElse (_, labT, labF) -> loop labF (loop labT seenBefore')

    let exitLabel = blockMap |> getExitBlockLabel

    let labelsThatCanReachExit = loop exitLabel []

    blockMap
    |> Map.filter (fun lab _ -> List.contains lab labelsThatCanReachExit)

and getExitBlockLabel blockMap =
    match blockMap
          |> Map.filter (fun _ (Block (_, _, _, dep)) -> dep = Exit)
          |> Map.toList with
    | [] -> error $"no exit point"
    | [ (lab, _) ] -> lab
    | _ -> error "more than one exit point"


and postProcessDeparture (Block (lab, _, _, dep) as block) blockMap =
    let existOrIsExit (lab: Label) blockMap =
        lab.StartsWith "EXIT"
        || Map.containsKey lab blockMap

    match dep with
    | Exit -> block
    | Goto lab ->
        match existOrIsExit lab blockMap with
        | false -> error "destination of block {lab} does not exist"
        | true -> block
    | IfGoto (_, lab) ->
        match existOrIsExit lab blockMap with
        | false -> error "destination of block {lab} does not exist"
        | true -> block
    | IfGotoElse (e, labT, labF) ->
        match (existOrIsExit labT blockMap, existOrIsExit labF blockMap) with
        | (false, false) -> error "both destinations of block {lab} do not exist"
        | (true, false) ->
            printfn $"FIXING: lab {lab}, remove destination {labF}"
            block |> setDeparture (IfGoto(e, labT))
        | (false, true) ->
            printfn $"FIXING: lab {lab}, remove destination {labT}"
            block |> setDeparture (IfGoto(Not e, labF))
        | (true, true) -> block



let getEntryBlockLabel (blockMap: Map<Label, Block>) =
    match blockMap
          |> Map.filter (fun _ (Block (_, arr, _, _)) -> arr = Entry)
          |> Map.toList with
    | [] -> error $"no exit point"
    | [ (lab, _) ] -> lab
    | _ -> error "more than one exit point"

let reorderBlocks blocks =
    let blockMap = createBlockMap blocks
    let entryLabel = getEntryBlockLabel blockMap

    let addUnique element list =
        if List.contains element list then
            list
        else
            element :: list

    let rec loop (pending: Label list) (seenBefore: Label list) =
        match pending with
        | [] -> seenBefore
        | lab :: rest ->
            if List.contains lab seenBefore then
                loop rest seenBefore
            else
                let (Block (_, _, _, dep)) = Map.find lab blockMap

                match dep with
                | Exit -> loop rest (addUnique lab seenBefore)
                | Goto dest -> loop (rest @ [ dest ]) (addUnique lab seenBefore)
                | IfGoto (_, dest) -> loop (rest @ [ dest ]) (addUnique lab seenBefore)
                | IfGotoElse (_, destT, destF) ->
                    loop (rest @ [ destT; destF ]) (addUnique lab seenBefore)

    let orderedLabels = loop [ entryLabel ] [] |> List.rev

    orderedLabels
    |> List.map (fun label -> Map.find label blockMap)

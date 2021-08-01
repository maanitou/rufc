module SymTab

exception SymTabError of string
let error str = SymTabError str |> raise

type SymTab<'a> = SymTab of Map<string, 'a>

let empty<'a> = Map.empty<string, 'a> |> SymTab

let bind name value (SymTab tab) =
    if Map.containsKey name tab then
      error $"{name} is already defined"

    Map.add name value tab |> SymTab

let unbind name (SymTab tab) = Map.remove name tab |> SymTab

let lookup name (SymTab tab) = Map.find name tab

let tryLookup name (SymTab tab) = Map.tryFind name tab

let update name (value: 'a) (SymTab tab: SymTab<'a>) : SymTab<'a> =
    let updateFunction =
        function
        | Some _ -> Some value
        | None -> raise (SymTabError $"variable {name} is not defined yet")

    Map.change name updateFunction tab |> SymTab

let bindOrUpdate name (value: 'a) (vtab: SymTab<'a>) : SymTab<'a> =
    match tryLookup name vtab with
    | None -> bind name value vtab
    | Some _ -> update name value vtab


let ofList lst = lst |> Map.ofList |> SymTab

let toList (SymTab tab) = Map.toList tab


// Pretty print a division
let ppDiv (SymTab tab) =
    [ for (k, v) in (tab |> Map.toList) do
          $"{k}:{v}" ]
    |> String.concat "; "


/// Split a SymTab into two disjoint tabs specified by a set of keys.
let split (SymTab vtab) (keys: string list) =
    let mapKeys =
        vtab |> Map.toList |> List.map (fun (k, v) -> k)

    if keys
       |> List.exists (fun k -> not (List.contains k mapKeys)) then
        failwith "splitSymTab: second argument must be a subset of the vtab keys"

    let map1 =
        vtab
        |> Map.filter (fun k v -> List.contains k keys)

    let map2 =
        vtab
        |> Map.filter (fun k v -> not (List.contains k keys))

    (map1 |> SymTab, map2 |> SymTab)

/// Merge two disjoint SymTab.
let merge (SymTab vtab1) (SymTab vtab2) =
    let map1Keys =
        vtab1 |> Map.toList |> List.map (fun (k, v) -> k)

    let map2Keys =
        vtab2 |> Map.toList |> List.map (fun (k, v) -> k)

    if map1Keys
       |> List.exists (fun k -> List.contains k map2Keys) then
        failwith "joinSymTabs: set of keys are not disjoint"

    (vtab1, vtab2)
    ||> Map.fold (fun acc k v -> Map.add k v acc)
    |> SymTab
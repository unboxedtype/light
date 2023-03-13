// For emacs: -*- fsharp -*-

module LHTypes

open type TVM.Instruction

// built-in types
type LHType =
    | Bool
    | Int
    | String
    | List of e:LHType
    | Pair of l:LHType * r:LHType
    | UT of e:LHRecord  // union type (records)
    | ST of tag:int * args:LHTagArg list  // sum type (ADT)
and LHTagArg =
    (int * LHType)
and LHVar =
    string * LHType
and LHRecord =
    | LHRecord of tag:int * fields:LHVar list
    member this.getTag : int =
        let (LHRecord (t,_)) = this
        t
    member this.getFields =
        let (LHRecord (_,v)) = this
        v
    member this.getFieldByIndex i =
        this.getFields |> List.item i
    member this.getFieldByName (name:string) =
        this.getFieldByIndex (this.getFieldPos name)
    member this.getFieldNames =
        this.getFields |> List.map fst
    member this.getFieldPos (name:string) : int =
        this.getFieldNames
        |> List.findIndex (fun n -> n = name)

// Type scheme is a description of all record types in the program.
// It is represented as a list of mutually recursive record definitions.
// The correct scheme must contain a record with tag 0 - the State record
type LHProgramTypes =
    (string * LHRecord) list

let findLHType (typename:string) (pr:LHProgramTypes) : LHRecord =
    pr
    |> List.tryFind (fun e -> (fst e) = typename)
    |> Option.get
    |> snd

let findLHStateType (pr:LHProgramTypes) : LHRecord =
    findLHType "State" pr

// c -> a
let buildHeapValue (t:LHType) : TVM.Code =
    []

// a -> _
let insertGlobal (v:string) : TVM.Code =
    []

// s -> s' c
let getNextVarCell () : TVM.Code =
    []
// Outputs the TVM code that builds the contract state
// according to the given ProgramTypes State description.
let buildStateVar (prTypes:LHProgramTypes) : TVM.Code =
    let state = findLHStateType prTypes
    let n = state.getFields |> List.length
    state.getFields
    |> List.map (fun (name, typ) ->
                 getNextVarCell () @
                 (buildHeapValue typ) @
                 (insertGlobal name))
    |> List.concat

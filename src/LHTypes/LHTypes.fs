// For emacs: -*- fsharp -*-

// The contract  state is  defined by  corresponding State  record.  The
// State record is a set of typed variable names.

// When the  contract begins execution,  it takes  the Cell from  C4 and
// parses it according  to State record description.  For each variable,
// there  is  a  corresponding Global  variable  slot  (SETGLOB/GETGLOB)
// defined in VM. During the execution, the contract access variables by
// reading them from Globals.

// When  the  contract  execution  is  done,  the  contract  state  gets
// updated.  This is  done by  serializing globals  back into  the Cell.
// This Cell is put back in the C4.

// Each contract State variable is represented  by its own cell.  It may
// seem unoptimal at first, however,  this structure allows us to update
// the state  more effectively:  unaffected values  are taken  back from
// previuos C4 without cell rebuilding.

// Hence, we need the following algorithms and structures:

// * [StateRecord] A structure for  describing State variables and their
//   types. We consider full blown ADTs here.

// * [ReadStateRecord] An algorithm that extracts State type from the
//   program AST.
//   ReadStateRecord : AST -> StateRecord

// * [ValueFromCell] An algorithm for deserialization of a value of type
//   T from the cell.
//   ValueFromCell: Cell -> T

// * [StateGlobalsMapping]  An   algorithm  for  assinging   each  state
//   variable its  own unique  global identifier (variable  mapping). We
//   have no more than (254 - N) identifiers available for that, where N
//   is a number  of functions defined in the contract.   There might be
//   more spendings.
//   StateGlobalsMapping : StateRecord -> Map [(string, int)]

// * [ValueIntoCell] An algorithm for serialization of a value of type T
//   to a cell.
//   ValueIntoCell: T -> Cell

// * [State Init] An  algorithm to construct the C4 cell  according to a
//   given State description and a set of value cells *from scratch*.
//   StateInit : StateRecord -> [(name,valueCell)] -> Cell

// * [State Update] An algorithm for  constructing the C4 cell according
//   to a given State description, a set of new value cells and a set of
//   old value cells.
//   StateUpdate : StateRecord
//                 -> [(name,valueCell)]
//                 -> [(name,valueCell)]
//                 -> Cell

// * [State Read] An algorithm for deconstructing the C4 cell according
//   to a given State description into a set of (name, VM-native value)
//   pairs. This list may be further fed into ValuesIntoGlobals algorithm.
//   StateRead : C4 -> [(name, TVM.value)]

// * [ValueIntoGlobals]  An  algorithm  for  inserting  the  value  into
//   globals  collection with  the  given name,  according to  variable
//   mapping (see StateGlobalsMapping).
//   ValueIntoGlobals : [(name, TVM.value)] -> VariableMapping -> ()

// * [VariableUpdateAnalisys]  An   algorithm  that  takes   a  function
//   definition  as an  input and  gives a  set of  variables that  gets
//   affected by the function as an output.
//   VariableUpdateAnalisys: AST -> [name]

module Types

open type TVM.Instruction

type StateError =
    | CellUnderflow = 20

// variable identifier type
type Name =
    string

type VarName =
    Name

// built-in types
type Type =
    | Bool
    | Int of n:int
    | UInt of n:int
    | String
    | List of e:Type
    | Pair of l:Type * r:Type
    | PT of e:ProductType             // product type (records)
    | ST of e:SumType                 // sum type     (disjoint unions)
    | Function of inp:Type * out:Type // function type
and Variable =
    VarName * Type
and VariableList =
    Variable list
// TypeList is a list of name*type pairs, where name
// denotes either a type variable name, or a global type name.
// record State --> ("State", PT ([("x",List Int);("y",bool)]))
and TypeList =
    (Name * Type) list
and ProductType =  // to construct it, you shall provide all the fields
    TypeList
and SumType =      // to construct it, you shall provide only a single field
    TypeList

// Type scheme is a description of all record types in the program.
// It is represented as a list of mutually recursive record definitions.
// The correct scheme must contain a record with tag 0 - the State record
type ProgramTypes =
    TypeList

type VariablesMapping =
    Map<Name,int>

// t = PT [("x",Int);("y",List Int);("z",Bool)]
// stateGlobalsMapping t = Map [("x",1);("y",2);("z",3)]
let stateGlobalsMapping (t:ProductType) : VariablesMapping =
    let n = List.length t
    t
    |> List.map fst
    |> (fun l -> List.zip l [1..n])
    |> Map.ofList

let findType (typename:string) (pr:ProgramTypes) : Type =
    pr
    |> List.tryFind (fun e -> (fst e) = typename)
    |> Option.get
    |> snd

let findStateType (pr:ProgramTypes) : Type =
    findType "State" pr


// constructs the stack object from the cell
// corresponding to type t
// s -> v
let deserializeValue (t:Type) : TVM.Code =
    match t with
    | Int n ->
        [Ldi (uint n)]
    | UInt n ->
        [Ldu (uint n)]
    | Bool ->
        [Ldu 1u] // is it correct?
    | _ ->
        failwith "not implemented"

// b v -> b'
let serializeValue (t:Type) : TVM.Code =
    match t with
    | Int n ->
        [Sti (uint n)]
    | UInt n ->
        [Stu (uint n)]
    | Bool ->
        [Stu 1u]
    | _ ->
        failwith "not implemented"

// Construct the heap representation of the variable of type t
// residing in the given cell.
// Cell resides on the stack.
// c -> a
let valueFromCell (t:Type) : TVM.Code =
    [Ctos] @ (deserializeValue t) @ [Ends]

// Construct the cell with the variable value of type t
// Value is residing on the stack.
// v -> c
let valueToCell (t:Type) : TVM.Code =
    [Newc] @ (serializeValue t) @ [Endc]

// Put the constructed object into the global variable "v"
// The object is residing on the stack.
// a -> _
let valueIntoGlobals (v:Name) (vm: VariablesMapping) : TVM.Code =
    [SetGlob (uint vm.[v])]

// s -> s' s''
let loadNextCell () : TVM.Code =
    [LdRef; Swap] // s'' c

// s -> s' c
let switchLoadNextCell () : TVM.Code =
    [LdRef; Ends; Ctos; LdRef; Swap] // s'' c

// Outputs the TVM code that builds the contract state
// according to the given State description.
let stateRead (types:ProgramTypes) : TVM.Code =
    let statePT = findStateType types
    match statePT with
    | PT stateT ->
        let vm = stateGlobalsMapping stateT
        let n = List.length stateT
        stateT
        |> List.zip [1..n]  // [(1, (n,t)); (2, (n',t'))...]
        |> List.map (fun (i, (name, typ)) ->
                     (if (i % 4 = 0) then switchLoadNextCell ()
                      else loadNextCell ()) @
                     (valueFromCell typ) @
                     valueIntoGlobals name vm)
        |> List.concat
        |> List.append [PushCtr 7u; Ctos] // Cell with the State
    | _ ->
        failwith "State shall be a Product type"

let testStateRead0 () =
    let types = [("State", PT ([("x", (Int 256));("y", Bool)]))]
    let code = stateRead types
    printfn "%A" code
    // let c4 = encodeC4
    // let init = initialState code
    // let final = runVMWithC4 c4 init

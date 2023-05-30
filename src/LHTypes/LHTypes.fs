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

// Hence, we need the following algorithms and structures:

// * [StateRecord] A structure for  describing State variables and their
//   types. We consider full blown ADTs here.

// * [ReadStateRecord] An algorithm that extracts State type from the
//   program AST.
//   ReadStateRecord : AST -> StateRecord

// * [deserializeValue] An algorithm for deserialization of a value of type
//   T from the slice.

// * [StateGlobalsMapping]  An   algorithm  for  assinging   each  state
//   variable its  own unique  global identifier (variable  mapping).
//   StateGlobalsMapping : StateRecord -> Map [(string, int)]

// * [serializeValue] An algorithm for serialization of a value of type T
//   into a slice.

// * [State Reader] An algorithm for deconstructing the C4 cell according
//   to a given State description into a set of (name, VM-native value)
//   pairs. This list may be further fed into ValuesIntoGlobals algorithm.
//   StateWrite : StateRecord -> Cell -> [(name, TVM.value)]

// * [State Writer] An algorithm for constructing the C4 cell according
//   to a given State description. New variable values are taken from
//   the 'state' variable. They get serialized and placed into a cell according to
//   the chosen data placement structure.

module LHTypes

open type TVM.Instruction

type StateError =
    | CellUnderflow = 20

// variable identifier type
type Name =
    string

type VarName =
    Name

// Type id is a unique type identifier; built-in
// types have it defined initially, and user
// data types are assigned their own typeid
// during the compilation.
type TypeId =
    int

// Basic types:
// Unit        = 0001
// Bool        = 0010
// UInt        = 0100
// String      = 1000

// Compound types:
// List<Int>.Cons     = 1001
// List<Int>.Nil      = 1011
// Map<T1,T2>         = 1100
// Function<T1,T2>    = 1101

type Type =
    | Unit
    | Bool
    | Int of n:int    // n = bit length; 1 <= n <= 256
    | UInt of n:int   // n = bit length  1 <= n <= 256
    | String
    | PT of e:ProductType               // product type
    | ST of e:SumType                   // sum type
    | Function of inp:Type * out:Type   // function type
    | UserType of name:Name * typ:option<Type>  // user-defined type with name s
    | TVar of s:Name // type variable
    member this.usertypeName =
        match this with
            | UserType (s, _) -> s
            | _ -> failwith "not a UserType type"

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
    (Name * (Type list)) list

// Type scheme is a description of all record types in the program.
// It is represented as a list of mutually recursive record definitions.
// The correct scheme must contain a record with tag 0 - the State record
type ProgramTypes =
    TypeList

type VariablesMapping =
    Map<Name,int>

// map an LH elementary type into Type
let mapType (str : string) : Type =
    match str with
    | "int" -> Int 256
    | "string" -> String
    | "bool" -> Int 2
    | "unit" -> Unit
    | S -> UserType (S, None)
    // | _ -> failwith (str + " is not supported currently")

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
    let t = findType "state" pr
    match t with
    | UserType ("State", Some typ) ->
        typ
    | _ ->
        failwithf "Unexpected state type %A" t


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
        [Ldu 2u] // is it correct?
    | Function (_, _) ->
        [LdRef; Swap; Ctos; Bless; Swap]
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
        [Stu 2u]
    | Function (_, _) ->
        // TODO: temporal stub not to fail tests
        // Has to be changed for proper function serialization.
        [Pop 1u; Newc; Endc; Swap; StRef]
    | _ ->
        failwith "not implemented"

// Outputs the TVM code that builds the contract state
// according to the given State description.
let stateReader (types:ProgramTypes) : TVM.Code =
    let statePT = findStateType types
    match statePT with
    | PT stateT ->
        let n = List.length stateT
        stateT
        |> List.map (fun (name, typ) -> deserializeValue typ)
        |> List.concat
        |> List.append [PushCtr 4u; Ctos] // Cell with the State
        |> (fun l -> List.append l [Ends; Tuple (uint n); PushInt 0; Swap; Tuple 2u])
    | _ ->
        failwith "State shall be a Product type"

// Outputs the TVM code that assembles the C4 cell from the
// given state variable values located on the stack. State is
// encoded according to the given State description.
let stateWriter (types:ProgramTypes) : TVM.Code =
    // this function generates a pairs of swaps needed
    // to reverse the list l. The acc is an accumulator (state)
    // TODO!!: Use REVERSE instruction for that.
    let rec xchgs l acc =
        let len = List.length l
        if len > 1 then
            let (s,e) = (List.head l, List.last l)
            let next = List.take (len-2) (List.tail l)
            xchgs next ((s,e) :: acc)
        else
            acc
    let statePT = findStateType types
    match statePT with
    | PT stateT ->
        let n = List.length stateT
        stateT
        |> List.map (fun (name, typ) -> serializeValue typ)
        |> List.concat
        |> List.append ([GetGlob 2u; Second; Untuple (uint n)] @
                        (let pairs = xchgs [0..(n-1)] []
                         [for (i,j) in pairs -> Xchg2 (uint i, uint j)]) @ [Newc])
        |> (fun l -> List.append l [Endc; PopCtr 4u])
    | _ ->
        failwith "State shall be a Product type"

// Find all partially defined types within the type term 't'.
let rec hasUndefType (t:Type) : List<Name> =
    match t with
    | UserType (name, None) ->
        List.singleton name
    | UserType (name, Some t) ->
        hasUndefType t
    | PT pts ->
        pts
        |> List.map snd
        |> List.map hasUndefType
        |> List.concat
    | ST sts ->
        sts
        |> List.map snd
        |> List.concat
        |> List.map hasUndefType
        |> List.concat
    | _ ->
        // TODO: what about Function?
        []

// substitute type name with the given definition def
// in the type t
let rec insertType (name:Name) (typDefs:ProgramTypes) (expr:Type) : Type =
    match expr with
    | UserType (name1, None) when name1 = name ->
        let def = (Map.ofList typDefs).[name1] in
        UserType (name1, Some def)
    | UserType (name1, Some t) ->
        UserType (name1, Some (insertType name typDefs t))
    | PT pts ->
        PT (pts
            |> List.map (fun (name1, t) ->
                         (name1, insertType name typDefs t) ))
    | ST sts ->
        ST (sts
            |> List.map (fun (name1, ts) ->
                         (name1, List.map (insertType name typDefs) ts)))
    | _ ->
        // TODO: what about Function?
        expr

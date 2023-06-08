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

// variable identifier type
type Name =
    string

type VarName =
    Name

type Type =
    | Unit
    | Bool
    | VMCell
    | VMSlice
    | Coins
    | Int of n:int    // n = bit length; 1 <= n <= 256
    | UInt of n:int   // n = bit length  1 <= n <= 256
    | String
    | PT of e:ProductType               // product type
    | ST of e:SumType                   // sum type
    | UserType of name:Name * typ:option<Type>  // user-defined type with name s
    | Function of inp:Type * out:Type   // function type
    | TVar of s:Name // type variable
    member this.usertypeName =
        match this with
        | UserType (s, _) -> s
        | _ -> failwith "not a UserType type"
    member this.baseType =
        match this with
        | UserType (_, None) ->
            failwithf "baseType not defined for %A" this
        | UserType (_, Some t) ->
            t.baseType
        | _ ->
            this

and Variable =
    VarName * Type
and VariableList =
    List<Variable>
// TypeList is a list of name*type pairs, where name
// denotes either a type variable name, or a global type name.
// record State --> ("State", PT ([("x",List Int);("y",bool)]))
and TypeList =
    List<Name * Type>
and ProductType =  // to construct it, you shall provide all the fields
    TypeList
and SumType =      // to construct it, you shall provide all args to a single constructor
    List<Name * List<Type>>

// Type scheme is a description of all record types in the program.
// It is represented as a list of mutually recursive record definitions.
// The correct scheme must contain a record with tag 0 - the State record
type ProgramTypes =
    TypeList

type VariablesMapping =
    Map<Name,int>

// map an LH elementary type into Type
let mapType (str : string) : option<Type> =
    match str with
    | "int" -> Some (Int 256)
    | "string" -> Some String
    | "bool" -> Some Bool
    | "VMCell" -> Some VMCell
    | "VMSlice" -> Some VMSlice
    | "Coins" -> Some Coins
    | "unit" -> Some Unit

    // TODO!! This is a temporary hack, not to mess with function types right now.
    | "fun:int->int" -> Some (Function (Int 256, Int 256))
    | "fun:int->fun:int->int" -> Some (Function (Int 256, Function (Int 256, Int 256)))
    | "fun:VMCell->fun:State->VMCell" -> Some (Function (VMCell, Function (UserType ("State", None), VMCell)))

    | "" -> None
    | S -> Some (UserType (S, None))
    | _ -> failwithf "Undefined type %s" str


// constructs the stack object from the cell
// corresponding to type t
// s -> v
let deserializeValue (ty:TypeList) (t:Type) : string =
    let rec deserializeValueInner ty t : string =
        match t with
        | Int n ->
            sprintf "%i LDI" n
        | UInt n ->
            sprintf "%i LDU" n
        | Bool ->
            sprintf "2 LDI"
        | PT fields ->
            let n = List.length fields
            List.map snd fields // [t1; t2; ...]
            |> List.map (deserializeValueInner ty)  // [str; str; str]
            |> String.concat " "
            // v1 v2 .. vn s --> s v1 v2 .. vn --> s (v1 .. vn)
            // --> (v1 .. vn) s
            |> (fun s -> s + sprintf " %i ROLLREV %i TUPLE SWAP " n n)
        | Function (_, _) ->
            "LDREFRTOS x{D766} s, ENDS SWAP"   // D766 = LDCONT
        | UserType (n, Some t) ->
            deserializeValueInner ty t
        | _ ->
            failwithf "Parsing for type %A not implemented" t
    "CTOS " + (deserializeValueInner ty t) + " ENDS  "
// v b -> b'
let serializeValue (ty:TypeList) (t:Type) : string =
    let rec serializeValueInner ty t : string =
        match t with
        | Int n ->
            sprintf "%i STI" n
        | UInt n ->
            sprintf "%i STU" n
        | Bool ->
            sprintf "2 STI"
        | PT fields ->
            let n = List.length fields
            " SWAP " +
            (sprintf " %i UNTUPLE " n) +    // b [v1; v2; ... vn] --> b v1 v2 .. vn
            (sprintf " %i 0 REVERSE " (n+1)) +    // vn ... v1 b
            (List.map snd fields // [t1; t2; ...]
             |> List.map (serializeValueInner ty)  // [str; str; str]
             |> String.concat " ") // ... -> b'
        | UserType (n, Some t) ->
            serializeValueInner ty t
        | Function _ ->
            // cont b -> b cont
            // -> b cont b
            // -> b c
            // -> c b
            // -> b''
            "SWAP NEWC x{CF43} s, ENDC SWAP STREF"   // STCONT mnemonics; otherwise,
        | _ ->
            failwith "not implemented"
    "NEWC " + serializeValueInner ty t + " ENDC "
// substitute type name with the given definition def
// in the type t
let rec insertType (name:Name) (typDefs:ProgramTypes) (expr:Type) : Type =
    match expr with
    | UserType (name1, None) when name1 = name ->
        let def = Map.tryFind name1 (Map.ofList typDefs) in
        match def with
        | Some def' ->
            UserType (name1, Some def')
        | None ->
            failwithf "Definition for the type %A not found" name1
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

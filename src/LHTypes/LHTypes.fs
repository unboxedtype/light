// For emacs: -*- fsharp -*-

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
    | Tuple of list<Type>
    | Record of list<Name*Type>
     // ADT = Algebraic Data Type
     // Each constructor has a name.
     // Contructors may have zero or more arguments.
    | ADT of list<Name*option<Type>>  // ADT
    | UserType of Name*option<Type>   // alias for some other type
    | Function of Type*Type   // function type
    | TVar of s:Name // type variable; needed for type inference
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
// type State --> ("State", Record [("x",List Int);("y",bool)])
and TypeList =
    List<Name * Type>

// Type scheme is a description of all record types in the program.
// It is represented as a list of mutually recursive record definitions.
// The correct scheme must contain a record with tag 0 - the State record
type ProgramTypes = TypeList
type VariablesMapping = Map<Name,int>

// constructs the stack object from the slice
// corresponding to type t
let rec deserializeValueSlice ty t : string =
    match t with
    | Int n ->
        sprintf "%i LDI" n
    | UInt n ->
        sprintf "%i LDU" n
    | Bool ->
        sprintf "2 LDI"
    | Record fields ->
        let n = List.length fields
        List.map snd fields // [t1; t2; ...]
        |> List.map (deserializeValueSlice ty)  // [str; str; str]
        |> String.concat " "
        // v1 v2 .. vn s --> s v1 v2 .. vn --> s (v1 .. vn)
        // --> (v1 .. vn) s
        |> (fun s -> s + sprintf " %i ROLLREV %i TUPLE SWAP " n n)
    | Function (_, _) ->
        "LDREFRTOS x{D766} s, ENDS SWAP"   // D766 = LDCONT
    | UserType (n, Some t) ->
        deserializeValueSlice ty t
    | _ ->
        failwithf "Parsing for type %A not implemented" t

// constructs the stack object from the cell
// corresponding to type t
// s -> v
let deserializeValue (ty:TypeList) (t:Type) : string =
    "CTOS " + (deserializeValueSlice ty t) + " ENDS  "

// Same as deserializeValue, but do not try to deserialize continuations,
// just put an empty cont on the stack in this case.
let deserializeValueSimpl (ty:TypeList) (t:Type) : string =
    let rec deserializeValueInner ty t : string =
        match t with
        | Int n ->
            sprintf "%i LDI" n
        | UInt n ->
            sprintf "%i LDU" n
        | Bool ->
            sprintf "2 LDI"
        | Record fields ->
            let n = List.length fields
            List.map snd fields // [t1; t2; ...]
            |> List.map (deserializeValueInner ty)  // [str; str; str]
            |> String.concat " "
            // v1 v2 .. vn s --> s v1 v2 .. vn --> s (v1 .. vn)
            // --> (v1 .. vn) s
            // |> (fun s -> s + sprintf " %i ROLLREV %i TUPLE SWAP " n n)
        | Function (_, _) ->
            "LDREF NIP <{ }> PUSHCONT SWAP"   // empty push cont
        | UserType (n, Some t) ->
            deserializeValueSlice ty t
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
        | Record fields ->
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
            "SWAP NEWC x{CF43} s, ENDC SWAP STREF"   // CF43 = STCONT
        | _ ->
            failwith "not implemented"
    "NEWC " + serializeValueInner ty t + " ENDC "
// substitute type name with the given definition def
// in the type t
let rec insertType (name:Name) (typDefs:ProgramTypes) (expr:Type) : Type =
    match expr with
    | Tuple ts ->
        ts
        |> List.map (insertType name typDefs)
        |> Tuple
    | UserType (name1, None) when name1 = name ->
        let def = Map.tryFind name1 (Map.ofList typDefs) in
        match def with
        | Some def' ->
            UserType (name1, Some def')
        | None ->
            failwithf "Definition for the type %A not found" name1
    | UserType (name1, Some t) ->
        UserType (name1, Some (insertType name typDefs t))
    | Record pts ->
        pts
        |> List.map (fun (name1, t) ->
                    (name1, insertType name typDefs t))
        |> Record
    | ADT sts ->
        sts
        |> List.map ( fun (ctorName, ctorArgOpt) ->
                      match ctorArgOpt with
                      | None -> (ctorName, None)
                      | Some t -> (ctorName, Some (insertType name typDefs t))
                    )
        |> ADT
    | _ ->
        // TODO: what about Function?
        expr

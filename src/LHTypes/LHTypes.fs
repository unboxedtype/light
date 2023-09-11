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
let rec deserializeValueSlice ty t : list<TVM.Instruction> =
    match t with
    | Int n ->
        [TVM.Ldi n] // sprintf "%i LDI" n
    | UInt n ->
        [TVM.Ldu n] // sprintf "%i LDU" n
    | Bool ->
        [TVM.Ldi 2] // sprintf "2 LDI"
    | Record fields ->
        let n = List.length fields
        (List.map snd fields // [t1; t2; ...]
        |> List.map (deserializeValueSlice ty)  // [str; str; str]
        |> List.concat) 
        @ [TVM.RollRev n; TVM.Tuple n; TVM.Swap]
    | Function (_, _) ->
        [TVM.LdRefRtos;
         TVM.LdCont;
         TVM.Ends;
         TVM.Swap]
    | UserType (n, Some t) ->
        deserializeValueSlice ty t
    | Unit ->
        [TVM.LdRef; TVM.Nip; TVM.PushNull; TVM.Swap]
        // [TVM.SkipOptRef; TVM.PushNull; TVM.Swap]
    | _ ->
        failwithf "Parsing for type %A not implemented" t

// constructs the stack object from the cell
// corresponding to type t
// s -> v
let deserializeValue (ty:TypeList) (t:Type) : list<TVM.Instruction> =
    [TVM.Ctos] @ (deserializeValueSlice ty t) @ [TVM.Ends]

// Same as deserializeValue, but do not try to deserialize continuations,
// just put an empty cont on the stack in this case.
let deserializeValueSimpl (ty:TypeList) (t:Type) : list<TVM.Instruction> =
    let rec deserializeValueInner ty t : list<TVM.Instruction> =
        match t with
        | Int n ->
            [TVM.Ldi n]  // sprintf "%i LDI" n
        | UInt n ->
            [TVM.Ldu n]  // sprintf "%i LDU" n
        | Bool ->
            [TVM.Ldi 2]  // sprintf "2 LDI"
        | Record fields ->
            let n = List.length fields
            (List.map snd fields // [t1; t2; ...]
            |> List.map (deserializeValueInner ty)  // [str; str; str]
            |> List.concat)
            @ [TVM.RollRev n; TVM.Tuple n; TVM.Swap]
        | Function (_, _) ->
            [TVM.LdRef; TVM.Nip; TVM.PushCont []; TVM.Swap]
        | UserType (n, Some t) ->
            deserializeValueInner ty t
        | Unit ->
            [TVM.LdRef; TVM.Nip; TVM.PushNull; TVM.Swap]
        | _ ->
            failwithf "Parsing for type %A not implemented" t
    [TVM.Ctos] @ (deserializeValueInner ty t) @ [TVM.Ends]

// v b -> b'
let serializeValue (ty:TypeList) (t:Type) : list<TVM.Instruction> =
    let rec serializeValueInner ty t : list<TVM.Instruction> =
        match t with
        | Int n ->
            [TVM.Sti n] // sprintf "%i STI" n
        | UInt n ->
            [TVM.Stu n] // sprintf "%i STU" n
        | Bool ->
            [TVM.Sti 2] // sprintf "2 STI"
        | Record fields ->
            let n = List.length fields
            [TVM.Swap;
             TVM.Untuple n;
             TVM.Reverse (n+1, 0)] @
            (List.map snd fields // [t1; t2; ...]
             |> List.map (serializeValueInner ty)
             |> List.concat)
             // ... -> b'
        | UserType (n, Some t) ->
            serializeValueInner ty t
        | Function _ ->
            // cont b -> b cont
            // -> b cont b
            // -> b c
            // -> c b
            // -> b''
            [TVM.Swap;
             TVM.Newc;
             TVM.StCont;
             TVM.Endc;
             TVM.Swap;
             TVM.StRef]
        | Unit ->
            [TVM.Newc;
             TVM.Endc;
             TVM.Swap;
             TVM.StRef] (* empty cell will be put *)
        | _ ->
            failwith "not implemented"
    [TVM.Newc] @ (serializeValueInner ty t) @ [TVM.Endc]
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

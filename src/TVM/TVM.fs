module TVM

// Incomplete pattern matches on this expression.
#nowarn "25"

open System
open System.Collections.Generic

exception TVMError of string

// codepage number is an unsigned integer
type CodePage =
    int

type Action =
    | SendMsg
    | Reserve

type Instruction =
    | CondSel
    | DumpHeap          // this is artificial instruction.
    | PrintStr of s:string
    | Push of n:int
    | PushRef of c:SValue list
    | Dup               // Push 0 alias
    | Pop of n:int
    | Drop              // Pop 0 alias
    | BlkDrop of n:int
    | DropX
    | Xchg of i:int      // Xchg s0, s(i)
    | Xchg2 of int * int // Xchg s(i),s(j)
    | Swap               // Xchg 0 alias
    | Swap2              // a b c d -> c d a b
    | Greater
    | Less
    | GetGlob of k:int   // 1 <= k <= 31
    | SetGlob of k:int   // 1 <= k <= 31
    | PushInt of n:int
    | PushCont of c:Code // this should also be int8 list, but for now..
    | PushCtr of n:int
    | PopCtr of n:int
    | IfElse
    | IfRet
    | Inc
    | Add
    | Sub
    | Mul
    | Div
    | DivMod
    | Execute
    | CallDict of n:int
    | JmpX
    | DictUGetJmp
    | DumpStk
    | Nop
    | Tuple of n:int
    | TLen
    | TupleVar
    | UntupleVar
    | Nil
    | PushNull
    | Second
    | Third
    | Index of k:int
    | IndexVar
    | IndexVarQ
    | Untuple of n:int
    | SetIndex of k:int
    | SetIndexVar
    | SetIndexVarQ
    | TPush
    | Newc
    | Endc
    | Sti of cc:int
    | Ldi of cc:int
    | LdDict
    | Ends
    | StRef
    | NewDict    // ... -> ... D
    | DictIGet   // i D n -> x (-1),  or 0
    | DictISetB  // b i D n -> D'
    | ThrowIfNot of nn:int
    | ThrowIf of nn:int
    | Throw of nn:int
    | Equal
    | IfExec     // If
    | IfJmp
    | Ret
    | SetNumArgs of n:int
    | RollRev of n:int
    | RollRevX
    | Roll of n:int
    | Repeat
    | Depth
    | Dec
    | Pick   // PushX
    | XchgX
    | PushSlice of s:SValue list
    | StSlice
    | IsNull
    | IsZero
    | Dup2
    | Rot
    | Rot2
    | RotRev
    | Bless
and Code =
    Instruction list
and Value =  // stack value types
    | Int of v:int
    | Tup of vs:Value list
    | Null
    | Cont of v:Continuation
    | Builder of vs:SValue list
    | Cell of vs:SValue list
    | Slice of vs:SValue list
    member this.unboxCont =
        match this with | Cont x -> x | _ -> failwith "Cont expected"
    member this.unboxTup : Value list =
        match this with | Tup x -> x | _ -> failwith "Tup expected"
    member this.asSV : SValue =
        match this with
        | Int n -> SInt n
        | Cont c -> SCode (c.code)
        | Cell s -> SCell s
        | _ -> failwith "not serializable"
    member this.unboxInt =
        match this with | Int x -> x | _ -> failwith "Int expected"
    member this.unboxBuilder = match this with | Builder x -> x | _ -> failwith "Builder expected"
    member this.unboxSlice = match this with | Slice vs -> vs | _ -> failwith "Slice expected"
    member this.unboxCell = match this with | Cell x -> x | _ -> failwith "Cell expected"
    member this.isInt = match this with | Int _ -> true | _ -> false
    member this.isCont = match this with | Cont _ -> true | _ -> false
    member this.isTuple = match this with | Tup _ -> true | _ -> false
    member this.isCell = match this with | Cell _ -> true | _ -> false
    member this.isSlice = match this with | Slice _ -> true | _ -> false
    member this.isNull = match this with | Null -> true | _ -> false
    member this.isBuilder =
        match this with
            | Builder _ -> true
            | _ -> false
    member this.packCell =
        match this with
            | Builder vs -> Cell vs
            | _ -> failwith "packCell expects Builder"
    member this.unpackCell =
        match this with
            | Cell vs -> vs
            | _ -> failwith "unpackCell expects Cell"
and SValue =  // Serializable Value
// Dictionary value type is Cell because there may be several SValues
// chained together. SValue would have been not adequate enough.
    | SDict of v:Map<int,SValue list>  // dictionary is able to store only SValue
    | SCode of c:Code
    | SInt of n:int
    | SCell of c:SValue list   // c is a cell
    static member isSDict = function | SDict _ -> true | _ -> false
    static member isSCode = function | SCode _ -> true | _ -> false

and ControlData =
    { mutable stack: Stack
      mutable save: ControlRegs
      mutable nargs: int }
    static member Default = {
        stack = []; save = ControlRegs.Default; nargs = -1
    }
and ControlRegs =
    { mutable c0:Continuation option;
      mutable c3:Continuation option;
      mutable c7:Value } // it should be tuple all the time
    static member Default = {
        c0 = None; c3 = None; c7 = Tup []
    }
and Continuation =
    { mutable code:Code;
      mutable data:ControlData }
    static member Default = {
        code = []; data = ControlData.Default;
    }
    static member ContQuit = {
        code = []; data = ControlData.Default;
    }
and Stack =
    Value list

let TVM_True = (Int -1)
let TVM_False = (Int 0)

let isOverflow n =
    // skip the test for now
    false

let failIfNot b str =
    if (not b) then
        failwith str
    else
        ()

let failIf b str =
    failIfNot (not b) str

let emptyTuple = []
let emptyContinuation = Continuation.Default

type TVMState =
    { mutable code:Code;
      mutable stack:Stack;
      mutable cr:ControlRegs; }
    static member Default = {
        code = []; stack = []; cr = ControlRegs.Default }
    member this.preclear_cr (save:ControlRegs) =
        if save.c0.IsSome then this.cr.c0 <- None else ()
        if save.c3.IsSome then this.cr.c3 <- None else ()
    member this.adjust_cr regs =
        this.cr.c0 <- if regs.c0.IsSome then regs.c0 else this.cr.c0
        this.cr.c3 <- if regs.c3.IsSome then regs.c3 else this.cr.c0
    member this.put_code code =
        this.code <- code
    member this.put_stack stk =
        this.stack <- stk
    member this.put_c7 c7 =
        this.cr.c7 <- c7

// do the ordinary jump into continuation cont
let switch_to_cont cont (st:TVMState) =
    st.adjust_cr cont.data.save
    st.put_code cont.code
    st

let jump_to cont (st:TVMState) =
    switch_to_cont cont st

// general jump to continuation cont
let jump_ext cont pass_args st =
    let depth = st.stack.Length
    if (pass_args > depth) || (cont.data.nargs > depth) then
        raise (TVMError "stack underflow while jumping to a continuation: not enough args on stack")
    elif (cont.data.nargs > pass_args && pass_args >= 0) then
        raise (TVMError "stack underflow while jumping to closure cont: not enough args passed")
    st.preclear_cr cont.data.save
    let mutable copy = cont.data.nargs
    if pass_args >= 0 && copy < 0 then
        copy <- pass_args
    else
        ()
    if cont.data.stack <> [] then
        if copy < 0 then
            copy <- st.stack.Length
        else
            ()
        let mutable new_stk = (List.take copy st.stack) @ cont.data.stack
        st.put_stack new_stk
    else
        if (copy >= 0) && (copy < st.stack.Length) then
            st.put_stack (List.take copy st.stack)
        else
            ()
    jump_to cont st

// simple jump to continuation cont
let jump cont (st:TVMState) =
    if (cont.data.stack <> []) || (cont.data.nargs >= 0) then
        jump_ext cont -1 st         // the stack needs to be adjusted before the CC switch
    else
        switch_to_cont cont st      // do the CC switch immediately

let call_ext cont (pass_args:int) (ret_args:int) (st:TVMState) =
    if cont.data.save.c0.IsSome then
        jump_ext cont pass_args st
    else
        let depth = st.stack.Length
        if (pass_args > depth) || (cont.data.nargs > depth) then
            raise (TVMError "stack underflow while calling a continuation: not enough args on stack")
        elif (cont.data.nargs > pass_args) && (pass_args >= 0) then
            raise (TVMError "stack underflow while calling a closure continuation: not enough arguments passed")
        let old_c0 = st.cr.c0
        st.preclear_cr cont.data.save
        let mutable copy = cont.data.nargs
        let mutable skip = 0
        if pass_args >=0 then
            if copy >= 0 then
                skip <- pass_args - copy
            else
                copy <- pass_args
        else
            ()
        let mutable new_stk = []
        if cont.data.stack <> [] then
            if copy < 0 then
                copy <- st.stack.Length
            else
                ()
            new_stk <- (List.take copy st.stack) @ cont.data.stack
            if skip > 0 then
                st.put_stack (List.skip skip st.stack)
        elif copy >= 0 then
            new_stk <- List.take copy st.stack
            st.put_stack (List.skip copy st.stack)
            st.put_stack (List.skip skip st.stack)
        else
            new_stk <- st.stack
            st.put_stack []
        let ret = { code = st.code; data = { ControlData.Default with stack = st.stack; nargs = ret_args } }
        ret.data.save.c0 <- old_c0
        st.put_stack new_stk
        st.cr.c0 <- Some ret
        jump_to cont st

let call cont (st:TVMState) =
    if cont.data.save.c0.IsSome then
        jump cont st
    elif (cont.data.stack <> [] || cont.data.nargs >= 0) then
        call_ext cont -1 -1 st
    else
        let ret = { code = st.code; data = ControlData.Default }
        ret.data.save.c0 <- st.cr.c0
        st.cr.c0 <- Some ret
        jump_to cont st

// RET instruction handler
// Transfer control to c0 continuation
let ret st =
    let c0 = st.cr.c0
    match c0 with
        | Some c ->
            st.cr.c0 <- None
            jump c st
        | None ->
            st

let initialState (code:Code) : TVMState =
    let st = { code = code; stack = []; cr = {ControlRegs.Default with c0 = Some Continuation.ContQuit } }
    st

let mkBuilder (vs:SValue list) =
    Builder vs

let mkCell (b:Value) : Value =
    failIfNot (b.isBuilder) "not a builder"
    Cell b.unboxBuilder

let sti cc st =
    let (b :: x :: stack') = st.stack
    failIfNot (b.isBuilder) "STI: not a builder"
    failIfNot (x.isInt) "STI: not an integer"
    let vs = b.unboxBuilder
    // failIf (x > float 2 ** cc) "STU: Range check exception"
    st.put_stack (mkBuilder (vs @ [x.asSV]) :: stack')
    st

let ldi cc st =
    let (s :: stack') = st.stack
    failIfNot (s.isSlice) "LDI: slice expected"
    let (Slice (SInt n :: t)) = s
    let logBase b v = (log v) / (log b)
    failIf (logBase 2.0 (float n) > cc) "not enough bits for the integer"
    // check n-th size against cc
    st.put_stack (Slice t :: Int n :: stack')
    st

let ends st =
    let (Slice t :: stack') = st.stack
    failIfNot (t = []) "ENDS: slice not empty"
    st.put_stack stack'
    st

let newc st =
    let stack = st.stack
    st.put_stack (mkBuilder [] :: stack)
    st

let endc st =
    let (b :: stack) = st.stack
    failIfNot (b.isBuilder) "ENDC: not a builder"
    st.stack <- (mkCell b) :: stack
    st

let execute st =
    failIf (List.length st.stack < 1) "EXECUTE: stack underflow"
    let (cont :: stack') = st.stack
    st.stack <- stack'
    call cont.unboxCont st

let pushcont c st =
    let stack' = st.stack
    let cont = { Continuation.Default with code = c }
    st.stack <- (Cont cont) :: stack'
    st

let pushint n st =
    let stack' = st.stack
    st.stack <- (Int n) :: stack'
    st

let pushnull st =
    let stack' = st.stack
    st.stack <- Null :: stack'
    st

let pushslice (c:SValue list) st =
    st.stack <- (Slice c) :: st.stack
    st

let stslice st =
    let (b :: s :: stack') = st.stack
    failIfNot (b.isBuilder) "STSLICE: builder expected"
    failIfNot (s.isSlice) "STSLICE: slice expected"
    st.stack <- Builder (s.unboxSlice @ b.unboxBuilder) :: stack'
    st

let isnull st =
    let (x :: stack') = st.stack
    if x.isNull then
        st.stack <- (Int -1) :: stack'
    else
        st.stack <- (Int 0) :: stack'
    st

let iszero st =
    let (x :: stack') = st.stack
    if x = (Int 0) then
        st.stack <- (Int -1) :: stack'
    else
        st.stack <- (Int 0) :: stack'
    st

let push n st =
    let stack' = st.stack
    failIf (n < 0) "PUSH: type check error"
    failIf (List.length stack' <= n) "PUSH: stack underflow"
    let sn = stack'.Item n
    st.stack <- sn :: stack'
    st

let pushctr n st =
    let stack =
        if n = 7 then
            failIfNot (st.cr.c7.isTuple) "PUSHCTR: C7 is a tuple"
            st.cr.c7 :: st.stack
        elif n = 3 then
            if st.cr.c3.IsSome then
                (Cont st.cr.c3.Value) :: st.stack
            else
                raise (TVMError "PUSHCTR: Register c3 is not initialized")
        elif n = 0 then
            if st.cr.c0.IsSome then
                (Cont st.cr.c0.Value) :: st.stack
            else
                failwith "C0 is not initialized (but should be?)"
        else
            raise (TVMError "PUSHCTR: only c0,c3,c7 are supported")
    st.stack <- stack
    st

let popctr n st =
    failIf (n <> 7 && n <> 3) "POPCTR: only c3 and c7 are supported"
    if n = 7 then
        let (c7 :: stack) = st.stack
        failIfNot (c7.isTuple) "POPCTR: c7 is a tuple"
        st.stack <- stack
        st.cr.c7 <- c7
    else
        let (c3 :: stack) = st.stack
        failIfNot (c3.isCont) "POPCTR: c3 is a continuation"
        st.stack <- stack
        st.cr.c3 <- Some c3.unboxCont
    st

let pop n st =
    let (a :: stack') = st.stack
    if n > 0 then
        st.put_stack (List.updateAt (n-1) a stack')
    else
        st.put_stack stack'
    st

let xchg2 i j st =
    failIf (List.length st.stack <= i) "XCHG: Stack underflow"
    failIf (List.length st.stack <= j) "XCHG: Stack underflow"
    let stk = List.toArray st.stack
    let si = stk.[i]
    let sj = stk.[j]
    let tmp = stk.[j]
    let stack' =
       Array.updateAt j si stk  // s[j] := s[i]
       |> Array.updateAt i tmp // s[i] := old s[j]
       |> Array.toList
    st.stack <- stack'
    st

let xchg n st =
    xchg2 0 n st

let swap2 st =
    let (d :: c :: b :: a :: stack) = st.stack
    st.put_stack (b :: a :: d :: c :: stack)
    st

let True = -1
let False = 0

let ifelse st =
    let (fb :: tb :: f :: stack') = st.stack
    failIfNot (f.isInt) "IfElse: stack item must be integer"
    failIfNot (tb.isCont) "IfElse: stack item must be continuation"
    failIfNot (fb.isCont) "IfElse: stack item must be continuation"
    let (Cont true_branch_cont) = tb
    let (Cont false_branch_cont) = fb
    let code' =
        if f = TVM_True then
            st.code @ true_branch_cont.code
        else
            st.code @ false_branch_cont.code
    st.code <- code'
    st.stack <- stack'
    st

let binop f st =
    let (a2 :: a1 :: stack') = st.stack
    failIfNot (a1.isInt) "binop: stack item must be integer"
    failIfNot (a2.isInt) "binop: stack item must be integer"
    let (Int v1, Int v2) = (a1, a2)
    let res = f v1 v2
    st.stack <- (Int res) :: stack'
    st

let sub v1 v2 =
    v1 - v2

let add v1 v2 =
    v1 + v2

let mul v1 v2 =
    v1 * v2

let div v1 v2 =
    v1 / v2

let gt v1 v2 =
    if v1 > v2 then -1 else 0

let lt v1 v2 =
    if v1 < v2 then -1 else 0

let equal v1 v2 =
    if v1 = v2 then -1 else 0

let inc st =
    let (a1 :: stack') = st.stack
    failIfNot (a1.isInt) "INC: stack item must be integer"
    // TODO: overflow check
    st.stack <- Int (a1.unboxInt + 1) :: stack'
    st

let dumpstk trace st =
    let stk = st.stack
    if trace then
        printfn "STACK: %A"  stk
    else
        ()
    st

let nop st =
    st

let tuple n (is_stack:bool) st =
    let stk = st.stack
    failIf (n < 0) "TUPLE: incorrect argument"
    if (not is_stack) then
        failIf (n > 15) "TUPLE: incorrect argument"
    else
        failIf (n > 254) "TUPLE: range check error"
    failIf (List.length stk < n) "TUPLE: Stack underflow"
    let args = List.rev (List.take n stk)
    let t = Tup args
    st.stack <- t :: (List.skip n stk)
    st

let untuple n st =
    let (Tup v :: stack') = st.stack
    failIf (List.length v <> n) "INDEX: Type check exception"
    st.stack <- v @ stack'
    st

let nil st =
    tuple 0 false st

// TPUSH (t x – t')
let tpush st =
    let (x :: (Tup ut) :: stack) = st.stack
    failIf (List.length ut = 255) "TPUSH: Type check exception"
    st.stack <- Tup (x :: ut) :: stack
    st

// INDEX k (t - t[k]), 0 <= k <= 15
let index k st =
    let (t :: stack') = st.stack
    failIfNot (t.isTuple) "INDEX: Tuple expected"
    let (Tup v) = t
    failIf (List.length v <= k) "INDEX: Range check exception"
    let elem = List.item k v
    st.stack <- elem :: stack'
    st

// SETINDEX k (t x – t')
let setindex k st =
    let (x :: (Tup v) :: stack') = st.stack
    failIf (List.length v <= k) "INDEX: Range check exception"
    let v' = List.updateAt k x v
    st.stack <- (Tup v') :: stack'
    st

let newdict st =
    pushnull st

// i D n -> x -1 or 0
let dictiget st =
    let (n :: cD :: i :: stack') = st.stack
    failIfNot (i.isInt) "DICTIGET: Integer expected"
    failIfNot (cD.isCell || cD.isNull) "DICTIGET: Cell or Null expected"
    // Fits n i check has to be done here as well
    let D =
        match cD with
            | Null ->
                Map []
            | Cell (SDict sd :: _) ->
                sd
    match D.TryFind i.unboxInt with
        | None ->
            st.stack <- (Int 0) :: stack'
        | Some v -> // any SValue
            st.stack <- ((Int -1) :: (Slice v) :: stack')
    st

// b i D n --> D'
let dictisetb st =
    let (n :: sD :: i :: b :: stack') = st.stack
    failIfNot (sD.isCell || sD.isNull) "DICTUSETB: Cell or Null expected"
    let D =
        match sD with
            | Cell (SDict sd :: _) ->
                sd
            | Null ->
                Map []
    failIfNot (i.isInt) "DICTUSETB: Integer expected"
    failIfNot (b.isBuilder) "DICTUSETB: Cell expected"
    let sv = b.unboxBuilder  // serialize builder into a cell
    let D' = D.Add (i.unboxInt, sv)
    st.stack <- Cell ([SDict D']) :: stack'
    st

let calldict n st =
    failIf (st.cr.c3.IsNone) "CALLDICT: c3 is not initialized"
    st.cr.c3.Value.data.stack <- [Int n]
    call (st.cr.c3.Value) st

let throwifnot n st =
    let (i :: stack') = st.stack
    failIfNot (i.isInt) "THROWIFNOT: Integer expected"
    if i.unboxInt = 0 then
        raise (TVMError (string n))
    else
        ()
    st.stack <- stack'
    st

let throwif n st =
    let (i :: stack') = st.stack
    failIfNot (i.isInt) "THROWIF: Integer expected"
    if i.unboxInt <> 0 then
        raise (TVMError (string n))
    else
        ()
    st.stack <- stack'
    st

// this implementation is incorrect,
// it should transfer control to C3 cont, but
// for now we skip it
let throw nn st =
    raise (TVMError (string nn))

let ifexec st =
    let (c :: f :: stack') = st.stack
    failIfNot (f.isInt) "IF: Integer expected"
    failIfNot (c.isCont) "IF: Continuation expected"
    if f.unboxInt <> 0 then
        st.stack <- (c :: stack')
        execute st
    else
        st.stack <- stack'
        st

let jmpx st =
    let (c :: stack') = st.stack
    failIfNot (c.isCont) "JMPX: continuation expected"
    st.put_stack stack'
    jump c.unboxCont st

let ifjmp st =
    let (c :: f :: stack') = st.stack
    failIfNot (f.isInt) "IFJMP: Integer expected"
    failIfNot (c.isCont) "IFJMP: Continuation expected"
    st.put_stack stack'
    if (f.unboxInt <> 0) then
        jump c.unboxCont st
    else
        st

let setnumargs n st =
    let (cont :: stack') = st.stack
    failIfNot (cont.isCont) "SETNUMARGS: continuation expected"
    let c : Continuation = cont.unboxCont
    let c1 : Continuation =
        if c.data.nargs < 0 then
            // this is the record "copy with update" operation;
            { c with data = { c.data with nargs = n + (List.length c.data.stack) } }
        else
            c
    st.put_stack (Cont c1 :: stack')
    st

// rollrev 1:
// s0 :: s1 :: s2 :: ... ->
// s1 :: s0 :: s2 ...
// rollrev n:
// s0 :: s1 :: s2 :: ... :: sn :: sn+1 ->
// s1 :: s2 :: sn-1 :: s0 :: sn :: sn+1
let rollrev n (st:TVMState) =
    if n > 0 then
        if n >= List.length st.stack then
            raise (TVMError "stack underflow")
        else
            let (a0 :: stack) = st.stack
            let (l, r) = (List.take n stack, List.skip n stack)
            st.put_stack (l @ [a0] @ r)
            st
    else
        st

// 1 2 3   -> 1 3 2  (roll 1)
// 1 2 3   -> 2 3 1  (roll 2)
// 1 2 3 4 -> 2 3 4 1   (roll 3)
// ... an ... a0  -->  ... an-1 .. a1 a0 an
let roll n (st:TVMState) =
    if n > 0 then
        if n >= List.length st.stack then
            raise (TVMError "stack underflow")
        else
            let spine = List.take (n+1) st.stack // a1 .. an
            let rest = List.skip (n+1) st.stack  // an+1 ...
            let spine' = (List.singleton spine.[n]) @ (List.take n spine) // a2 .. an a1
            st.put_stack (spine' @ rest) // an-1
            st
    else
        st

let drop st =
    pop 0 st

// BLKDROP is a DROP executed n times in a row
let blkdrop n st =
    List.fold (fun st _ -> drop st) st [1..n]

let divmod st =
    let (y :: x :: stack') = st.stack
    failIfNot (y.isInt) "DIVMOD: Integer expected"
    failIfNot (x.isInt) "DIVMOD: Integer expected"
    let x' = x.unboxInt
    let y' = y.unboxInt
    let q = x' / y'
    let r = x' % y'
    st.put_stack (Int r :: Int q :: stack')
    st

// REPEAT (n c – ), executes continuation c n times, if integer n
// is non-negative
let rec repeat st =
   let (c :: (Int n) :: stack') = st.stack
   failIf (n < 0) "REPEAT: range check error"
   // failIfNot (n >= (int64(2) <<< 31)) "REPEAT: range check error"

   if n > 0 then
       st.put_stack stack'
       let st' = call c.unboxCont st
       st'.put_stack (c :: Int (n - 1) :: st'.stack)
       repeat st'
   else
       st.put_stack stack'
       st

// SETINDEXVAR (t x k – t')
let setindexvar st =
    let (Int k :: x :: Tup t :: stack') = st.stack
    st.put_stack (Tup (List.updateAt k x t) :: stack')
    st

// SETINDEXVARQ (t x k – t')
// sets the k-th component of Tuple t to x, where 0 ≤ k < 255, and returns
// the resulting Tuple t 0 . If |t| ≤ k, first extends the original Tuple
// to length k+1  by setting all new components to  Null. If the original
// value of t is Null, treats it as an empty Tuple. If t is not Null or Tuple,
// throws an exception. If x is Null and either |t| ≤ k or t is Null, then
// always returns t' = t (and does not consume tuple creation gas).
let setindexvarq st =
    failIf (List.length st.stack < 3) "SETINDEXVARQ: stack underflow"
    let (k :: x :: t :: stack') = st.stack
    failIfNot (t.isTuple || t.isNull) "SETINDEXVARQ: type check error"
    failIfNot (k.isInt) "SETINDEXVARQ: type check error"
    failIf (k.unboxInt < 0 || k.unboxInt >= 255) "SETINDEXVARQ: range check error"
    if (x.isNull && (t.isNull || List.length t.unboxTup <= k.unboxInt)) then
        st.put_stack (t :: stack')
    else
        let t' = if t.isNull then [] else t.unboxTup
        let k' = k.unboxInt
        let tlen = List.length t'
        if  tlen <= k' then
            let ext = List.init (k' + 1 - tlen) (fun _ -> Null)
            let t'' = t' @ ext
            let res = List.updateAt k' x t''
            st.put_stack (Tup res :: stack')
        else
            let k' = k.unboxInt
            let res = List.updateAt k' x t'
            st.put_stack (Tup res :: stack')
    st



// INDEXVAR (t k – x)
let indexvar st =
    let ((Int k) :: (Tup l) :: stack') = st.stack
    failIf (k < 0) "range check error"
    failIf (k > 254) "range check error"
    failIf (k >= l.Length) "range check error"
    st.put_stack (l.Item k :: stack')
    st

// INDEXVARQ (t k – x)
// If k ≥ n, or if t is Null, returns a Null instead of x.
let indexvarq st =
    let (ki :: t :: stack') = st.stack
    failIfNot (ki.isInt) "INDEXVARQ: type check error"
    failIfNot (t.isTuple || t.isNull) "INDEXVARQ: type check error"
    let k = ki.unboxInt
    let l = if t.isTuple then t.unboxTup else []
    failIf (k < 0 || k > 254) "range check error"
    if (k >= List.length l) then
        st.put_stack (Null :: stack')
    else
        st.put_stack (l.Item k :: stack')
    st


let tuplevar st =
    let ((Int n) :: stack') = st.stack
    st.put_stack stack'
    tuple n true st

let untuplevar st =
    let ( (Int n) :: (Tup l) :: stack' ) = st.stack
    failIf (List.length l <> n) "UNTUPLEVAR: Range check error"
    st.put_stack ( (List.rev l) @ stack')
    st

let tlen st =
    let (Tup l :: stack') = st.stack
    st.put_stack ( (Int (List.length l)) :: stack' )
    st

let second st =
    let (Tup (a0 :: a1 :: _) :: stack') = st.stack
    st.put_stack (a1 :: stack')
    st

let third st =
    let (Tup (a0 :: a1 :: a2 :: _) :: stack') = st.stack
    st.put_stack (a2 :: stack')
    st

let depth (st:TVMState) =
    st.put_stack (Int (List.length st.stack) :: st.stack)
    st

let dec st =
    let (Int n :: stack') = st.stack
    st.put_stack (Int (n-1) :: stack')
    st

let pick st =
    let (Int n :: stack') = st.stack
    st.put_stack (stack'.Item n :: stack')
    st

let xchgx st =
    let (Int n :: stack') = st.stack
    st.put_stack stack'
    xchg n st

// ROT (a b c -> b c a)
let rot st =
    let (c :: b :: a :: stack') = st.stack
    st.put_stack (a :: c :: b :: stack')
    st

// ROTREV (a b c -> c a b)
let rotrev st =
    let (c :: b :: a :: stack') = st.stack
    st.put_stack (b :: a :: c :: stack')
    st
// ROT2 (a b c d e f -> c d e f a b)
let rot2 st =
    let (f :: e :: d :: c :: b :: a :: stack') = st.stack
    st.put_stack (b :: a :: f :: e :: d :: c :: stack')
    st

let ifret st =
    let ((Int n) :: stack') = st.stack
    st.stack <- stack'
    if n <> 0 then
        ret st
    else
        st

let rollrevx st =
    let ( (Int n) :: stack' ) = st.stack
    st.stack <- stack'
    rollrev n st

let dropx st =
    let ((Int n) :: stack') = st.stack
    st.stack <- stack'
    blkdrop n st

let getglob k st =
    let (Tup l) = st.cr.c7
    st.put_stack ((List.item k l) :: st.stack)
    st

let setglob k st =
    let (Tup l) = st.cr.c7
    let (x :: stack') = st.stack
    let l' =
        if l.Length < (k + 1) then
            List.append l (List.init (k + 1 - l.Length) (fun _ -> Null))
        else
            l
    let l'' = List.updateAt k x l'
    st.put_stack stack'
    st.cr.c7 <- Tup l''
    st

let dictugetjmp st =
    let (n :: cD :: k :: stack') = st.stack
    failIfNot n.isInt "DICTUGETJMP: integer expected"
    failIfNot k.isInt "DICTUGETJMP: integer expected"
    failIfNot cD.isCell "DICTUGETJMP: cell expected"
    let (Cell [SDict kv]) = cD
    st.put_stack stack'
    match Map.tryFind k.unboxInt kv with
        | Some (SCode code :: _) ->
            jump { Continuation.Default with code = code } st
        | None ->
            st // on failure, just remove stack arguments

let bless st =
    let (s :: stack') = st.stack
    failIfNot (s.isSlice) "BLESS: Slice expected"
    match s with
        | Slice (SCode c :: []) ->
            st.put_stack (Cont {Continuation.Default with code = c} :: stack')
        | _ ->
            failwith "BLESS: Slice has to carry an ordinary continuation"
    st

let lddict st =
    let (sD :: stack') = st.stack
    failIfNot (sD.isSlice) "LDDICT: Slice expected"
    match sD with
        | Slice (SDict d :: []) ->
            st.put_stack ( Slice [] :: (Cell [SDict d]) :: stack' )
        | _ ->
            failwith "LDDICT: Dictionary within slice expected"
    st

let pushref (c:SValue list) (st:TVMState) =
    st.put_stack ((Cell c) :: st.stack)
    st

// log of the mere instruction is enough to see the dbg message
let printstr s trace st =
    if trace then
        printfn "%A" s
    st

let dumpheap trace st =
    if trace then
        printfn "%A" (st.cr.c7.unboxTup.[1])
    st

let condsel st =
    let (y :: x :: f :: stack') = st.stack
    failIfNot (f.isInt) "CONDSEL: integer expected"
    if f.unboxInt <> 0 then
        st.put_stack (x :: stack')
    else
        st.put_stack (y :: stack')
    st

let dispatch (i:Instruction) (trace:bool) =
    match i with
        | CondSel ->
            condsel
        | DumpHeap ->
            dumpheap trace
        | PrintStr s ->
            printstr s trace
        | StSlice ->
            stslice
        | Bless ->
            bless
        | DictUGetJmp ->
            dictugetjmp
        | GetGlob k ->
            getglob k
        | SetGlob k ->
            setglob k
        | IfRet ->
            ifret
        | Ret ->
            ret
        | PushNull ->
            pushnull
        | PushInt n ->
            pushint n
        | Push n ->
            push n
        | Dup ->
            push 0
        | Dup2 ->
            fun st -> push 1 (push 1 st)
        | Rot ->
            rot
        | Rot2 ->
            rot2
        | RotRev ->
            rotrev
        | PushCtr n ->
            pushctr n
        | PushCont c ->
            pushcont c
        | Pop n ->
            pop n
        | Drop ->
            drop
        | PopCtr n ->
            popctr n
        | Xchg n ->
            xchg n
        | Xchg2 (i,j) ->
            xchg2 i j
        | Swap ->
            xchg 1
        | Swap2 ->
            swap2
        | Equal ->
            binop equal
        | Less ->
            binop lt
        | Greater ->
            binop gt
        | Inc ->
            inc
        | Add ->
            binop add
        | Sub ->
            binop sub
        | Mul ->
            binop mul
        | Div ->
            binop div
        | Execute ->
            execute
        | CallDict n ->
            calldict n
        | JmpX ->
            jmpx
        | IfElse ->
            ifelse
        | DumpStk ->
            dumpstk trace
        | Nop ->
            nop
        | Tuple n ->
            tuple n false
        | TupleVar ->
            tuplevar
        | UntupleVar ->
            untuplevar
        | TLen ->
            tlen
        | Second ->
            second
        | Third ->
            third
        | Nil ->
            nil
        | Index k ->
            index k
        | IndexVar ->
            indexvar
        | IndexVarQ ->
            indexvarq
        | Untuple n ->
            untuple n
        | SetIndex k ->
            setindex k
        | SetIndexVar ->
            setindexvar
        | SetIndexVarQ ->
            setindexvarq
        | TPush ->
            tpush
        | Newc ->
            newc
        | Endc ->
            endc
        | Sti cc ->
            sti cc
        | Ldi cc ->
            ldi cc
        | LdDict ->
            lddict
        | Ends ->
            ends
        | NewDict ->
            newdict
        | DictIGet ->
            dictiget
        | DictISetB ->
            dictisetb
        | ThrowIfNot n ->
            throwifnot n
        | ThrowIf n ->
            throwif n
        | Throw nn ->
            throw nn
        | IfExec ->
            ifexec
        | IfJmp ->
            ifjmp
        | Repeat ->
            repeat
        | SetNumArgs n ->
            setnumargs n
        | RollRev n ->
            rollrev n
        | RollRevX ->
            rollrevx
        | Roll n ->
            roll n
        | DropX ->
            dropx
        | DivMod ->
            divmod
        | Depth ->
            depth
        | Dec ->
            dec
        | Pick ->
            pick
        | XchgX ->
            xchgx
        | BlkDrop n ->
            blkdrop n
        | IsNull ->
            isnull
        | IsZero ->
            iszero
        | PushSlice s ->
            pushslice s
        | PushRef s ->
            pushref s
        | _ ->
            failwith ("unsupported instruction: " + (string i))

let step (st:TVMState) trace : TVMState =
    match (st.code) with
        | [] ->
            if trace then
                printfn "Implicit RET"
            ret st
        | i :: code' ->
            if trace then
                printfn "Executing %A" i
            st.code <- code'
            try
               dispatch i trace st
            with
                | TVMError s ->
                    failwith ("Execution aborted with TVM exception: " + s)
                | _ as exp ->
                    failwith (sprintf "Execution aborted with unknown exception: %A" exp)

let rec runVMLimits st trace maxSteps =
    if maxSteps = 0 then
        failwith "runVM: max steps exceeded"
    let st' = step st trace
    if st.code = [] && st.cr.c0 = None then
        st'.put_stack ((Int 0) :: (st'.stack))
        [st']
    else
        runVMLimits st' trace (maxSteps - 1)

let rec runVM st (trace:bool) =
    runVMLimits st trace 10000

let getResult st : Value option =
    match st.stack with
        | (Int 0) :: s ->
            match s with
                | [] ->
                    None
                | a :: _ ->
                    Some a
        | _ ->
            raise (TVMError "Virtual machine executed with error")

let cellToSliceFift v = v + " <s "

let rec instrToFift (i:Instruction) : string =
    match i with
        | PrintStr s -> "\"" + s + "\" PRINTSTR"
        | Push n -> "s" + (string n) + " PUSH"
        | PushSlice v ->
            (cellToSliceFift (encodeCellIntoFift v)) + " PUSHSLICE"
        | PushRef v ->
            (encodeCellIntoFift v) + " PUSHREF"
        | IsNull -> "ISNULL"
        | IsZero -> "ISZERO"
        | Add -> "ADD"
        | Mul -> "MUL"
        | Div -> "DIV"
        | Sub -> "SUB"
        | Nil -> "NIL"
        | PushNull -> "PUSHNULL"
        | TPush -> "TPUSH"
        | Equal -> "EQUAL"
        | Greater -> "GREATER"
        | Swap -> "SWAP"
        | IfJmp -> "IFJMP"
        | Dup -> "DUP"
        | DictIGet -> "DICTIGET"
        | Inc -> "INC"
        | Dec -> "DEC"
        | Newc -> "NEWC"
        | Drop -> "DROP"
        | DictISetB -> "DICTISETB"
        | Sti n -> (string n) + " STI"
        | Ldi n -> (string n) + " LDI"
        | PushCtr n -> "c" + (string n) + " PUSHCTR"
        | PopCtr n -> "c" + (string n) + " POPCTR"
        | Pop n -> "s" + (string n) + " POP"
        | PushInt n -> (string n) + " INT"
        | Index n -> (string n) + " INDEX"
        | ThrowIfNot n -> (string n) + " THROWIFNOT"
        | ThrowIf n -> (string n) + " THROWIF"
        | UntupleVar -> "UNTUPLEVAR"
        | SetNumArgs n -> (string n) + " SETNUMARGS"
        | Throw n -> (string n) + " THROW"
        | CallDict n -> (string n) + " CALLDICT"
        | SetIndex n -> (string n) + " SETINDEX"
        | PushCont c ->
            "<{ " + String.concat "\n" (List.map instrToFift c) + " }> PUSHCONT"
        | Repeat -> "REPEAT"
        | Pick -> "PICK"
        | TupleVar -> "TUPLEVAR"
        | TLen -> "TLEN"
        | Second -> "SECOND"
        | Third -> "THIRD"
        | Depth -> "DEPTH"
        | Xchg n -> "s0 s" + (string n) + " XCHG" // XCHG s0,sn
        | XchgX -> "XCHGX"
        | DivMod -> "DIVMOD"
        | IndexVar -> "INDEXVAR"
        | IndexVarQ -> "INDEXVARQ"
        | SetIndexVar -> "SETINDEXVAR"
        | SetIndexVarQ -> "SETINDEXVARQ"
        | DumpStk -> "DUMPSTK"
        | Tuple n -> (string n) + " TUPLE"
        | BlkDrop n -> (string n) + " BLKDROP"
        | Xchg2 (i,j) -> "s" + (string i) + " " + "s" + (string j) + " XCHG"
        | Swap2 -> "SWAP2"
        | RollRev n -> (string n) + " ROLLREV"
        | Roll n -> (string n) + " ROLL"
        | Dup2 -> "DUP2"
        | Rot -> "ROT"
        | Rot2 -> "ROT2"
        | RotRev -> "ROTREV"
        | Execute -> "EXECUTE"
        | SetGlob n -> (string n) + " SETGLOB"
        | GetGlob n -> (string n) + " GETGLOB"
        | DictUGetJmp -> "DICTUGETJMP"
        | Ret -> "RET"
        | Less -> "LESS"
        | LdDict -> "LDDICT"
        | Ends -> "ENDS"
        | Bless -> "BLESS"
        | StSlice -> "STSLICE"
        | Endc -> "ENDC"
        | JmpX -> "JMPX"
        | RollRevX -> "ROLLREVX"
        | CondSel -> "CONDSEL"
        | _ ->
            failwith (sprintf "unsupported instruction: %A" i)
// by the given abstract slice, produce TVM assembly code that
// build TVM representation of that slice
and encodeCellIntoFift (s:SValue list) : string =
    match s with
        | (SCode c) :: [] ->
            "<{ " + (codeToFift c |> String.concat " ") + " }>c "
        | (SDict d) :: [] ->  // d = Map<int, SValue list>
            let kv = Map.toList d
            // udict!+ (v k D n - D')
            // k = key : n-bit int
            // v = val : slice
            let dictnew = "dictnew"
            let udictadd (k,v,D,n) =
                [" "; cellToSliceFift (encodeCellIntoFift v); string k; D; string n; "udict!+"; "drop"]
                |> String.concat " "
            (List.fold (fun D (k,v) -> udictadd(k, v, D, 8)) dictnew kv) + " "
        | _ ->
            failwith "not implemented"
and codeToFift c : string list =
    c |> List.map instrToFift

let outputFift (st:TVMState) : string =
    String.concat "\n" [
        "\"Asm.fif\" include";
        "<{";
        (codeToFift st.code |> String.concat "\n")
        "}>s";
        "1000000 gasrunvmcode";  // 1000000 = TVM gas limit
        "swap drop"; // omit VM exit code
        ".s"
    ]

let dumpFiftScript (fname:string) (str:string)  =
    use f = System.IO.File.CreateText(fname)
    f.WriteLine(str)

let bucketSize = 254;
let arrayDefaultVal = Null
let arrayNew = [PushNull]

// a v k -> a'
let arrayPut =
    [SetIndexVarQ]

// a k -> a[k]
let arrayGet =
    [IndexVarQ]

// a k -> a[k] -1 | null 0
let arrayGetWithCode =
    arrayGet @ [Dup; IsNull; IsZero]

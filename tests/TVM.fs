module TVM

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework
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
    | Push of n:int
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
    | PushInt of n:int
    | PushCont of c:Code
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
    | DumpStk
    | Nop
    | Tuple of n:int
    | TLen
    | TupleVar
    | UntupleVar
    | Nil
    | PushNull
    | Second
    | Index of k:int
    | IndexVar
    | Untuple of n:int
    | SetIndex of k:int
    | SetIndexVar
    | TPush
    | Newc
    | Endc
    | Stu of cc:int
    | Ldu of cc:int
    | Ends
    | StRef
    | NewDict    // ... -> ... D
    | DictUGet   // i D n -> x (-1),  or 0
    | DictUSetB  // b i D n -> D'
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
    | Repeat
    | Depth
    | Dec
    | Pick
    | XchgX
    | PushSlice of c:SValue list
    | StSlice
    | IsNull
    | IsZero
    | Dup2
    | Rot2
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
    static member unboxCont = function | Cont x -> x | _ -> failwith "Cont expected"
    static member unboxTup = function | Tup x -> x | _ -> failwith "Tup expected"
    member this.asSV : SValue =
        match this with
        | Int n -> SInt n
        | Cont c -> SCode (c.code)
        | Cell s as p -> SCell p
        | _ -> failwith "not serializable"
    member this.unboxInt = match this with | Int x -> x | _ -> failwith "Int expected"
    member this.unboxBuilder = match this with | Builder x -> x | _ -> failwith "Builder expected"
    member this.unboxSlice = match this with | Slice vs -> vs | _ -> failwith "Slice expected"
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
    | SCell of c:Value   // c is a cell
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
and Stack =
    Value list

let TVM_True = (Int -1)
let TVM_False = (Int 0)

let contQuit : Continuation =
    { code = []; data = ControlData.Default }

let isOverflow n =
    // skip the test for now
    false

let failIfNot b str =
    if (not b) then
        raise (TVMError str)
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
        // if save.c7.IsSome then this.cr.c7 <- None else ()
    member this.adjust_cr regs =
        this.cr.c0 <- if regs.c0.IsSome then regs.c0 else this.cr.c0
        this.cr.c3 <- if regs.c3.IsSome then regs.c3 else this.cr.c0
        // this.cr.c7 <- if regs.c7.IsSome then regs.c7 else this.cr.c7
    member this.put_code code =
        this.code <- code
    member this.put_stack stk =
        this.stack <- stk

// do the ordinary jump into continuation cont
let switch_to_cont cont (st:TVMState) =
    st.adjust_cr cont.data.save
    st.put_code cont.code
    st

// cont = continuation to jump to
// pass_args = number of arguments to pass to the continuation
        // -1 = the whole current stack needs to be passed
        // before doing the jump
let jump_stk cont pass_args st =
    let depth = List.length st.stack
    if (pass_args > depth || cont.data.nargs > depth) then
        raise (TVMError "jump_stk: stack underflow: not enough args on the stack")
    elif (cont.data.nargs > pass_args && pass_args >= 0) then
        raise (TVMError "jump_stk: stack underflow: not enough arguments passed")
    st.preclear_cr cont.data.save
    let copy =
        if (cont.data.nargs < 0) && (pass_args >= 0) then
            pass_args
        else
            cont.data.nargs
    let copy' = if copy < 0 then depth else copy
    let new_stk = cont.data.stack @ (List.take copy' st.stack)
    st.put_stack new_stk
    switch_to_cont cont st

let jump_to cont (st:TVMState) =
    switch_to_cont cont st

let jump cont (st:TVMState) =
    if (cont.data.stack <> []) || (cont.data.nargs >= 0) then
        jump_stk cont -1 st         // the stack needs to be adjusted before the CC switch
    else
        switch_to_cont cont st      // do the CC switch immediately

let call cont (st:TVMState) =
    if cont.data.save.c0.IsSome then
        jump cont st
    elif cont.data.stack <> [] then
        failIf (cont.data.nargs <> -1) "CALL: nargs different from -1 is not supported"
        let ret = { code = st.code; data = { ControlData.Default with stack = st.stack; save = { c0 = st.cr.c0; c3 = st.cr.c3; c7 = st.cr.c7 } } }
        st.put_stack cont.data.stack
        st.cr.c0 <- Some ret
        jump_to cont st
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

[<OneTimeSetUp>]
let Setup () =
    ()

let printTerm term =
    let str = sprintf "%A" term
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

let initialState (code:Code) : TVMState =
    let st = { code = code; stack = []; cr = ControlRegs.Default }
    st.cr.c0 <- Some contQuit
    st

let mkBuilder (vs:SValue list) =
    Builder vs

let mkCell (b:Value) : Value =
    failIfNot (b.isBuilder) "not a builder"
    Cell b.unboxBuilder

let stu cc st =
    let (b :: x :: stack') = st.stack
    failIfNot (b.isBuilder) "STU: not a builder"
    failIfNot (x.isInt) "STU: not an integer"
    let vs = b.unboxBuilder
    // failIf (x > float 2 ** cc) "STU: Range check exception"
    st.put_stack (mkBuilder (vs @ [x.asSV]) :: stack')
    st

let ldu cc st =
    let (s :: stack') = st.stack
    failIfNot (s.isSlice) "LDU: slice expected"
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
    call (Value.unboxCont cont) st

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

let stslice s st =
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
        st.cr.c3 <- Some (Value.unboxCont c3)
    st

let pop n st =
    let (a :: _) = st.stack
    st.stack <- List.tail (List.updateAt n a st.stack)
    st

let xchg2 i j st =
    failIf (List.length st.stack <= j) "XCHG: Stack underflow"
    let stk = List.toArray st.stack
    let si = stk.[i]
    let sj = stk.[j]
    let tmp = stk.[j]
    let stack' =
        Array.updateAt j si stk |>  // s[j] := s[i]
        Array.updateAt i tmp |> // s[i] := old s[j]
        Array.toList
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

let equal v1 v2 =
    if v1 = v2 then -1 else 0

let inc st =
    let (a1 :: stack') = st.stack
    failIfNot (a1.isInt) "INC: stack item must be integer"
    // TODO: overflow check
    st.stack <- Int (a1.unboxInt + 1) :: stack'
    st

let dumpstk st =
    let stk = st.stack
    printfn "STACK: %A"  stk
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
    let (Tup v :: stack') = st.stack
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
let dictuget st =
    printfn "%A" st.stack
    let (n :: sD :: i :: stack') = st.stack
    failIfNot (i.isInt) "DICTUGET: Integer expected"
    // UFits n i check has to be done here as well
    let D =
        match sD with
            | Null ->
                Map []
            | Slice (SDict sd :: _) ->
                sd
    match D.TryFind i.unboxInt with
        | None ->
            st.stack <- (Int 0) :: stack'
        | Some v -> // any SValue
            st.stack <- ((Int -1) :: (Slice v) :: stack')
    st

// b i D n --> D'
let dictusetb st =
    let (n :: sD :: i :: b :: stack') = st.stack
    let D =
        match sD with
            | Slice (SDict sd :: _) ->
                sd
            | Null ->
                Map []
    failIfNot (i.isInt) "DICTUSET: Integer expected"
    failIfNot (b.isBuilder) "DICTUSET: Builder expected"
    let sv = b.unboxBuilder  // serialize builder into a cell
    let D' = D.Add (i.unboxInt, sv)
    st.stack <- Slice ([SDict D']) :: stack'
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
    jump (Value.unboxCont c) st

let ifjmp st =
    let (c :: f :: stack') = st.stack
    failIfNot (f.isInt) "IFJMP: Integer expected"
    failIfNot (c.isCont) "IFJMP: Continuation expected"
    st.put_stack stack'
    if (f.unboxInt <> 0) then
        jump (Value.unboxCont c) st
    else
        st

let setnumargs n st =
    let (cont :: stack') = st.stack
    failIfNot (cont.isCont) "SETNUMARGS: continuation expected"
    let c = Value.unboxCont cont
    if c.data.nargs < 0 then
        c.data.nargs <- n + (List.length c.data.stack)
    else
        ()
    st.put_stack (Cont c :: stack')
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

let drop st =
    pop 0 st

// BLKDROP is a DROP executed n times in a row
let blkdrop n st =
    List.fold (fun st _ -> drop st) st [1..n]

let divmod st =
    let (Int y :: Int x :: stack') = st.stack
    let q = x / y
    let r = x % y
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
       let st' = call (Value.unboxCont c) st
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

// INDEXVAR (t k – x)
let indexvar st =
    let ((Int k) :: (Tup l) :: stack') = st.stack
    failIf (k < 0) "range check error"
    failIf (k > 254) "range check error"
    failIf (k >= l.Length) "range check error"
    st.put_stack (l.Item k :: stack')
    st

let tuplevar st =
    let ((Int n) :: stack') = st.stack
    st.put_stack stack'
    tuple n true st

let untuplevar st =
    let ( (Tup l) :: (Int n) :: stack' ) = st.stack
    failIf (List.length l <> n) "UNTUPLEVAR: Range check error"
    st.put_stack (l @ stack')
    st

let tlen st =
    let (Tup l :: stack') = st.stack
    st.put_stack ( (Int (List.length l)) :: stack' )
    st

let second st =
    let (Tup (a0 :: a1 :: _) :: stack') = st.stack
    st.put_stack (a1 :: stack')
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

let dispatch (i:Instruction) =
    match i with
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
        | Rot2 ->
            rot2
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
            dumpstk
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
        | Nil ->
            nil
        | Index k ->
            index k
        | IndexVar ->
            indexvar
        | Untuple n ->
            untuple n
        | SetIndex k ->
            setindex k
        | SetIndexVar ->
            setindexvar
        | TPush ->
            tpush
        | Newc ->
            newc
        | Endc ->
            endc
        | Stu cc ->
            stu cc
        | Ldu cc ->
            ldu cc
        | Ends ->
            ends
        | NewDict ->
            newdict
        | DictUGet ->
            dictuget
        | DictUSetB ->
            dictusetb
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
        | _ ->
            failwith (sprintf "unsupported instruction: %A" i)

let step (st:TVMState) : TVMState =
    match (st.code) with
        | [] ->
            printfn "Implicit RET"
            ret st
        | i :: code' ->
            printfn "Executing %A" i
            st.code <- code'
            dispatch i st

let rec runVM st (trace:bool) =
    let st' = step st
    if st.code = [] && st.cr.c0 = None then
        st'.stack <- (Int 0) :: (st'.stack)
        [st']
    else
        st' :: (runVM st' trace)

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

[<Test>]
let testInitState () =
    let st = initialState []
    Assert.AreEqual (st, step st)

[<Test>]
let testPushInt0 () =
    let st = initialState [PushInt 10]
    let finalSt = List.last (runVM st false)
    Assert.AreEqual ( Some (Int 10), getResult finalSt )

[<Test>]
let testPushInt1 () =
    let st = initialState [PushInt 10; PushInt 20]
    let finalSt = List.last (runVM st false)
    Assert.AreEqual ( Some (Int 20), getResult finalSt )

[<Test>]
let testPush0 () =
    let st = initialState [PushInt 10; PushInt 20; Push 1]
    try
        let states = runVM st true
        let finalSt = List.last states
//        printTerm finalSt
        Assert.AreEqual ( Some (Int 10), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPush1 () =
    let st = initialState [PushInt 10; PushInt 20; Push 0]
    try
        let finalSt = List.last (runVM st false)
//        printTerm finalSt
        Assert.AreEqual ( Some (Int 20), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPop0 () =
    let st = initialState [PushInt 10; PushInt 20; Pop 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 10), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPop1 () =
    let st = initialState [PushInt 10; PushInt 20; Pop 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 20), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPop2 () =
    let st = initialState [PushInt 30; PushInt 10; PushInt 20; Pop 1; Pop 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 30), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testAdd () =
    let st = initialState [PushInt 30; PushInt 10; Add]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 40), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testSub () =
    let st = initialState [PushInt 30; PushInt 10; Sub]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 20), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute0 () =
    let st = initialState [PushCont []]
    let emptyCont = Cont emptyContinuation
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some emptyCont, getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute1 () =
    let st = initialState [PushCont []; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (None, getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute2 () =
    let st = initialState [PushCont [PushInt 10]; DumpStk; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute3 () =
    let st = initialState [PushInt 10; PushCont [PushInt 20; Add]; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 30), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute4 () =
    let st = initialState [PushInt 10;
                           PushCont [PushCont [PushInt 20]; Execute; Add];
                           Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 30), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

let testExecute5 () =
    let st = initialState [PushCont [PushCont [PushInt 30]]; Execute; Execute; PushInt 20]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 20), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)


[<Test>]
let testIfElse0 () =
    let st = initialState [PushInt 0;
                           PushCont [PushInt 10];
                           PushCont [PushInt 20];
                           IfElse]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 20), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testXchg0 () =
    let st = initialState [PushInt 10; PushInt 20; Xchg 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testXchg1 () =
    let st = initialState [PushInt 30; PushInt 10; PushInt 20; Xchg 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 30), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testXchgId () =
    let st = initialState [PushInt 30; PushInt 10; PushInt 20; Xchg 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 20), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater0 () =
    let st = initialState [PushInt 30; PushInt 10; Greater]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int -1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater1 () =
    let st = initialState [PushInt 10; PushInt 30; Greater]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater2 () =
    // let f n = if n > 10 then n else (n - 1)
    let st = initialState [Push 0;
                           PushInt 10;
                           Greater;
                           PushCont [];
                           PushCont [PushInt 1; Sub];
                           IfElse]
    st.stack <- [Int 7]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 6), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater3 () =
    // Recursion
    // let f n g =
    //    if n > 10 then (g (n - 1)) else n
    // eval (f 12 f)
    let st = initialState [PushCont [Push 1;    // n f n
                                     PushInt 0; // 0 n f n
                                     Greater; // (n > 0?) f n
                                     PushCont [Xchg 1; // n f
                                               PushInt 1; // 1 n f
                                               Sub;  // (n-1) f
                                               Xchg 1; // f (n-1)
                                               Push 0; // f f (n-1)
                                               Execute]; //
                                     PushCont [Push 1] // c2 c1 (n>0?) f n
                                     IfElse]; // f n
                           Push 0; // f f n
                           Execute // -> f n
                           ]
    st.stack <- [Int 12]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTuple0 () =
    let st = initialState [Nil]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTuple1 () =
    let st = initialState [Nil; Tuple 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Tup []]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTuple2 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Int 1; Int 2]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndex0 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2; Index 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndex1 () =
    let st = initialState [Nil; Index 0]
    try
        runVM st false |> ignore
    with
        | TVMError s ->
            Assert.Pass()

[<Test>]
let testUntuple0 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2; Untuple 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testUntuple1 () =
    // exception is anticipated here
    let st = initialState [Nil; Untuple 2]
    try
        runVM st false |> ignore
    with
        | TVMError s ->
            Assert.Pass()

[<Test>]
let testSetIndex0 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2;
                           PushInt 3; SetIndex 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Int 3; Int 2]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testNewC () =
    let st = initialState [Newc]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Builder []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testEndC () =
    let st = initialState [Newc; Endc]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Cell []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testStu0 () =
    let st = initialState [PushInt 100; Newc; Stu 255]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Builder [SInt 100]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testStu1 () =
    let st = initialState [PushInt 200; PushInt 100; Newc;
                           Stu 255; Stu 255]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (
            Some (Builder [SInt 100; SInt 200]),
            getResult finalSt
        )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDict0 () =
    let st = initialState [PushInt 10; // 10
                           Newc; // 10 b
                           Stu 128; // b'
                           PushInt 200; // b' 200(key)
                           NewDict; // b' 200 D
                           PushInt 10; // b' 200 D 10
                           DictUSetB] // D'
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (
            Some (Slice [SDict (Map [(200, [SInt 10])])]),
            getResult finalSt
        )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDict1 () =
    let st = initialState [DictUGet] // k D' i -> v
    st.stack <- [Int 128;
                 Slice [SDict (Map [(200, [SInt 10])])]; Int 200]
    try
        let finalSt = List.last (runVM st false)
        let ((Int 0) :: (Int -1) :: s1 :: t) = finalSt.stack
        printfn "%A" finalSt.stack
        Assert.AreEqual (
            (Int 0) :: (Int -1) :: [Slice [SInt 10]],
            List.take 3 finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPushctr0 () =
    let st = initialState [PushCtr 7] // k D' i -> v
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPopctr0 () =
    let st = { TVMState.Default with code = [PushCtr 7; PushInt 200; TPush;
                                             PopCtr 7; PushCtr 7] }
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Int 200]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPopctr1 () =
    let st = initialState [PushCont [PushInt 10]; PopCtr 3; PushCtr 3; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testCalldict0 () =
    let st = initialState [PushCont [Drop; PushInt 10]; PopCtr 3; CallDict 5]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

let rec instrToFift (i:Instruction) : string =
    match i with
        | Push n -> "s" + string(n) + " PUSH"
        | IsNull -> "ISNULL"
        | IsZero -> "ISZERO"
        | Add -> "ADD"
        | Nil -> "NIL"
        | PushNull -> "PUSHNULL"
        | TPush -> "TPUSH"
        | Equal -> "EQUAL"
        | Swap -> "SWAP"
        | IfJmp -> "IFJMP"
        | Dup -> "DUP"
        | DictUGet -> "DICTUGET"
        | Inc -> "INC"
        | Dec -> "DEC"
        | Newc -> "NEWC"
        | Drop -> "DROP"
        | DictUSetB -> "DICTUSETB"
        | Stu n -> string(n) + " STU"
        | PushCtr n -> "c" + string(n) + " PUSHCTR"
        | PopCtr n -> "c" + string(n) + " POPCTR"
        | PushInt n -> string(n) + " INT"
        | Index n -> string(n) + " INDEX"
        | ThrowIfNot n -> string(n) + " THROWIFNOT"
        | SetNumArgs n -> string(n) + " SETNUMARGS"
        | Throw n -> string(n) + " THROW"
        | CallDict n -> string(n) + " CALLDICT"
        | SetIndex n -> string(n) + " SETINDEX"
        | PushCont c ->
            "<{ " + String.concat "\n" (List.map instrToFift c) + " }> PUSHCONT"
        | Repeat -> "REPEAT"
        | Pick -> "PICK"
        | TupleVar -> "TUPLEVAR"
        | TLen -> "TLEN"
        | Second -> "SECOND"
        | Depth -> "DEPTH"
        | Xchg n -> "s0 s" + string(n) + " XCHG" // XCHG s0,sn
        | XchgX -> "XCHGX"
        | DivMod -> "DIVMOD"
        | IndexVar -> "INDEXVAR"
        | SetIndexVar -> "SETINDEXVAR"
        | DumpStk -> "DUMPSTK"
        | Tuple n -> string(n) + " TUPLE"
        | BlkDrop n -> string(n) + " BLKDROP"
        | Xchg2 (i,j) -> "s" + string(i) + " " + "s" + string(j) + " XCHG"
        | Swap2 -> "SWAP2"
        | RollRev n -> string(n) + " ROLLREV"
        | Dup2 -> "DUP2"
        | Rot2 -> "ROT2"
        | _ ->
            failwith (sprintf "unsupported instruction: %A" i)

let outputFift (st:TVMState) : string =
    String.concat "\n" [
        "\"Asm.fif\" include";
        "<{";
        String.concat "\n" (List.map instrToFift st.code);
        "}>s";
        "runvmcode";
        "drop";
        ".s"
    ]

let dumpFiftScript (fname:string) (str:string)  =
    use f = System.IO.File.CreateText(fname)
    f.WriteLine(str)

[<Test>]
let testCalldict1 () =
    // input = [], output = heap
    let (heapGet, heapGetCode) = (0, [PushCtr 7; Index 0])
    // input = heap, output = []
    let (heapPut, heapPutCode) = (1, [PushCtr 7; Swap; SetIndex 0; Drop])
    // input = [], output = nextAddr
    let (heapNextAddr, heapNextAddrCode) =
        (2, [
            PushCtr 7; // c7
            Index 1;   // ctr
            Inc;       // ctr'
            Dup;       // ctr' ctr'
            PushCtr 7; // ctr' ctr' c7
            Swap;      // ctr' c7 ctr'
            SetIndex 1;// ctr' c7'
            PopCtr 7;  // ctr'
        ]
    )
    // input = k, output = heap[k]
    let (heapLookup, heapLookupCode) =
        (3, heapGetCode @ [PushInt 128; DictUGet; ThrowIfNot 1])

    // input = (k:int) (v:Builder); output = heap'[k := v]
    let (heapUpdateAt, heapUpdateAtCode) =
        (4, heapGetCode @ [PushInt 128; DictUSetB] )

    // intput = n , output = builder (contains n as uint)
    let (intToBuilder, intToBuilderCode) =
        (5, [Newc; Stu 128])

    // the structure of C7 is as follows:
    // C7[0] = heap (dict)
    // C7[1] = heap address counter (int)
    // C7[2] = globals (dict) (funcId -> address)

    // heap is represented as a dictionary (SliceDict type)
    // heap address counter is an integer, starting from 0
    let initC7 = [
        Nil;       // ()
        PushNull;  // (0) null
        TPush;     // (null)
        PushInt 0; // (null) 0
        TPush;     // (0, null)
        PushNull;  // (0, null) null
        TPush;     // (null, 0, null)
        PopCtr 7;
    ]
    // input = args... n
    // output = C3[n](args)
    let compileSelectorFunction (id, args_cnt, cont) =
        [Dup; PushInt id; Equal; PushCont cont; SetNumArgs args_cnt; IfJmp]

    let selectorFunctions = [
        (heapLookup, 1, heapLookupCode);
        (heapPut, 1, heapPutCode);
        (heapGet, 1, heapGetCode);
        (heapNextAddr, 0, heapNextAddrCode);
        (heapUpdateAt, 2, heapUpdateAtCode);
        (intToBuilder, 1, intToBuilderCode)
    ]

    let functionNotFoundException =
        [Throw 100]

    let selectorFunction =
        ((List.map compileSelectorFunction selectorFunctions)
        |> List.concat)
        @ functionNotFoundException

    let st = initialState (
        initC7 @
        [PushCont selectorFunction;
         PopCtr 3;
         CallDict heapNextAddr;
         Drop;
         CallDict heapNextAddr
         ]
    )
    try
        dumpFiftScript "testCalldict1.fif" (outputFift st)
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 2), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev0 () =
    let st = initialState [RollRev 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ([Int 0], finalSt.stack) // success int
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev1 () =
    let st = initialState [PushInt 1; RollRev 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ([Int 0; Int 1], finalSt.stack) // success int
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev2 () =
    let st = initialState [PushInt 1; RollRev 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("must not reach this point")
    with
        | TVMError s ->
            Assert.Pass() // Stack underflow

[<Test>]
let testRollRev3 () =
    let st = initialState [PushInt 1; PushInt 2; RollRev 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual([Int 0; Int 1; Int 2], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev4 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; RollRev 2]
    try
        let finalSt = List.last (runVM st false)
        printfn "%A" finalSt.stack
        Assert.AreEqual([Int 0; Int 2; Int 1; Int 3], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

// a0 : a1 : a2 : ... an : sn
// -->
// a1' : a2' : .. an' :  an : sn
// ai' = map ai
// k is just a recursive counter
let rec rearrange n map st =
    failIf (st.stack.Length <= n) "rearrange: stack underflow"
    let rec rearrange2 k n st =
        if k > n then st
        else
            rearrange2 (k + 1) n (drop (xchg (k + 1) (map k st)))
    let drop_a0 = drop st // remove the a0 element
    if n > 0 then
        let dup_an = rollrev (n-1) (push (n-1) drop_a0) // dup an element
        rearrange2 0 (n-1) dup_an
    else
        drop_a0

[<Test>]
let testRearrange0 () =
    let st = initialState []
    st.put_stack ([Int 1; Int 2; Int 3])
    try
        let finalSt = rearrange 2 (fun k -> push k) st
        printfn "%A" finalSt.stack
        Assert.AreEqual([Int 2; Int 3; Int 3], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRearrange1 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    try
        let finalSt = rearrange 0 (fun k -> push k) st
        Assert.Fail("rearrange should work only with non-empty stack")
    with
        | TVMError s ->
            Assert.Pass() // ok

[<Test>]
let testRearrange2 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    st.put_stack ([Int 1; Int 2])
    try
        let finalSt = rearrange 1 (fun k -> push k) st
        printfn "%A" finalSt.stack
        Assert.AreEqual([Int 2; Int 2], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRearrange3 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    st.put_stack ([Int 1; Int 2; Int 3; Int 4])
    try
        let finalSt = rearrange 2 (fun k -> push k) st
        printfn "%A" finalSt.stack
        Assert.AreEqual([Int 2; Int 3; Int 3; Int 4], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRearrange4 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    st.put_stack ([Int 1])
    try
        let finalSt = rearrange 1 (fun k -> push k) st
        printfn "%A" finalSt.stack
        Assert.Fail("stack underflow shall happen")
    with
        | TVMError s ->
            Assert.Pass(s)

[<Test>]
let testRearrange5 () =
    let st = initialState []
    st.put_stack ([Int 1])
    try
        let finalSt = rearrange 0 (fun k -> push k) st
        printfn "%A" finalSt.stack
        Assert.AreEqual([], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRearrange6 () =
    let st = initialState []
    st.put_stack ([Int 1; Int 2; Int 3])
    try
        let finalSt = rearrange 0 (fun k -> push k) st
        printfn "%A" finalSt.stack
        Assert.AreEqual([Int 2; Int 3], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

let bucketSize = 10;
let arrayDefaultVal = Null
let arrayNew =
    [PushInt bucketSize; PushCont [PushNull]; Repeat;
     PushInt bucketSize; TupleVar; PushInt (bucketSize-1);
     PushCont [Dup]; Repeat; PushInt bucketSize; TupleVar]

// a k v -> a'
let arrayPut =
    [Swap;  // a v k
     PushInt bucketSize; // a v k bs
     DivMod;  // a v i j
     Xchg2 (1,2) // a i v j
     Swap2; // v j a i
     Dup2;  // v j a i a i
     Rot2;  // a i a i v j
     Swap2; // a i v j a i
     IndexVar; // a i v j a[i]
     Xchg 2; // a i a[i] j v
     Swap;   // a i a[i] v j
     SetIndexVar; // a i a[i][j -> v]
     Swap;
     SetIndexVar] // a[i -> a[i][j -> v]]

// a k -> a[k]
let arrayGet =
    [PushInt bucketSize; // a k bs
     DivMod; // a i j
     RollRev 2; // j a i
     IndexVar; // j a[i]
     Swap; // a[i] j
     IndexVar] // a[i][j]

// a k -> a[k] -1 | null 0
let arrayGetWithCode =
    arrayGet @ [Dup; IsNull; IsZero]

[<Test>]
let testTupleVar0 () =
    let st = initialState [PushInt 0; TupleVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTupleVar1 () =
    let st = initialState [PushInt 100; PushInt 1; TupleVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup [Int 100]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTupleVar2 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2; TupleVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup [Int 200; Int 100]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDivmod0 () =
    let st = initialState [PushInt 10; PushInt 3; DivMod]
    try
        let finalSt = List.last (runVM st false)
        printfn "%A" finalSt.stack
        Assert.AreEqual([Int 1; Int 3], List.tail finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndexvar0 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2;
                           TupleVar; PushInt 1; IndexVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 100), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndexvar1 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2;
                           TupleVar; PushInt 3; IndexVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("range error")
    with
        | TVMError s ->
            Assert.Pass()

[<Test>]
let testSetindexvar0 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2;
                           TupleVar; PushInt 300; PushInt 1;
                           SetIndexVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup [Int 200; Int 300]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testArrayGetPut () =
    let st = initialState (arrayNew @ [PushInt 1] @ arrayGet)
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (arrayDefaultVal), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRepeat0 () =
    let st = initialState [PushInt 0; PushCont [PushInt 200]; Repeat]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(None, getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRepeat1 () =
    let st = initialState [PushInt 1; PushCont [PushInt 100]; Repeat]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 100), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRepeat2 () =
    let st = initialState [PushInt 3; PushCont [Nil]; Repeat]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testArrayGetPut1 () =
    let code = arrayNew @ [PushInt 1; PushInt 600] @ arrayPut @ [DumpStk; PushInt 1] @ arrayGet
    let st = initialState code
    dumpFiftScript "testArrayGetPut1.fif" (outputFift st)
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 600), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDepth0 () =
    let st = initialState [Depth]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDepth1 () =
    let st = initialState [PushInt 100; Depth]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDepth2 () =
    let st = initialState [PushInt 100; PushInt 200; Drop; Drop; Depth]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDec0 () =
    let st = initialState [PushInt 0; Dec]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int -1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDec1 () =
    let st = initialState [PushCont []; Dec]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("Dec expects integer")
    with
        | _ -> Assert.Pass()

[<Test>]
let testPick0 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2; PushInt 2; Pick]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPick1 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2; PushInt 3; Pick]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("Out of bound")
    with
        | _ -> Assert.Pass()

[<Test>]
let testXchgx0 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2;
                           PushInt 1; XchgX]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testBlkDrop0 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2; PushInt 3; BlkDrop 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIsNull0 () =
    let st = initialState [PushNull; IsNull]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int -1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIsNull1 () =
    let st = initialState [PushInt 0; IsNull]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testSwap () =
    let st = initialState [PushInt 0; PushInt 1; Swap]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testSwap2 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; PushInt 4; Swap2]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        printfn "%A" stk
        Assert.AreEqual([Int 2; Int 1; Int 4; Int 3], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRot2 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3;
                           PushInt 4; PushInt 5; PushInt 6; Rot2]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        printfn "%A" stk
        Assert.AreEqual([Int 2; Int 1; Int 6; Int 5; Int 4; Int 3], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecutePushCtr0 () =
    // this is unintuitive; The continuation in C0 already has save.c0 set,
    // so the obvious return point to PushInt 2 will be changed back to
    // that save.c0, which is contQuit. So, this code will execute only one
    // PushInt 1.
    let st = initialState [PushCont [PushCtr 0; Execute; PushInt 2]; Execute; PushInt 1]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 1], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecuteTriple () =
    // this is unintuitive; The continuation in C0 already has save.c0 set,
    // so the obvious return point to PushInt 2 will be changed back to
    // that save.c0, which is contQuit. So, this code will execute only one
    // PushInt 1.
    let st = initialState [PushCont [PushCont [PushInt 2]; Execute; PushInt 1]; Execute; PushInt 0]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 0; Int 1; Int 2], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

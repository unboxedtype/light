module TVM

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework
open System
open System.Collections.Generic

exception TVMError of string

type Instruction =
    | Push of n:int
    | Dup               // Push 0 alias
    | Pop of n:int
    | Drop              // Pop 0 alias
    | Xchg of i:int     // Xchg s0, s(i)
    | Swap              // Xchg 0 alias
    | Greater
    | PushInt of n:int
    | PushCont of c:Code
    | PushCtr of n:int
    | PopCtr of n:int
    | IfElse
    | Inc
    | Add
    | Sub
    | DivMod
    | Execute
    | CallDict of n:int
    | JumpX
    | DumpStk
    | Nop
    | Tuple of n:int
    | TupleVar
    | Nil
    | PushNull
    | Index of k:int
    | IndexVar
    | Untuple of n:int
    | SetIndex of k:int
    | SetIndexVar
    | TPush
    | Newc
    | Endc
    | StU of cc:int
    | StRef
    | NewDict    // ... -> ... D
    | DictUGet   // i D n -> x (-1),  or 0
    | DictUSetB  // b i D n -> D'
    | ThrowIfNot of nn:int
    | Throw of nn:int
    | Equal
    | IfExec     // If
    | IfJmp
    | SetNumArgs of n:int
    | RollRev of n:int
    | Repeat
    | Depth
    | Dec
    | Pick
    | XchgX
and Code =
    Instruction list

// codepage number is an unsigned integer
type CodePage =
    int

type Action =
    SendMsg

type Value =
    | Int of v:int
    | Tup of v:Value list
    | Null
    | Cont of v:Continuation
    | Builder of vs:Value list
    | Cell of v:Value list
    | Slice of vs:Value list
    | SliceDict of v:Map<int,Value> // this one is artificial
    static member isInt = function | Int _ -> true | _ -> false
    static member isCont = function | Cont _ -> true | _ -> false
    static member isBuilder = function | Builder _ -> true | _ -> false
    static member isSlice = function | Slice _ -> true | _ -> false
    static member isSliceDict = function | SliceDict _ -> true | _ -> false
    static member isTuple = function | Tup _ -> true | _ -> false
    static member unboxInt = function | Int x -> x | _ -> raise (TVMError "unbox")
    static member unboxCont = function | Cont x -> x | _ -> raise (TVMError "unbox")
    static member unboxTuple = function | Tup x -> x | _ -> raise (TVMError "unbox")
    static member unboxBuilder = function | Builder x -> x | _ -> raise (TVMError "unbox")
    static member boxInt = fun n -> Int n
    static member boxDict = fun v -> SliceDict v
    static member unboxDict = function | Null -> Map [] | SliceDict v -> v | _ -> raise (TVMError "unbox")

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
        switch_to_cont cont st         // do the CC switch immediately

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
        let ret = { code = st.code; data = { ControlData.Default with save = { c0 = st.cr.c0; c3 = st.cr.c3; c7 = st.cr.c7 } } }
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
    { code = code; stack = []; cr = ControlRegs.Default }

let mkBuilder vs =
    Builder vs

let mkCell b =
    Cell (Value.unboxBuilder b)

let stu cc st =
    let (b :: x :: stack') = st.stack
    failIfNot (Value.isBuilder b) "STU: not a builder"
    failIfNot (Value.isInt x) "STU: not an integer"
    let vs = Value.unboxBuilder b
    // failIf (x > float 2 ** cc) "STU: Range check exception"
    st.put_stack (mkBuilder (vs @ [x]) :: stack')
    st

let newc st =
    let stack = st.stack
    st.put_stack (mkBuilder [] :: stack)
    st

let endc st =
    let (b :: stack) = st.stack
    failIfNot (Value.isBuilder b) "ENDC: not a builder"
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
            failIfNot (Value.isTuple st.cr.c7) "PUSHCTR: C7 is a tuple"
            st.cr.c7 :: st.stack
        elif n = 3 then
            if st.cr.c3.IsSome then
                (Cont st.cr.c3.Value) :: st.stack
            else
                raise (TVMError "PUSHCTR: Register c3 is not initialized")
        else
            raise (TVMError "PUSHCTR: only c3 and c7 are supported")
    st.stack <- stack
    st

let popctr n st =
    failIf (n <> 7 && n <> 3) "POPCTR: only c3 and c7 are supported"
    if n = 7 then
        let (c7 :: stack) = st.stack
        failIfNot (Value.isTuple c7) "POPCTR: c7 is a tuple"
        st.stack <- stack
        st.cr.c7 <- c7
    else
        let (c3 :: stack) = st.stack
        failIfNot (Value.isCont c3) "POPCTR: c3 is a continuation"
        st.stack <- stack
        st.cr.c3 <- Some (Value.unboxCont c3)
    st

let pop n st =
    let (a :: _) = st.stack
    st.stack <- List.tail (List.updateAt n a st.stack)
    st

let xchg n st =
    failIf (List.length st.stack <= n) "XCHG: Stack underflow"
    let stk = List.toArray st.stack
    let s0 = stk.[0]
    let sn = stk.[n]
    let stack' =
        Array.updateAt n s0 stk |>
        Array.updateAt 0 sn |>
        Array.toList
    st.stack <- stack'
    st

let True = -1
let False = 0

let ifelse st =
    let (fb :: tb :: f :: stack') = st.stack
    failIfNot (Value.isInt f) "IfElse: stack item must be integer"
    failIfNot (Value.isCont tb) "IfElse: stack item must be continuation"
    failIfNot (Value.isCont fb) "IfElse: stack item must be continuation"
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
    failIfNot (Value.isInt a1) "binop: stack item must be integer"
    failIfNot (Value.isInt a2) "binop: stack item must be integer"
    let (Int v1, Int v2) = (a1, a2)
    let res = f v1 v2
    st.stack <- (Int res) :: stack'
    st

let sub v1 v2 =
    v1 - v2

let add v1 v2 =
    v1 + v2

let gt v1 v2 =
    if v1 > v2 then -1 else 0

let eq v1 v2 =
    if v1 = v2 then -1 else 0

let inc st =
    let (a1 :: stack') = st.stack
    failIfNot (Value.isInt a1) "INC: stack item must be integer"
    // TODO: overflow check
    st.stack <- Int (Value.unboxInt a1 + 1) :: stack'
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
    let (t :: stack') = st.stack
    let v = Value.unboxTuple t
    failIf (List.length v <> n) "INDEX: Type check exception"
    st.stack <- v @ stack'
    st

let nil st =
    tuple 0 false st

// TPUSH (t x – t')
let tpush st =
    let (x :: t :: stack) = st.stack
    let ut = Value.unboxTuple t
    failIf (List.length ut = 255) "TPUSH: Type check exception"
    st.stack <- Tup (x :: ut) :: stack
    st

// INDEX k (t - t[k]), 0 <= k <= 15
let index k st =
    let (t :: stack') = st.stack
    let v = Value.unboxTuple t
    failIf (List.length v <= k) "INDEX: Range check exception"
    let elem = List.item k v
    st.stack <- elem :: stack'
    st

// SETINDEX k (t x – t')
let setindex k st =
    let (x :: t :: stack') = st.stack
    let v = Value.unboxTuple t
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
    failIfNot (Value.isSliceDict sD) "DICTUGET: sliceDict value expected"
    let D = Value.unboxDict sD
    failIfNot (Value.isInt i) "DICTUGET: Integer expected"
    // UFits n i check has to be done here as well
    match D.TryFind (Value.unboxInt i) with
        | None ->
            st.stack <- (Int 0) :: stack'
        | Some v ->
            st.stack <- (Int -1) :: v :: stack'
    st

// b i D n --> D'
let dictusetb st =
    let (n :: sD :: i :: b :: stack') = st.stack
    let D = Value.unboxDict sD
    failIfNot (Value.isInt i) "DICTUSET: Integer expected"
    failIfNot (Value.isBuilder b) "DICTUSET: Builder expected"
    let D' = D.Add (Value.unboxInt i, Slice (Value.unboxBuilder b))
    st.stack <- SliceDict D' :: stack'
    st

let calldict n st =
    failIf (st.cr.c3.IsNone) "CALLDICT: c3 is not initialized"
    st.cr.c3.Value.data.stack <- [Int n]
    call (st.cr.c3.Value) st

let jumpx st =
    let (cont :: stack') = st.stack
    failIfNot (Value.isCont cont) "JUMPX: continuation is expected"
    st.put_stack stack'
    jump (Value.unboxCont cont) st

let throwifnot n st =
    let (i :: stack') = st.stack
    failIfNot (Value.isInt i) "THROWIFNOT: Integer expected"
    if (Value.unboxInt i) = 0 then
        raise (TVMError ("TVM exception was thrown: " + string n))
    else
        ()
    st.stack <- stack'
    st

// this implementation is incorrect,
// it should transfer control to C3 cont, but
// for now we skip it
let throw nn st =
    raise (TVMError ("TVM exception was thrown: " + (string nn)))

let ifexec st =
    let (c :: f :: stack') = st.stack
    failIfNot (Value.isInt f) "IF: Integer expected"
    failIfNot (Value.isCont c) "IF: Continuation expected"
    if (Value.unboxInt f <> 0) then
        st.stack <- (c :: stack')
        execute st
    else
        st.stack <- stack'
        st

let ifjmp st =
    let (c :: f :: stack') = st.stack
    failIfNot (Value.isInt f) "IFJMP: Integer expected"
    failIfNot (Value.isCont c) "IFJMP: Continuation expected"
    st.put_stack stack'
    if (Value.unboxInt f <> 0) then
        jump (Value.unboxCont c) st
    else
        st

let setnumargs n st =
    let (cont :: stack') = st.stack
    failIfNot (Value.isCont cont) "SETNUMARGS: continuation expected"
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

let dispatch (i:Instruction) =
    match i with
        | PushNull ->
            pushnull
        | PushInt n ->
            pushint n
        | Push n ->
            push n
        | Dup ->
            push 0
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
        | Swap ->
            xchg 1
        | Equal ->
            binop eq
        | Greater ->
            binop gt
        | Inc ->
            inc
        | Add ->
            binop add
        | Sub ->
            binop sub
        | Execute ->
            execute
        | CallDict n ->
            calldict n
        | JumpX ->
            jumpx
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
        | StU cc ->
            stu cc
        | NewDict ->
            newdict
        | DictUGet ->
            dictuget
        | DictUSetB ->
            dictusetb
        | ThrowIfNot n ->
            throwifnot n
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
        | _ ->
            let msg = sprintf "unsupported instruction: %A" i
            raise (TVMError msg)

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
                           DumpStk;
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
                                     PushCont [Push 1; DumpStk] // c2 c1 (n>0?) f n
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
    let st = initialState [PushInt 100; Newc; StU 255]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Builder [Int 100]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testStu1 () =
    let st = initialState [PushInt 200; PushInt 100; Newc;
                           StU 255; StU 255]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (
            Some (Builder [Int 100; Int 200]),
            getResult finalSt
        )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDict0 () =
    let st = initialState [PushInt 10; // 10
                           Newc; // 10 b
                           StU 128; // b' (value)
                           PushInt 200; // b' 200(key)
                           NewDict; // b' 200 D
                           PushInt 10; // b' 200 D 10
                           DictUSetB] // D'
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (
            Some (SliceDict (Map [(200, Slice [Int 10])])),
            getResult finalSt
        )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDict1 () =
    let st = initialState [DictUGet] // k D' i -> v
    st.stack <- [Int 128;
                 SliceDict (Map [(200, Slice [Int 10])]); Int 200]
    try
        let finalSt = List.last (runVM st false)
        let ((Int 0) :: (Int -1) :: s1 :: t) = finalSt.stack
        printfn "%A" finalSt.stack
        Assert.AreEqual (
            (Int 0) :: (Int -1) :: [Slice [Int 10]],
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
        | StU n -> string(n) + " STU"
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
        | Depth -> "DEPTH"
        | XchgX -> "XCHGX"
        | DivMod -> "DIVMOD"
        | IndexVar -> "INDEXVAR"
        | SetIndexVar -> "SETINDEXVAR"
        | DumpStk -> "DUMPSTK"
        | _ ->
            raise (TVMError (sprintf "unsupported instruction: %A" i))

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
        (5, [Newc; StU 128])

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

[<Test>]
let testRearrangeIntegral0 () =
    let map_elem k st =
        let D s = index 0 (pushctr 7 s)
        let K s = push k s
        index 2 (throwifnot 5 (dictuget (pushint 128 (D (K st)))))
    let st = initialState []
    // a0 : ... : an : s h[a0: NGlobal n c, a1: NAp a0 a1', a2: NAp a1 a2', ...]
    let nglobal n c = Tup ([Int 0; Int n; Cont c])
    let nap a0 a1' = Tup ([Int 1; Int a0; Int a1'])
    let heap = Value.boxDict (Map [(0, nglobal 1 emptyContinuation); (1, nap 0 3000)])
    st.cr.c7 <- Tup [heap]
    st.put_stack [Int 0; Int 1]
    try
        let finalSt = rearrange 1 map_elem st
        printfn "%A" finalSt.stack
        Assert.AreEqual([Int 3000; Int 1], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

let setIndexVar t k v =
// SETINDEXVAR (t v k – t')
    t @ v @ k @ [SetIndexVar]

let indexVar t k =
// INDEXVAR (t k – x)
    t @ k @ [IndexVar]

let div x y =
    x @ y @ [DivMod; Drop]
let mod' x y =
    x @ y @ [DivMod; Swap; Drop]

let bucketSize = 5;
let arrayNew =
    [PushInt bucketSize; PushCont [PushInt 0]; Repeat;
     PushInt bucketSize; TupleVar; PushInt (bucketSize-1);
     PushCont [Dup]; Repeat; PushInt bucketSize; TupleVar; Dup]

// put (a:array) (k:index) (v:value) -> array
let arrayPut a k v =
    let i = div k [PushInt bucketSize]
    let j = mod' k [PushInt bucketSize]
    let t1 = indexVar a i
    let t2 = setIndexVar t1 j v
    setIndexVar a i t2

// get (a:array) (k:index) -> element
let arrayGet a k =
    // calculuate the corresponding bucket number
    // get the element from the bucket
    let i = div k [PushInt bucketSize]
    let j = mod' k [PushInt bucketSize]
    let t1 = indexVar a i
    indexVar t1 j

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
    let st = initialState (arrayGet arrayNew [PushInt 1])
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
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
    let a1 = arrayPut arrayNew [PushInt 1] [PushInt 600]
    let a2 = arrayGet a1 [PushInt 1]
    let st = initialState a2
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
let testArrayGetPut2 () =
    // x ... t'
    let saveArray t = t @ [Depth; Dec; XchgX; Drop]
    // x ... -> x ... x
    let loadArray = [Depth; Dec; Pick]
    // a[1] = 600; a[2] = 700; a[3] = 800;
    let a1 = arrayPut loadArray [PushInt 1] [PushInt 600]
    let a2 = arrayPut a1 [PushInt 2] [PushInt 700]
    let a3 = arrayGet loadArray [PushInt 1]
    let st = initialState ( (saveArray arrayNew) @
                            (saveArray a2) @
                            arrayGet loadArray [PushInt 1] @ [DumpStk]
                            )
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 600), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testArrayGetPut3 () =
    // x ... t'
    let saveArray t = t @ [Depth; Dec; XchgX; Drop]
    // x ... -> x ... x
    let loadArray = [Depth; Dec; Pick]
    // a[1] = 600; a[2] = 700; a[3] = 800;
    let a1 = arrayPut loadArray [PushInt 1] [PushInt 600]
    let a2 = arrayPut a1 [PushInt 2] [PushInt 700]
    let a3 = arrayPut a2 [PushInt 3] [PushInt 800]
    let a4 = arrayGet loadArray [PushInt 2] // 700
    let a5 = arrayPut loadArray [PushInt 3] a4 // a[3] = 700
    let st = initialState ( (saveArray arrayNew) @
                            (saveArray a3) @
                            saveArray a5 @
                            arrayGet loadArray [PushInt 3]
                            )
    try
        dumpFiftScript "testArrayGetPut3.fif" (outputFift st)
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 700), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

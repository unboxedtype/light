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
    | Execute
    | CallDict of n:int
    | JumpX
    | DumpStk
    | Nop
    | Tuple of n:int
    | Nil
    | PushNull
    | Index of k:int
    | Untuple of n:int
    | SetIndex of k:int
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
    static member isTuple = function | Tup _ -> true | _ -> false
    static member unboxInt = function | Int x -> x | _ -> raise (TVMError "unbox")
    static member unboxCont = function | Cont x -> x | _ -> raise (TVMError "unbox")
    static member unboxTuple = function | Tup x -> x | _ -> raise (TVMError "unbox")
    static member unboxBuilder = function | Builder x -> x | _ -> raise (TVMError "unbox")
    static member boxInt = fun n -> Int n

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
      mutable c7:Value list; }
    static member Default = {
        c0 = None; c3 = None; c7 = []
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
    failIf (List.length stack' <= n) "PUSH: stack underflow"
    let sn = List.item n stack'
    st.stack <- sn :: stack'
    st

let pushctr n st =
    let stack =
        if n = 7 then
            (Tup st.cr.c7) :: st.stack
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
        st.cr.c7 <- Value.unboxTuple c7
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

let tuple n st =
    let stk = st.stack
    failIf (n < 0) "TUPLE: incorrect argument"
    failIf (n > 15) "TUPLE: incorrect argument"
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
    tuple 0 st

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

let mkDict slice : Map<int,Value> =
    match slice with
        | Null ->
            Map []
        | SliceDict d ->
            d
        | _ ->
            raise (TVMError "mkDict: dict has to be presented as sliceDict")

// i D n – x -1 or 0
let dictuget st =
    let (n :: sD :: i :: stack') = st.stack
    let D = mkDict sD
    failIfNot (Value.isInt i) "DICTUGET: Integer expected"
    // UFits n i check has to be done here as well
    let v' =
        match D.TryFind (Value.unboxInt i) with
            | None ->
                raise (TVMError "Key not found")
            | Some v ->
                v // this is a slice
    st.stack <- v' :: stack'
    st

// b i D n --> D'
let dictusetb st =
    let (n :: sD :: i :: b :: stack') = st.stack
    let D = mkDict sD
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
            pop 0
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
            tuple n
        | Nil ->
            nil
        | Index k ->
            index k
        | Untuple n ->
            untuple n
        | SetIndex k ->
            setindex k
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
        | SetNumArgs n ->
            setnumargs n
        | _ ->
            raise (TVMError "unsupported instruction")

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
    st.stack <- [Int 255;
                 SliceDict (Map [(200, Slice [Int 10])]); Int 200]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Slice [Int 10]), getResult finalSt)
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
        | PushCont c -> "<{ " + String.concat "\n" (List.map instrToFift c) + " }> PUSHCONT"
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

// -------------------------------
// encoding for GMachine.Node type
// -------------------------------
// type Node =
//     | NNum of v: int
//     | NAp of f: Addr * a: Addr // f(a)
//     | NGlobal of args: int * code: GmCode
//     | NInd of v: Addr  // indirection node
//     // data type constructor with n params
//     | NConstr of int * Addr list

// (tag, args)
// NNum v = (0, v)
// NAp (f, v) = (1, f, v)
// NGlobal (n, code) = (2, n, code); code is a slice
// NInd v = (3, v)
// NConstr (n, [a]) = (4, n, (a0, a1, ...))

let compileToTVM (c:GMachine.GmCode) =
    []

let encodeNode (n:GMachine.Node) : Value =
    match n with
        | GMachine.NNum v ->
            Builder [Int 0; Int v]
        | GMachine.NAp (f, a) ->
            Builder [Int 1; Int f; Int a]
        | GMachine.NGlobal (n, c) ->
            let c' = compileToTVM c
            Builder [Int 2; Int n; Cell c']
        | GMachine.NInd v ->
            Builder [Int 3; Int v]
        | GMachine.NConstr (n, vs) ->
            Builder ([Int 4; Int n] @ (List.map Value.boxInt vs))
        | _ ->
            raise (TVMError "encodeNode: unknown type")

let compileValue v =
    match v with
        | Int n ->
            [PushInt n]
        | _ ->
            raise (TVMError "unsupported value type")

// Generates code that constructs the needed Builder object
// on the TVM stack. It does not get converted into Cell intentionally,
// not to pay for serialization, which is unnecessary in our case.
let compileBuilder (b:Value) =
    failIfNot (Value.isBuilder b) "compileBuilder: builder expected"
    let l = Value.unboxBuilder b
    // Builder [Int 2; Int 3]
    // -->
    // PUSHINT 3; PUSHINT 2; NEWC; STU 128; STU 128;
    let vals =
        List.map compileValue (List.rev l) |> List.concat
    vals @ [Newc] @ (List.replicate (List.length l) (StU 128))

module TVM

open NUnit.Framework
open System
open System.Collections.Generic

exception TVMError of string

type Instruction =
    | Push of n:int
    | Pop of n:int
    | Xchg of n:int     // Xchg s0, s(i)
    | Greater
    | PushInt of n:int
    | PushCont of c:Code
    | IfElse
    | Add
    | Sub
    | Execute
and Code =
    Instruction list

// codepage number is an unsigned integer
type CodePage =
    int

type Action =
    SendMsg

type Cell =
    Cell

type Value =
    | Int of v:int
    | Tuple of v:Value list
    | Null
    | Cont of v:Continuation
and Continuation = {
    mutable code:Code;
    mutable stack:Stack;
}
and Stack =
    Value list

let TVM_True = (Int -1)
let TVM_False = (Int 0)

let isInt a =
    match a with
        | Int v ->
            true
        | _ ->
            false

let isCont a =
    match a with
        | Cont v ->
            true
        | _ ->
            false

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

let emptyContinuation = {
    code = []; stack = [];
}
let emptyCont = Cont emptyContinuation

type TVMState = {
    mutable cc:Continuation;
}

[<OneTimeSetUp>]
let Setup () =
    ()

let initialState (code:Code) : TVMState =
    { cc = { code = code; stack = [] } }

let execute st =
    let stack = st.cc.stack
    failIf (List.length stack < 1) ("EXECUTE: stack underflow")
    let (c :: stack') = stack
    match c with
        | Cont v ->
            let code' = st.cc.code
            st.cc.stack <- stack'
            st.cc.code <- (v.code @ code')
            st
        | _ ->
            raise (TVMError "EXECUTE: stack item must be continuation")

let pushcont c st =
    let stack' = st.cc.stack
    let cont = { code = c ; stack = []; }
    st.cc.stack <- (Cont cont) :: stack'
    st

let pushint n st =
    let stack' = st.cc.stack
    st.cc.stack <- (Int n) :: stack'
    st

let push n st =
    let stack' = st.cc.stack
    failIf (List.length stack' <= n) "PUSH: stack underflow"
    let sn = List.item n stack'
    st.cc.stack <- sn :: stack'
    st

let pop n st =
    let (a :: _) = st.cc.stack
    st.cc.stack <- List.tail (List.updateAt n a st.cc.stack)
    st

let xchg n st =
    failIf (List.length st.cc.stack <= n) "XCHG: Stack underflow"
    let stk = List.toArray st.cc.stack
    let s0 = stk.[0]
    let sn = stk.[n]
    let stack' =
        Array.updateAt n s0 stk |>
        Array.updateAt 0 sn |>
        Array.toList
    st.cc.stack <- stack'
    st

let ifelse st =
    let (fb :: tb :: f :: stack') = st.cc.stack
    failIfNot (isInt f) "IfElse: stack item must be integer"
    failIfNot (isCont tb) "IfElse: stack item must be continuation"
    failIfNot (isCont fb) "IfElse: stack item must be continuation"
    let (Cont true_branch_cont) = tb
    let (Cont false_branch_cont) = fb
    match f with
        | TVM_False ->
            st.cc.code <- st.cc.code @ false_branch_cont.code
        | _ ->
            st.cc.code <- st.cc.code @ true_branch_cont.code
    st.cc.stack <- stack'
    st

let binop f st =
    let (a2 :: a1 :: stack') = st.cc.stack
    failIfNot (isInt a1) "binop: stack item must be integer"
    failIfNot (isInt a2) "binop: stack item must be integer"
    let (Int v1, Int v2) = (a1, a2)
    let res = f v1 v2
    st.cc.stack <- (Int res) :: stack'
    st

let sub v1 v2 =
    v1 - v2

let add v1 v2 =
    v1 + v2

let gt v1 v2 =
    if v1 > v2 then -1 else 0

let dispatch (i:Instruction) =
    match i with
        | PushInt n ->
            pushint n
        | Push n ->
            push n
        | Pop n ->
            pop n
        | Xchg n ->
            xchg n
        | Greater ->
            binop gt
        | Add ->
            binop add
        | Sub ->
            binop sub
        | PushCont c ->
            pushcont c
        | Execute ->
            execute
        | IfElse ->
            ifelse
        | _ ->
            raise (TVMError "unsupported instruction")

let step (st:TVMState) : TVMState =
    match (st.cc.code) with
        | [] ->
            st
        | i :: code' ->
            printfn "Executing %A" i
            st.cc.code <- code'
            dispatch i st

let printTerm term =
    let str = sprintf "%A" term
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

let rec runVM st (trace:bool) =
    let st' = step st
    match st'.cc.code with
        | [] ->
            // if we managed to get here, everything is good.
            // Error code 0 is put on the stack
            st'.cc.stack <- (Int 0) :: (st'.cc.stack)
            [st']
        | _ ->
            st' :: (runVM st' trace)

let getResult st : Value option =
    match st.cc.stack with
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
    let st = initialState [PushCont [PushInt 10]; Execute]
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
    st.cc.stack <- [Int 7]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 6), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater3 () =
    // let f n g =
    // if n > 10 then (g (n - 1)) else n
    let st = initialState [PushInt 12;
                           PushCont [Push 1;    // n f n
                                     PushInt 10; // n f n 10
                                     Greater; // n f (n > 10?)
                                     PushCont [Push 1; // n f n
                                               PushInt 1; // n f n 1
                                               Sub;  // n f (n-1)
                                               Push 1; // n f (n-1) f
                                               Execute];
                                     PushCont [Push 1] // n f (n>10?) c1 c2
                                     IfElse];
                           Push 0;
                           Execute
                           ]
    st.cc.stack <- []
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

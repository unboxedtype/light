module TVM

open NUnit.Framework
open System
open System.Collections.Generic

exception TVMError of string

type Instruction =
    | Push of n:int
    | Pop of n:int
    | Pushint of n:int
    
// codepage number is an unsigned integer
type CodePage =
    int

type Action =
    SendMsg

type Code =
    Instruction list

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
    mutable save:SaveList option;
    cp:CodePage;
    nargs:int;
}
and Stack =
    Value list
and SaveList =
    ControlRegs
and ControlRegs = {
    c0:Continuation; // next 'return' continuation
    c1:Continuation; // alt continuation
    c2:Continuation; // exception handler
    c3:Continuation; // current dictionary of functions
    c4:Cell option; // persistent data
    c5:Action list; // list of actions
    c7:Value list; // root of temp data
}
    
let emptyCont = {
    code = [];
    stack = [];
    save = None;
    cp = 0;
    nargs = 0
}

type GasLimit = {
    gl:int;
    gm:int;
    gr:int;
    gc:int
}

type TVMState = {
    mutable stack:Stack;
    mutable ctrls:ControlRegs;
    mutable cc:Continuation;
    cp:CodePage;
    mutable gas:GasLimit
}

[<OneTimeSetUp>]
let Setup () =
    ()

let initialState (code:Code) : TVMState =
    let ctrls = {
        c0 = emptyCont;
        c1 = emptyCont;
        c2 = emptyCont;
        c3 = emptyCont;
        c4 = None;
        c5 = [];
        c7 = []
    }
    let cc = {
        code = code;
        stack = [];
        save = None;
        cp = 0;
        nargs = 0
    }
    let gas = {
        gl = 1000000;
        gc = 0;
        gr = 1000000;
        gm = 1000000
    }
    
    { stack = [ Int(0) ]; // push 0 at start
      ctrls = ctrls;
      cc = cc;
      cp = 0;
      gas = gas }

let pushint n st =
    let stack' = st.cc.stack
    st.cc.stack <- (Int n) :: stack'
    st

let push n st =
    let stack' = st.cc.stack
    if List.length stack' <= n then
        raise (TVMError "PUSH: stack underflow")
    let sn = List.item n stack'
    st.cc.stack <- sn :: stack'
    st

let pop n st =
    let (a :: stack') = st.cc.stack
    let stack'' = List.insertAt n a stack'
    st.cc.stack <- stack''
    st
    
let dispatch (i:Instruction) =
    match i with
        | Pushint n ->
            pushint n
        | Push n ->
            push n
        | Pop n ->
            pop n
        | _ ->
            raise (TVMError "unsupported instruction")
    
let step (st:TVMState) : TVMState =
    match (st.cc.code) with
        | [] ->
            st
        | i :: code' ->
            dispatch i st
            st.cc.code <- code'
            st

let printTerm term =
    let str = sprintf "%A" term
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

let rec runVM st (trace:bool) =
    let st' = step st
    match st'.cc.code with
        | [] ->
            [st']
        | _ ->
            st' :: (runVM st' trace)

let getResult st =
    List.head (st.cc.stack)

[<Test>]
let testInitState () =
    let st = initialState []
    Assert.AreEqual (st, step st)

[<Test>]
let testPushint0 () =
    let st = initialState [Pushint 10]
    let finalSt = List.last (runVM st false)
    Assert.AreEqual ( Int 10, getResult finalSt )

[<Test>]
let testPushint1 () =
    let st = initialState [Pushint 10; Pushint 20]
    let finalSt = List.last (runVM st false)
    Assert.AreEqual ( Int 20, getResult finalSt )

[<Test>]
let testPush0 () =
    let st = initialState [Pushint 10; Pushint 20; Push 1]
    try
        let states = runVM st true
        let finalSt = List.last states
        Assert.AreEqual ( Int 10, getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPush1 () =
    let st = initialState [Pushint 10; Pushint 20; Push 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Int 20, getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)        

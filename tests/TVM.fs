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
    | Add
    | Sub
    | Execute
    | DumpStk
    | Nop
    | Tuple of n:int
    | Nil
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
and Continuation = {
    mutable code:Code;
    mutable stack:Stack;
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

let emptyContinuation = {
    code = []; stack = []
}
let emptyCont = Cont emptyContinuation

type TVMState = {
    mutable cc:Continuation;
    mutable c7:Value;
}

[<OneTimeSetUp>]
let Setup () =
    ()

let printTerm term =
    let str = sprintf "%A" term
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

let initialState (code:Code) : TVMState =
    { cc = { code = code; stack = [] }; c7 = Tup [] }

let mkBuilder vs =
    Builder vs

let unboxBuilder b =
    match b with
        | Builder vs ->
            vs
        | _ ->
            raise (TVMError "unboxBuilder on non-builder value")

let mkCell b =
    Cell (unboxBuilder b)

let stu cc st =
    let (b :: x :: stack') = st.cc.stack
    failIfNot (Value.isBuilder b) "STU: not a builder"
    failIfNot (Value.isInt x) "STU: not an integer"
    let vs = unboxBuilder b
    // failIf (x > float 2 ** cc) "STU: Range check exception"
    st.cc.stack <- mkBuilder (vs @ [x]) :: stack'
    st

let newc st =
    let stack = st.cc.stack
    st.cc.stack <- (mkBuilder []) :: stack
    st

let endc st =
    let (b :: stack) = st.cc.stack
    failIfNot (Value.isBuilder b) "ENDC: not a builder"
    st.cc.stack <- (mkCell b) :: stack
    st


let execute st =
    let stack = st.cc.stack
    failIf (List.length stack < 1) "EXECUTE: stack underflow"
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
    let cont = { code = c ; stack = [] }
    st.cc.stack <- (Cont cont) :: stack'
    st

let pushint n st =
    let stack' = st.cc.stack
    st.cc.stack <- (Int n) :: stack'
    st

let pushnull st =
    let stack' = st.cc.stack
    st.cc.stack <- Null :: stack'
    st

let push n st =
    let stack' = st.cc.stack
    failIf (List.length stack' <= n) "PUSH: stack underflow"
    let sn = List.item n stack'
    st.cc.stack <- sn :: stack'
    st

let pushctr n st =
    failIf (n <> 7) "PUSHCTR: only c7 is supported"
    let stack = st.c7 :: st.cc.stack
    st.cc.stack <- stack
    st

let popctr n st =
    failIf (n <> 7) "POPCTR: only c7 is supported"
    let (c7 :: stack) = st.cc.stack
    failIfNot (Value.isTuple c7) "POPCTR: c7 is a tuple"
    st.cc.stack <- stack
    st.c7 <- c7
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

let unboxInt f =
    match f with
        | Int n ->
            n
        | _ ->
            raise (TVMError "unboxInt on non-integer value")

let unboxTuple t =
    match t with
        | Tup l ->
            l
        | _ ->
            raise (TVMError "unboxTuple on non-tuple value")

let True = -1
let False = 0

let ifelse st =
    let (fb :: tb :: f :: stack') = st.cc.stack
    failIfNot (Value.isInt f) "IfElse: stack item must be integer"
    failIfNot (Value.isCont tb) "IfElse: stack item must be continuation"
    failIfNot (Value.isCont fb) "IfElse: stack item must be continuation"
    let (Cont true_branch_cont) = tb
    let (Cont false_branch_cont) = fb
    let code' =
        if f = TVM_True then
            st.cc.code @ true_branch_cont.code
        else
            st.cc.code @ false_branch_cont.code
    st.cc.code <- code'
    st.cc.stack <- stack'
    st

let binop f st =
    let (a2 :: a1 :: stack') = st.cc.stack
    failIfNot (Value.isInt a1) "binop: stack item must be integer"
    failIfNot (Value.isInt a2) "binop: stack item must be integer"
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

let dumpstk st =
    let stk = st.cc.stack
    printfn "STACK: %A"  stk
    st

let nop st =
    st

let tuple n st =
    let stk = st.cc.stack
    failIf (n < 0) "TUPLE: incorrect argument"
    failIf (n > 15) "TUPLE: incorrect argument"
    failIf (List.length stk < n) "TUPLE: Stack underflow"
    let args = List.rev (List.take n stk)
    let t = Tup args
    st.cc.stack <- t :: (List.skip n stk)
    st

let untuple n st =
    let (t :: stack') = st.cc.stack
    let v = unboxTuple t
    failIf (List.length v <> n) "INDEX: Type check exception"
    st.cc.stack <- v @ stack'
    st

let nil st =
    tuple 0 st

// TPUSH (t x – t')
let tpush st =
    let (x :: t :: stack) = st.cc.stack
    let ut = unboxTuple t
    failIf (List.length ut = 255) "TPUSH: Type check exception"
    st.cc.stack <- Tup (x :: ut) :: stack
    st

// INDEX k (t - t[k]), 0 <= k <= 15
let index k st =
    let (t :: stack') = st.cc.stack
    let v = unboxTuple t
    failIf (List.length v <= k) "INDEX: Range check exception"
    let elem = List.item k v
    st.cc.stack <- elem :: stack'
    st

// SETINDEX k (t x – t')
let setindex k st =
    let (x :: t :: stack') = st.cc.stack
    let v = unboxTuple t
    failIf (List.length v <= k) "INDEX: Range check exception"
    let v' = List.updateAt k x v
    st.cc.stack <- (Tup v') :: stack'
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

// i D n – x −1 or 0
let dictuget st =
    let (n :: sD :: i :: stack') = st.cc.stack
    let D = mkDict sD
    failIfNot (Value.isInt i) "DICTUGET: Integer expected"
    // UFits n i check has to be done here as well
    let v' =
        match D.TryFind (unboxInt i) with
            | None ->
                raise (TVMError "Key not found")
            | Some v ->
                v // this is a slice
    st.cc.stack <- v' :: stack'
    st

// b i D n --> D'
let dictusetb st =
    let (n :: sD :: i :: b :: stack') = st.cc.stack
    let D = mkDict sD
    failIfNot (Value.isInt i) "DICTUSET: Integer expected"
    failIfNot (Value.isBuilder b) "DICTUSET: Builder expected"
    let D' = D.Add (unboxInt i, Slice (unboxBuilder b))
    st.cc.stack <- SliceDict D' :: stack'
    st

let dispatch (i:Instruction) =
    match i with
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
            xchg 0
        | Greater ->
            binop gt
        | Add ->
            binop add
        | Sub ->
            binop sub
        | Execute ->
            execute
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
        | DictUSet ->
            dictusetb
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
    st.cc.stack <- [Int 7]
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
    st.cc.stack <- [Int 12]
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
    let st = initialState [PushInt 200; PushInt 100; Newc; StU 255; StU 255]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Builder [Int 100; Int 200]), getResult finalSt)
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
        Assert.AreEqual (Some (SliceDict (Map [(200, Slice [Int 10])])), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDict1 () =
    let st = initialState [DictUGet] // k D' i -> v
    st.cc.stack <- [Int 255;  SliceDict (Map [(200, Slice [Int 10])]); Int 200]
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
    let st = initialState [PushCtr 7; PushInt 200; TPush; PopCtr 7; PushCtr 7]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Int 200]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

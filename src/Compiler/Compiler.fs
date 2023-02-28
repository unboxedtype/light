module Compiler

// Debug switch turns on excessive logging
// Turn it off to produce gas-optimal executables
let debug = false

// Incomplete pattern matches on this expression.
#nowarn "25"

open System
open System.Collections.Generic

open type TVM.Instruction
open type TVM.Value
open type TVM.SValue

type RuntimeErrors =
    | GlobalNotFound = 10
    | HeapNodeNotFound = 11
    | HeapNodeWrongTag = 12
    | CaseNotFound = 13
    | PartialApplication = 14

type RuntimeGlobalVars =
    | Heap = 1
    | HeapCounter = 2
    | Globals = 3
    | UnwindCont = 4
    | UnwindSelector = 5

// v:builder k:uint D:cell -> D'
let dictSet =
    [PushInt 128; DictISetB]

// k D -> D[k] -1 | 0
let dictGet =
    [PushInt 128; DictIGet]

// _ -> hc
let getHeapCounter =
    [GetGlob (int RuntimeGlobalVars.HeapCounter)]

// _ -> g
let getGlobals =
    [GetGlob (int RuntimeGlobalVars.Globals)]

// _ -> h
let getHeap =
    [GetGlob (int RuntimeGlobalVars.Heap)]

// n -> _
let putHeapCounter =
    [SetGlob (int RuntimeGlobalVars.HeapCounter)]

// n -> _
let putHeap =
    [SetGlob (int RuntimeGlobalVars.Heap)]

// g -> _
let putGlobals =
    [SetGlob (int RuntimeGlobalVars.Globals)]


let printStack (s:string) =
    if debug then
        [PrintStr s.[0..14]; DumpStk]
    else
        []

// 1. allocate address for the node
// 2. store the node in the heap at that address
// 3. return the new heap on the stack
// node -> a , where heap[a] := n
let heapAlloc =
    (printStack "heapAlloc") @
    getHeapCounter @ // node k
    [Inc; Dup] @ // node k' k'
    putHeapCounter @ // node k'
    getHeap @ // node k' a
    [Xchg 2] @ // a k' node
    [Push 1] @ // a k' node k'
    [RollRev 3] @ // k' a k' node
    TVM.arrayPut @ // k' a'
    putHeap // k'

// k -> heap[k] or exception
let heapLookup =
    (printStack "heapLookup") @
    getHeap @ // k h
    [Swap] @ // h k
    TVM.arrayGetWithCode @
    [ThrowIfNot (int RuntimeErrors.HeapNodeNotFound)]

// (T, ...) -> (T, ...) if T = tag,
// or throws otherwise
let checkTag tag =
    if debug then
        [Dup;     // node node
         Index 0; // node tag'
         PushInt tag; // node tag' tag
         Equal;   // node (tag'==tag?)
         ThrowIfNot (int RuntimeErrors.HeapNodeWrongTag)]
    else
        []

let doUnwind =
    [GetGlob (int RuntimeGlobalVars.UnwindCont); Execute]

// n heap[n]  (heap[n] = (NNum _ n)
let mapUnwindNNum : TVM.Code =
    (printStack "Unwind NNum") @
    [Drop] // n

// n heap[n]  (heap[n] = (NAp, _, f, arg) )
let mapUnwindNAp : TVM.Code =
    (printStack "Unwind NAp") @
    [Index 2] @ // n f
    doUnwind

// n heap[n]  (heap[n] = (NInd _ m)
let mapUnwindNInd : TVM.Code =
    (printStack "Unwind NInd") @
    [Index 2; // n m
     Swap; // m n
     Drop] @ // m
     doUnwind

// n heap[n]  (heap[n] = (NConstr _ tag [a1,...,an])
let mapUnwindNConstr : TVM.Code =
    (printStack "Unwind NConstr") @
    [Drop] // n

// an .. a0   h[a0:NGlobal n c; a1: NAp a0 a1', a2:NAp a1 a2'...]
// -->
// an, an', ..., a2', a1'
// Please note that in case of n = 0 the result will be 'a0'
// so we keep the root node at stack at all times
let unwindRearrange () : TVM.Code =
    [GetGlob 9; // an .. a0 n
     Pick;  // an .. a0 an
     (* DumpStk; *)
     GetGlob 9; // an ... a0 an n
     RollRevX; // an an .. a1 a0
     Drop;
     GetGlob 9; // an an .. a1 n  (note: n = args count )
     PushCont (heapLookup @  // an an .. (NAp _ a0 a1')
               checkTag (int GMachine.NodeTags.NAp) @
               [Index 3;   // an an .. a1'
                GetGlob 9; // an an .. a1' n
                Dec;       // an an .. a1' (n-1)
                RollRevX]);// an a1' an .. a2
     // an an .. a1 n c
     Repeat] // an an' .. a1'

// an .. a1 a0 heap[n]  (heap[n] = (NGlobal _ n c)
let mapUnwindNGlobal : TVM.Code =
    (printStack "unwind NGlobal") @
    [Dup;        // an .. a1 a0 heap[n] heap[n]
     Index 2;    // an .. a0 heap[n] NGlobal.n
     Depth; Dec; Dec; Dec; // ... a0 heap[a0] NGlobal.n k   (k = number of passed arguments)
     Swap;
     Less;        // an .. a0 heap[a0] k<NGlobal.n?
     ThrowIf (int RuntimeErrors.PartialApplication); // ... a0 heap[a0]
     Dup; // an ... a0 heap[a0] heap[a0]
     Index 2; SetGlob 9; // an ... a0 heap[a0]  (c7[9] = nglobal.a0)
     Index 3; SetGlob 10] @ // an ... a0       (c7[10] = nglobal.c)
     (unwindRearrange ()) @ // an ... a0
     [GetGlob 10; Execute]

// If the current top stack element is:
//  - a value, i.e. a number or a saturated constructor,
//    then switch to the frame (instructions,stack pair) located on top of the dump.
//  - an Indirection node, then put the indirection
//    address on the stack and Unwind further
//  - a global function, then put the parameters
//    of the function onto the stack and execute the function instructions.
//    If there are not enough arguments on the stack (partial application), then
//    switch to dump code/stack pair
//  - an application node, then put the function address (i.e. first element
//    of the application) on the stack and Unwind further
// n

// Put the n-th element of the stack on top of the stack;
// 0 denotes the current top value of the stack.
let mapPush (n:int) : TVM.Code =
    (printStack (sprintf "mapPush %d" n)) @
    [Push n]

// Remove n consecutive elements from the stack
let mapPop (n:int) : TVM.Code =
    (printStack (sprintf "mapPop %d" n)) @
    [BlkDrop n]

// Remove n elements from the stack, starting from the second
// element of the stack, i.e. leaving the top stack element inplace.
// ... sn .. s2 s1 s -> ...  s
let mapSlide (n:int) : TVM.Code =
    (printStack (sprintf "mapSlide %d" n)) @
    [RollRev n; BlkDrop n]

// Extract the address of a function with id = n from the globals
// and put it on the stack; if the function with the given
// name n is not found, raise exception.
let mapPushglobal (n:int) : TVM.Code =
    (printStack (sprintf "mapPushglobal %d" n)) @
    [PushInt n] @
    getGlobals @
    [PushInt 128;       // n D 128
     DictIGet;        // D[n] -1 | 0
     ThrowIfNot (int RuntimeErrors.GlobalNotFound);
     Ldi 128; // n s'
     Ends] // n

// Allocate a node for the given integer on the heap and put the
// address of that node on the stack;
let mapPushint (n:int) : TVM.Code =
    (printStack (sprintf "mapPushint %d" n)) @
    [PushInt (int GMachine.NodeTags.NNum);
     PushCont mapUnwindNNum;
     PushInt n;
     Tuple 3] @
    heapAlloc

// Lookup arguments on the heap and do the corresponding arithmetic
// operation, placing the boxed result on the stack
// n2 n1 -> n3, where heap[n3] = heap[n1] OP heap[n2]
let binaryOperation (op:TVM.Code) : TVM.Code =
    (printStack (sprintf "binaryOperation %A" op)) @
    heapLookup @ // n2 (0, NNum1)
    checkTag (int GMachine.NodeTags.NNum) @
    [Third] @   // n2 NNum1  // (tag,_,NNum1)
    [Swap] @     // NNum1 n2
    heapLookup @ // NNum1 heap[n2]
    checkTag (int GMachine.NodeTags.NNum) @
    [Third] @   // NNum1 NNum2
    op @  // op(n1,n2)
    [PushInt (int GMachine.NodeTags.NNum); Swap] @ // nnum op(n1,n2)
    [PushCont mapUnwindNNum; Swap] @ // nnum cont op(n1,n2)
    [Tuple 3] @  // (nnum, cont, op(heap[n1], heap[n2])), NNum tag = 0
    heapAlloc    // n3

let mapAdd () : TVM.Code =
    binaryOperation [Add]

// n1 n2 -> n3, where heap[n3] = heap[n1] - heap[n2]
let mapSub () : TVM.Code =
    binaryOperation [Sub]

let mapMul () : TVM.Code =
    binaryOperation [Mul]

let mapDiv () : TVM.Code =
    binaryOperation [Div]

let mapEqual () : TVM.Code =
    binaryOperation [Equal]

let mapGreater () : TVM.Code =
    binaryOperation [Greater]

let mapLess () : TVM.Code =
    binaryOperation [Less]

// Allocate a node for function application on the heap and
// put the address of that node on the stack
// a1 f -> a2 , where heap[a3] = NAp (f, a1)
let mapMkap () : TVM.Code =
    (printStack "mapMkap") @
    [PushInt (int GMachine.NodeTags.NAp);  // a1 f 1
     RollRev 2;  // 1 a1 f
     Swap;       // 1 f a1
     PushCont mapUnwindNAp; // 1 f a1 c
     RollRev 2; // 1 c f a1
     Tuple 4] @ // (1, f, a1)
    heapAlloc   // a2

// Change the node pointed by the n-th + 1 element of the stack
// to the Indirection node pointing to the node with the address
// located on top of the stack.
// .. an .. a1 a -> .. an .. a1 , heap[an] := NInd a
let mapUpdate (n:int) : TVM.Code =
    (printStack (sprintf "mapUpdate %d" n)) @
    [PushInt (int GMachine.NodeTags.NInd); // a1 a 3   (note: 3 = NInd tag)
     Swap; // an .. a1 3 a
     PushCont mapUnwindNInd; Swap; // an .. a1 3 c a
     Tuple 3;     // an .. a1 (3,c,a)
     Push (n+1)] @    // an .. a1 (3,c,a) an
    getHeap @     // an .. a1 (3,c,a) an heap
    [Xchg 2] @    // an .. a1 heap an (3,c,a)
    TVM.arrayPut @ // .. an .. a1 heap'
    putHeap       // an .. a1

// -> a1 a2 .. an
// Allocate n dummy nodes on the heap and return put
// their addresses on the stack
let mapAlloc (n:int) : TVM.Code =
    (printStack (sprintf "mapAlloc %d" n)) @
    [PushInt n; PushCont ([PushNull] @ heapAlloc); Repeat]

let rec xchgs l acc =
    let len = List.length l
    if len > 1 then
        let (s,e) = (List.head l, List.last l)
        let next = List.take (len-2) (List.tail l)
        xchgs next ((s,e) :: acc)
    else
        acc

// Put the (address of) boxed constructor object onto the stack
// an .. a1 -> a  , where heap[a] = NConstr(tag, [a1, ... an])
let mapPack (tag:int) (n:int) : TVM.Code =
    (printStack (sprintf "mapPack %d %d" tag n)) @
    (let pairs = xchgs [0..(n-1)] []
    [for (i,j) in pairs -> Xchg2 (i,j)]) @
    [PushInt n; TupleVar] @ // (a1,...,an)
    [PushInt (int GMachine.NodeTags.NConstr); Swap; PushInt tag; Swap;
     PushCont mapUnwindNConstr; RollRev 2; Tuple 4] @ // (4, tag, (a1,...,an))
    heapAlloc

// Deconstruct the constructor object located on the stack,
// having n arguments. All arguments (their addresses) are placed onto the stack.
// n -> a1 .. am  , where heap[n] = (NConstr, _, tag, [a1..am])
let mapSplit (n:int) : TVM.Code =
    (printStack (sprintf "mapSplit %d" n)) @
    heapLookup @    // heap[n]
    checkTag (int GMachine.NodeTags.NConstr) @
    // (4, tag, (a1am))
    [Index 3; Dup] @  // (a1am) (a1am)
    [TLen] @        // (a1am) m
    [UntupleVar] @   // a1 .. am
    (let pairs = xchgs [0..(n-1)] []
     [for (i,j) in pairs -> Xchg2 (i,j)])


// Extract the constructor object's tag and transfer
// control the code given in the corresponding case branch.
// Here, cs is a case selector compiled in a form of a continuation
// that checks the given stack number against possible choices
// and transfer control to the found case; if no case suits,
// throws exception.
// n -> n
let mapCasejump (cs:TVM.Code) : TVM.Code =
    (printStack (sprintf "mapCasejump %A" cs)) @
    [Dup] @             // n n
    heapLookup @        // n heap[n]
    checkTag (int GMachine.NodeTags.NConstr) @
    [Index 2] @         // n tag : this is the tag we should find in cs
    [PushCont cs; Execute] // n

// If the top stack element evaluates to True, transfer control
// to the t branch; else to the f branch
// n -> _
let mapCond (t:TVM.Code) (f:TVM.Code) : TVM.Code =
    (printStack (sprintf "mapCond %A %A" t f)) @
    heapLookup @    // heap[n] ( heap[n] = (NNum,_,num) )
    checkTag (int GMachine.NodeTags.NNum) @
    [Index 2] @     // num
    [PushCont t] @  // num t
    [PushCont f] @  // num t f
    [CondSel] @     // t or f
    [Execute]

let mapUnwind () : TVM.Code =
    // we need to duplicate n (object heap address) because
    // several unwind routines need it (unwindNNum, unwindNAp,
    // unwindNConstr)
    (printStack "Unwind") @
    [Dup] @ // n n
    heapLookup @
    [Dup; Index 1; JmpX] // at the 1st position we have a continuation we need to jump to

let mapEval () : TVM.Code =
    (printStack "Eval") @
    [GetGlob (int RuntimeGlobalVars.UnwindCont)] @
//  [SetNumArgs 1] @
    [Execute]

let mapDumpstk () : TVM.Code =
    [DumpStk]

let rec compileInstr (i:GMachine.Instruction): TVM.Code =
    // some GMachine.Instruction has to be mapped into code fragments
    // of TVM
    match i with
        | GMachine.Push n ->
            mapPush n
        | GMachine.Pop n ->
            mapPop n
        | GMachine.Pushglobal f ->
            mapPushglobal (hash f)
        | GMachine.Pushint n ->
            mapPushint n
        | GMachine.Mkap ->
            mapMkap ()
        | GMachine.Update n ->
            mapUpdate n
        | GMachine.Slide n ->
            mapSlide n
        | GMachine.Alloc n ->
            mapAlloc n
        | GMachine.Unwind ->
            mapUnwind ()
        | GMachine.Eval ->
            mapEval ()
        | GMachine.Add ->
            mapAdd ()
        | GMachine.Sub ->
            mapSub ()
        | GMachine.Mul ->
            mapMul ()
        | GMachine.Div ->
            mapDiv ()
        | GMachine.Equal ->
            mapEqual ()
        | GMachine.Greater ->
            mapGreater ()
        | GMachine.Less ->
            mapLess ()
        | GMachine.Cond (t,f) ->
            mapCond (compileCode t) (compileCode f)
        | GMachine.Pack (tag,n) ->
            mapPack tag n
        | GMachine.Casejump l ->
            let l' = compileCasejumpSelector l
            mapCasejump l'
        | GMachine.Split n ->
            mapSplit n
        | GMachine.DumpStk ->
            mapDumpstk ()

and compileCode (code:GMachine.GmCode) : TVM.Code =
    code
    |> List.map (fun c -> compileInstr c) // list of lists of Instructions
    |> List.concat
and compileCasejumpSelector (l: (int * GMachine.GmCode) list) : TVM.Code =
    match l with
        | [] ->
            [Throw (int RuntimeErrors.CaseNotFound)]  // case not found
        | (tag, code) :: t ->
            [Dup; // n n
             PushInt tag; // n n tag
             Equal; // n (tag=n?)
             PushCont ([Drop] @ compileCode code); // n (-1|0) c
             IfJmp] @ // if we found the right tag, jmp to c
                compileCasejumpSelector t


// st - final state; we omit the exit code from the VM
let getResultStack (st:TVM.TVMState) : TVM.Stack =
    List.tail st.stack

// get node with address n from the heap
let getHeapAt (n:int) (st:TVM.TVMState) : TVM.Value =
    let (Tup (Null :: Tup heap :: _))  = st.cr.c7
    let i = n / TVM.bucketSize
    let j = n % TVM.bucketSize
    let (Tup h1) = List.item i heap
    List.item j h1

// extract heap node with the address given on the stack top
let getResultHeap (st:TVM.TVMState) : TVM.Value =
    let ((Int n) :: _) = getResultStack st
    getHeapAt n st

let tvmHeap (st:TVM.TVMState) =
    let (Tup (Null :: Tup heap :: _))  = st.cr.c7
    heap

let mkCont (c:TVM.Code) : TVM.Value =
    Cont { TVM.Continuation.Default with code = c }

let nnum (n:int) : TVM.Value =
    Tup [Int (int GMachine.NodeTags.NNum); mkCont mapUnwindNNum; Int n]

let nap (l:int) (r:int) : TVM.Value =
    Tup [Int (int GMachine.NodeTags.NAp); mkCont mapUnwindNAp; Int l; Int r]

let nglobal (n:int) (c:GMachine.GmCode) : TVM.Value =
    Tup [Int (int GMachine.NodeTags.NGlobal); mkCont mapUnwindNGlobal; (Int n);
         Cont ({TVM.Continuation.Default with code = compileCode c})]

let nind (v:int) =
    Tup [Int (int GMachine.NodeTags.NInd); mkCont mapUnwindNInd; (Int v)]

let nconstr (n:int) (a: int list) =
    Tup ([Int (int GMachine.NodeTags.NConstr); mkCont mapUnwindNConstr; (Int n); Tup (a |> List.map TVM.Int)])

// GMachine stack consists of addresses only; there are
// no data values there.
// We represent addresses by monotonically increasing
// sequence of integers in TVM.
let prepareStack (stk:GMachine.GmStack): TVM.Stack =
    List.map (fun i -> TVM.Int i) stk

let prepareGlobals (globals:GMachine.GmGlobals): TVM.Value =
    // globals is a mapping from names to addresses
    // we need to prepare the corresponding Cell [SDict] for that
    // Cell (SDict Map<int,SValue list>)
    // GmGlobals = Map<Name, Addr>, where Name is a string, Addr is int
    // Instead of symbolic name, we just use the hash of its name
    globals
    |> Map.toList  // [("main",10); ("f", 51); ... ]
    |> List.map ( fun x -> (hash (fst x), [SInt (snd x)]) ) // [(hash "main", [SInt 10]), ...]
    |> Map.ofList  // Map<int,SValue list>
    |> SDict
    |> List.singleton
    |> Cell

let encodeNode (v:GMachine.Node) : TVM.Value =
    match v with
    | GMachine.NNum n -> nnum n
    | GMachine.NAp (l, r) -> nap l r
    | GMachine.NGlobal (n, c) -> nglobal n c
    | GMachine.NConstr (n, vs) -> nconstr n vs
    | GMachine.NInd n -> nind n

let rec compileTuple t : TVM.Code =
    match t with
    | Tup l ->
        l
        |> List.map compileElem
        |> List.concat
        |> fun l -> l @ [Tuple l.Length]
        | _ -> failwith "not a tuple"
and compileSlice s : TVM.Code =
    match s with
    | Slice (SDict d :: []) ->
        if Map.isEmpty d then
            [PushNull]
        else
            failwith "not implemented"
    | Slice vs ->
        [PushSlice vs]
    | _ ->
        failwith "not implemented"
and compileElem e : TVM.Code =
    match e with
    | Int n -> [PushInt n]
    | Tup _ -> compileTuple e
    | Cont c -> [PushCont c.code]
    | Null -> [PushNull]
    | Slice _ -> compileSlice e
    | _ -> failwith "not implemented"

let prepareHeap (heap:GMachine.GmHeap): TVM.Value =
// heap in TVM is represented as array of arrays.
// We need to construct it by the given GmHeap.
// GmHeap = Map<Addr, Node>
    let kv = Map.toList heap
    let emptyHeap =
        let emptyBucket =
            List.init TVM.bucketSize (fun _ -> TVM.arrayDefaultVal)
        List.init TVM.bucketSize (fun _ -> emptyBucket)
    let put h k v =
        let i = k / TVM.bucketSize
        let j = k % TVM.bucketSize
        let ai = List.item i h
        let aij = List.updateAt j v ai
        List.updateAt i aij h
    let l =
        List.fold (fun h (k,v) -> put h k (encodeNode v)) emptyHeap kv
    Tup (l |> List.map Tup)

let prepareC7 heap heapCounter globals unwindCont =
    Tup [Null; heap; heapCounter; globals; unwindCont]

let selectorMap = Map [(0, [SCode mapUnwindNNum] );
                       (1, [SCode mapUnwindNAp] );
                       (2, [SCode mapUnwindNGlobal] );
                       (3, [SCode mapUnwindNInd] );
                       (4, [SCode mapUnwindNConstr] )]

let unwindCont =
    TVM.Cont { TVM.Continuation.Default with code = mapUnwind () }

let initC7 =
    TVM.arrayNew @ [SetGlob (int RuntimeGlobalVars.Heap)] @
    [PushInt -1; SetGlob (int RuntimeGlobalVars.HeapCounter)] @
    [PushNull; SetGlob (int RuntimeGlobalVars.Globals)] @
    [PushCont (mapUnwind ()); SetGlob (int RuntimeGlobalVars.UnwindCont)]

let compileInt (n:int) : TVM.Code =
    [PushInt n]

let compileHeap heapKV : TVM.Code =
    List.fold (fun h (k,v) ->
               let v' = compileTuple (encodeNode v)
               h @ (compileInt k) @ v' @ TVM.arrayPut) TVM.arrayNew heapKV

let compileIntBuilder (n:int) : TVM.Code =
    [PushInt n; Newc; Sti 128]

// Cell ([SDict vs]), vs = [(int,int)]
let compileGlobals globals : TVM.Code =
    List.fold (fun d (k, v) ->
               (compileIntBuilder v) @
               (compileInt k) @
               d @
               dictSet) [PushNull] globals

let initC7with heap globals globalsCnt (unwindCont:TVM.Value) : TVM.Code =
    // we need to compile each object and put everything into C7
    // the order of putting items in C7 matters here: greater indexes
    // become accessible only after the lesser ones were added.
    (compileHeap (Map.toList heap)) @ [SetGlob (int RuntimeGlobalVars.Heap)] @
    [PushInt globalsCnt; SetGlob (int RuntimeGlobalVars.HeapCounter)] @
    (compileGlobals globals) @ [SetGlob (int RuntimeGlobalVars.Globals)] @
    [PushCont unwindCont.unboxCont.code; SetGlob (int RuntimeGlobalVars.UnwindCont)]

let compile (gms: GMachine.GmState) : TVM.TVMState =
    let code = compileCode (GMachine.getCode gms)
    let stack = prepareStack (GMachine.getStack gms)
    let c0 = TVM.Continuation.Default
    // let us know how many addresses were already allocated for globals
    // this is to provide monotonic increase of the address counter.
    // Otherwise heap may become corrupted.
    let globalsCnt = Map.count (GMachine.getGlobals gms)
    let globalsInts =
        (GMachine.getGlobals gms)
        |> Map.toList  // [("main",10); ("f", 51); ... ]
        |> List.map ( fun x -> (hash (fst x), snd x) ) // [(hash "main", [SInt 10]), ...]
    let heap' = GMachine.getHeap gms
    let initC7Code = initC7with heap' globalsInts (globalsCnt - 1) unwindCont
    { code = initC7Code @ code; stack = stack; cr = { TVM.ControlRegs.Default with c0 = Some c0 } }

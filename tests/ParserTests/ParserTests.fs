// For emacs: -*- fsharp -*-

module LHMachineTests

open FSharp.Text.Lexing
open Parser
open ParserModule
open NUnit.Framework

open type LHExpr.Expr
open type LHExpr.SExpr
open type LHTypes.Type

let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

[<SetUp>]
let Setup () =
    ()

[<Test>]
let testTrivial () =
    let res = parse ""
    Assert.AreEqual( None, res );

[<Test>]
let testOne () =
    let res = parse "contract test"
    Assert.AreEqual( Some (Module ("test", [])), res );

[<Test>]
let testTwo () =
    let res = parse "contract
                        test"
    Assert.AreEqual( Some (Module ("test", [])), res );

[<Test>]
let testDecl2 () =
    let res = parse "contract test
                     type State = { x : int }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", PT [("x", Int 256)])])), res );

[<Test>]
[<Ignore("type List is not implemented")>]
let testDecl3 () =
    let res = parse "contract test
                     type State = { x : List }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", PT [("x", UserType ("List", Some Unit))])])), res );

[<Test>]
[<Ignore("type List is not implemented")>]
let testDecl4 () =
    let res = parse "contract test
                     type State = { x : List; y : Bool }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", PT [("x", UserType ("List", Some Unit));
                                                                  ("y", Bool)])])), res );

[<Test>]
let testDecl6 () =
    let res = parse "contract test

                     type UserData =
                         | Borrower of name:string * amount:int
                         | Depositor of name:string * amount:int
    "
    let decls = [TypeDef ("UserData",
                          ST [("Borrower", [String; Int 256]);
                              ("Depositor", [String; Int 256])])]
    Assert.AreEqual( Some (Module ("test", decls)), res  );


// extract n-th handler definition AST in a form of SExpr
let getHandlerAst (m:Module) (n:int) =
    m.Decls.[n].handlerDef
    |> (function | (_,_,c) -> c)
    |> (fun c -> c.toSExpr())

let getLetAst (m:Module) (n:int) =
    m.Decls.[n].letBinding
    |> (function | (_, _, _, c) -> c)
    |> (fun c -> c.toSExpr())

[<Test>]
let testHandler1 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if 1 > 5 then 1 else 0
    "
    let resAst = getHandlerAst res.Value 0
    let expected =
        SIf (SGt (SNum 1, SNum 5), SNum 1, SNum 0)
    Assert.AreEqual( expected, resAst  );

[<Test>]
let testHandler2 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if x > 5 then 1 else 0
    "
    let resAst = getHandlerAst res.Value 0
    let expected = SIf (SGt (SVar "x", SNum 5), SNum 1, SNum 0)
    Assert.AreEqual( expected , resAst );

[<Test>]
let testHandler3 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if (x > 5) then 1 else 0
    "
    let resAst = getHandlerAst res.Value 0
    let expected = SIf (SGt (SVar "x", SNum 5), SNum 1, SNum 0)
    Assert.AreEqual( expected, resAst  );

[<Test>]
let testLetMain4 () =
    let res = parse "contract test
                     let main =
                       let rec factorial n =
                          if (n > 1) then (n * factorial (n - 1)) else 1 in
                       factorial 10 ;;
    "
    let resAst = getLetAst res.Value 0
    let expected =
          SLetRec ("factorial",
            SFunc (("n",None), SIf (SGt (SVar "n", SNum 1),
                             SMul (SVar "n", SAp (SVar "factorial",
                                                  SSub (SVar "n", SNum 1))),
                             SNum 1)),
            SAp (SVar "factorial", SNum 10))
    Assert.AreEqual( expected, resAst  )

[<Test>]
let testApAssoc0 () =
    let res = parse "contract test
                     let f f1 f2 x y = f2 (f1 x) (f1 y) ;;"
    let resAst = getLetAst res.Value 0
    let expected = SFunc (("f1", None),
                    SFunc (("f2", None),
                     SFunc (("x", None),
                      SFunc (("y", None),
                       SAp (SAp (SVar "f2",
                             SAp (SVar "f1", SVar "x")),
                       SAp (SVar "f1", SVar "y"))))))
    Assert.AreEqual( expected, resAst  )


[<Test>]
let testHandler4 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if ( (1 + 1) > 2) then 1 else 0 "

    match res with
    | Some (Module ("test", [HandlerDef ("test", [("x", Some (Int 256))], decls)])) ->
        Assert.AreEqual(SIf (SGt (SAdd (SNum 1, SNum 1), SNum 2),
                             SNum 1,
                             SNum 0),
                        decls.toSExpr() );
    | _ ->
        Assert.Fail ("wrong parsing")


[<Test>]
let testHandler5 () =
    // This sample will not pass the typechecker, but shall parse well.
    let res = parse "contract test
                     handler test (x:int) =
                          if (1 + (1 > 2)) then 1 else 0
    "
    let expected = SIf (SAdd (SNum 1, SGt (SNum 1, SNum 2)), SNum 1, SNum 0)

    Assert.AreEqual( expected, getHandlerAst res.Value 0 );

[<Test>]
let testHandler6 () =
    let res = parse "contract test
                     handler fact (n:int) =
                          if (n > 1) then n * fact (n - 1) else 1
    "
    let expected = SIf (SGt (SVar "n", SNum 1),
                        SMul (SVar "n", SAp (SVar "fact", SSub (SVar "n", SNum 1))),
                        SNum 1)

    Assert.AreEqual( expected, getHandlerAst res.Value 0  );

[<Test>]
let testHandler7 () =
    let res = parse "contract test
                     handler msg_handler1 (n:int) =
                          n
                     handler msg_handler2 (n:int) =
                          n * 2
    "
    let expr0 = SVar "n"
    let expr1 = SMul (SVar "n", SNum 2)
    Assert.AreEqual( expr0 , getHandlerAst res.Value 0  );
    Assert.AreEqual( expr1 , getHandlerAst res.Value 1  );

[<Test>]
let testLet0 () =
    let res = parse "contract test
                     handler msg_handler1 (n:int) =
                       let f = 10 in f
    "
    let expected = SLet ("f", SNum 10, SVar "f")
    Assert.AreEqual( expected, getHandlerAst res.Value 0  );

[<Test>]
let testLet2 () =
    let res = parse "contract test

                     handler msg_handler1 (n:int) =
                       let f = 10 in
                       let g = msg_handler1 10 in
                       g
                    "
    let expected = SLet ("f", SNum 10,
                    SLet ("g", SAp (SVar "msg_handler1", SNum 10), SVar "g"))
    Assert.AreEqual( expected, getHandlerAst res.Value 0 );

[<Test>]
let testLetBindings0 () =
    let res = parse "contract test
                     let avg l =
                        let s = sum l in
                        let rec length l = l in
                            s + length l
                     ;;
                    "
    let expected = SFunc (("l", None),
                    SLet ("s", SAp (SVar "sum", SVar "l"),
                     SLetRec ("length", SFunc (("l", None), SVar "l"),
                      SAdd (SVar "s", SAp (SVar "length", SVar "l")))))
    Assert.AreEqual( expected, getLetAst res.Value 0 );

[<Test>]
let testStr0 () =
    let res = parse "contract test
                     let x = \"abcd\" ;;
    "
    let expected = SStr ("abcd")
    Assert.AreEqual( expected, getLetAst res.Value 0  );

[<Test>]
let testLetBindings1 () =
    let res = parse "contract test
                     let sum (x:int) (y:int) = x + y ;;
                    "
    let expected = SFunc (("x", Some (Int 256)),
                    SFunc (("y", Some (Int 256)),
                     SAdd (SVar "x", SVar "y")))
    Assert.AreEqual( expected, getLetAst res.Value 0 );

[<Test>]
let testActorInit () =
    let res = parse "
     contract test

     let actorInit msg is_external =
       let act_st = actorStateRead () in
       let msg_seqno = msgSeqNo msg in
       if msg_seqno  = act_st.seqno then
          failwith 100
       else
          let st = act_st.state in
          let st' = actorMain msg st in
          let act_st' = { seqno = msg_seqno; state = st' } in
          actorStateWrite act_st'
     ;;"

    let expected =
      SFunc (("msg", None),
       SFunc (("is_external", None),
        SLet ("act_st", SAp (SVar "actorStateRead", SNull),
         SLet ("msg_seqno", SAp (SVar "msgSeqNo", SVar "msg"),
           SIf (SEq (SVar "msg_seqno", SSelect (SVar "act_st", SVar "seqno")),
                SFailWith 100,
                SLet ("st", SSelect (SVar "act_st", SVar "state"),
                 SLet ("st'", SAp (SAp (SVar "actorMain", SVar "msg"), SVar "st"),
                  SLet ("act_st'", SRecord [("seqno", SVar "msg_seqno"); ("state", SVar "st'")],
                   SAp (SVar "actorStateWrite", SVar "act_st'")))))))))

    Assert.AreEqual( expected, getLetAst res.Value 0  );

(* [<Test>]
[<Ignore("not ready")>]
let testDecl5 () =
    let res = parse "contract test
                     type UserData = { name : string; balance : int }
                     type State = { ud:UserData }
    "
    let decls = [TypeDef ("UserData", PT [("name", String); ("balance", Int 256)]);
                 TypeDef ("State", PT [("ud", UserType "UserData")])]
    Assert.AreEqual( Some (Module ("test", decls)), res  );
*)

// TODO!
(*[<Test>]
let testDecl7 () =
    let res = parse "contract test

                     type UserData =
                         | Borrower of name:string * amount:int
                         | Depositor of name:string * amount:int

                     type State = { user : UserData }
    "
    let decls = [TypeDef ("UserData",
                          ST [("Borrower", [String; Int 256]);
                              ("Depositor", [String; Int 256])]);
                 TypeDef ("State",
                          PT [("user", UserType "UserData")])]

    Assert.AreEqual( Some (Module ("test", decls)), res  );
**)

(*
[<Test>]
[<Ignore("not ready")>]
let testLetBindings1 () =
    let res = parse "contract test
                     let c = 10000 ;;
                     let rec fact x = if x > 1 then x * fact (x - 1) else 1 ;;
                     type UserData = { name : string; balance : int }
                     type State = { ud:UserData }
                     handler msg_handler1 (n:int) =
                      let rec fact x = fact (x - 1) in
                      let g = 1000 in
                      fact g
                    "
    let decls = [
        LetBinding ("c", false, ENum 10000);
        LetBinding ("fact", true,
                    EFunc ("x", EIf ( EGt (EVar "x", ENum 1),
                                      EMul (EVar "x", EAp (EVar "fact", ESub (EVar "x", ENum 1))),
                                      ENum 1) ));
        TypeDef ("UserData", PT [("name", String); ("balance", Int 256)]);
        TypeDef ("State", PT [("ud", UserType "UserData")]);
        HandlerDef ("msg_handler1",
                    [("n", Int 256)],
                       ELet ("fact", EFunc ("x", EAp (EVar "fact", ESub (EVar "x", ENum 1))),
                        ELet ("g", ENum 1000,
                         EAp (EVar "fact", EVar "g"))))
        ]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
[<Ignore("type List is not implemented")>]
let testMatchExpr0 () =
    let res = parse "contract test
                     handler msg_handler1 (m:List) =
                      match m with
                      | Nil -> 0
                      | Cons (h, t) -> 1 + msg_handler1 t
                    "
    let decls = [HandlerDef ("msg_handler1",
                             [("m", UserType ("List", Unit))],
                             ECase (EVar "m",
                                    [(hash "Nil", [], ENum 0);
                                     (hash "Cons", ["h"; "t"],
                                      EAdd (ENum 1, EAp (EVar "msg_handler1", EVar "t")))]))
                             ]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

(**
[<Test>]
let testMatchExpr1 () =
    let res = parse "contract test
                     handler msg_handler1 (m:List) (l:List) =
                      match m with
                      | Nil ->
                           ( match l with
                             | Nil -> 0
                             | Cons (_, _) -> length l )
                      | Cons (h, t) -> 1 + msg_handler1 t
                    "
    let decls = [HandlerDef ("msg_handler1",
                  [("m",UserType ("List", Unit)); ("l",UserType ("List", Unit))],
                   ECase (EVar "m",
                    [(hash "Nil", [],
                       ECase (EVar "l",
                         [(hash "Nil", [], ENum 0);
                          (hash "Cons", ["_"; "_"], EAp (EVar "length", EVar "l"))]));
                     (hash "Cons", ["h"; "t"],
                       EAdd (ENum 1, EAp (EVar "msg_handler1", EVar "t")))]))
                    ]
    Assert.AreEqual( Some (Module ("test", decls)), res  );
**)

[<Test>]
let testAssignment0 () =
    let res = parse "contract Simple

                     type State = {
                       counter: int;
                       sum: int
                     }

                     handler add_more =
                         state <- { counter = 0 ; sum = 0 }
                    "
    let decls = [TypeDef ("State", PT [("counter", Int 256); ("sum", Int 256)]);
                 HandlerDef ("add_more", [], EAssign (ERecord [ENum 0; ENum 0]))]
    Assert.AreEqual( Some (Module ("Simple", decls)), res  );

[<Test>]
let testSample0 () =
    let res = parse "contract Simple

                     type State = {
                       counter: int;
                       sum: int
                     }

                     let sum a b = a + b ;;

                     handler add_more (x: int) =
                         let sum' = sum state.counter b in
                         let counter' = b in
                         state <- { counter = counter' ; sum = sum' }
                    "
    let decls = [
        TypeDef ("State", PT [("counter", Int 256); ("sum", Int 256)]);
        LetBinding ("sum", false, EFunc ("a", EFunc ("b", EAdd (EVar "a", EVar "b"))));
        HandlerDef ("add_more", [("x", Int 256)],
                    ELet ("sum'",
                      EAp (EVar "sum",
                       EAp (ESelect (EVar "state", EVar "counter"), EVar "b")),
                        ELet ("counter'", EVar "b",
                         EAssign (ERecord [EVar "counter'"; EVar "sum'"]))))
    ]
    Assert.AreEqual( Some (Module ("Simple", decls)), res  );
***)

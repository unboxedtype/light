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

[<OneTimeTearDown>]
let AfterTest () =
    // 'Fun' counter reset. We need this to generate fresh fun names
    // on each test.
    Parser.resetFunVar ()

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
let testTypecast1 () =
    let res = parse "contract test
                     let number = assembly \"100 INT\" :> int  ;;
                    "
    let expected = STypeCast (SAsm ("100 INT"), LHTypes.Int 256)
    Assert.AreEqual( expected, getLetAst res.Value 0 );

[<Test>]
[<Ignore("parser error")>]
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


[<Test>]
let testFun1 () =
    Parser.resetFunVar ()
    let res = parse "contract test
                     let sum = fun (x:int) (y:int) -> x + y ;;
                    "
    let expected = SLet ("fun1",
                    SFunc (("x", Some (Int 256)),
                     SFunc (("y", Some (Int 256)),
                      SAdd (SVar "x", SVar "y"))), SVar "fun1")
    Assert.AreEqual( expected, getLetAst res.Value 0);

[<Test>]
let testFun2 () =
    Parser.resetFunVar ()
    let res = parse "contract test
                     let sum = fun x y -> x + y ;;
                    "
    let expected = SLet ("fun1",
                    SFunc (("x", None),
                     SFunc (("y", None),
                      SAdd (SVar "x", SVar "y"))), SVar "fun1")
    Assert.AreEqual( expected, getLetAst res.Value 0);

[<Test>]
let testFun3 () =
    Parser.resetFunVar ()
    let res = parse "contract test
                     let sum =
                       (fun x y -> x + y) 10 20 ;;
                    "
    let expected = SAp (
                    SAp (
                     SLet ("fun1",
                      SFunc (("x", None),
                       SFunc (("y", None),
                        SAdd (SVar "x", SVar "y")
                       )
                      ), SVar "fun1"
                     ),
                     SNum 10
                    ),
                    SNum 20
                   )
    Assert.AreEqual( expected, getLetAst res.Value 0);

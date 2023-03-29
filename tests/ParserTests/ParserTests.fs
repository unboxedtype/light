// For emacs: -*- fsharp -*-

module LHMachineTests

open FSharp.Text.Lexing
open Parser
open ParserModule
open NUnit.Framework

open type LHMachine.Expr

[<SetUp>]
let Setup () =
    ()

let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

[<Test>]
let testTrivial () =
    let res = parse ""
    Assert.AreEqual( None, res );

[<Test>]
let testOne () =
    let res = parse "module test"
    Assert.AreEqual( Some (Module ("test", [])), res );

[<Test>]
let testTwo () =
    let res = parse "module
                        test"
    Assert.AreEqual( Some (Module ("test", [])), res );

[<Test>]
let testDecl () =
    let res = parse "module test
                     type State = { }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", ProdType [])])), res );

[<Test>]
let testDecl2 () =
    let res = parse "module test
                     type State = { x : int }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", ProdType [("x","int")])])), res );

[<Test>]
let testDecl3 () =
    let res = parse "module test
                     type State = { x : List }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", ProdType [("x","List")])])), res );

[<Test>]
let testDecl4 () =
    let res = parse "module test
                     type State = { x : List; y : Bool }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", ProdType [("x","List"); ("y","Bool")])])), res );

[<Test>]
let testDecl5 () =
    let res = parse "module test
                     type UserData = { name : String; balance : Uint }
                     type State = { ud:UserData }
    "
    let decls = [TypeDef ("UserData", ProdType [("name","String"); ("balance","Uint")]);
                 TypeDef ("State", ProdType [("ud","UserData")])]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testDecl6 () =
    let res = parse "module test

                     type UserData =
                         | Borrower of name:String * amount:Uint
                         | Depositor of name:String * amount:Uint
    "
    let decls = [TypeDef ("UserData",
                          SumType [("Borrower", [("name","String"); ("amount","Uint")]);
                                   ("Depositor", [("name","String"); ("amount","Uint")])])]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testDecl7 () =
    let res = parse "module test

                     type UserData =
                         | Borrower of name:String * amount:Uint
                         | Depositor of name:String * amount:Uint

                     type State = { user : UserData }
    "
    let decls = [TypeDef ("UserData",
                          SumType [("Borrower", [("name","String"); ("amount","Uint")]);
                                   ("Depositor", [("name","String"); ("amount","Uint")])]);
                 TypeDef ("State",
                          ProdType [("user","UserData")])]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler1 () =
    let res = parse "module test
                     handler test (x:int) =
                          if 1 > 5 then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x","int")],
                             EIf (EGt (ENum 1, ENum 5), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler2 () =
    let res = parse "module test
                     handler test (x:int) =
                          if x > 5 then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x","int")],
                             EIf (EGt (EVar "x", ENum 5), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler3 () =
    let res = parse "module test
                     handler test (x:int) =
                          if (x > 5) then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x","int")],
                             EIf (EGt (EVar "x", ENum 5), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler4 () =
    let res = parse "module test
                     handler test (x:int) =
                          if ( (1 + 1) > 2) then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x","int")],
                             EIf (EGt (EAdd (ENum 1, ENum 1), ENum 2), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler5 () =
    // This sample will not pass the typechecker, but shall parse well.
    let res = parse "module test
                     handler test (x:int) =
                          if (1 + (1 > 2)) then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x","int")],
                             EIf (EAdd (ENum 1, EGt (ENum 1, ENum 2)), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler6 () =
    let res = parse "module test
                     handler fact (n:int) =
                          if (n > 1) then n * fact (n - 1) else 1
    "
    let decls = [HandlerDef ("fact", [("n","int")],
                             EIf (EGt (EVar "n", ENum 1),
                                  EMul (EVar "n", EAp (EVar "fact", ESub (EVar "n", ENum 1))),
                                  ENum 1))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler7 () =
    let res = parse "module test
                     handler msg_handler1 (n:int) =
                          n
                     handler msg_handler2 (n:int) =
                          n * 2
    "
    let decls = [HandlerDef ("msg_handler1", [("n","int")], EVar "n");
                 HandlerDef ("msg_handler2", [("n","int")], EMul (EVar "n", ENum 2))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet0 () =
    let res = parse "module test
                     handler msg_handler1 (n:int) =
                       let f = 10 in f
    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n","int")],
                             ELet (false, [("f",ENum 10)], EVar "f"))];
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet1 () =
    let res = parse "module test
                     handler msg_handler1 (n:int) =
                       let f = 10 in f
    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n","int")],
                             ELet (false, [("f",ENum 10)], EVar "f"))];
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet2 () =
    let res = parse "module test

                     handler msg_handler1 (n:int) =
                       let f = 10 in
                       let g = msg_handler1 10 in
                       g
                    "

    let decls = [HandlerDef ("msg_handler1",
                             [("n","int")],
                             ELet (false, [("f", ENum 10)],
                                    ELet (false, [("g", EAp (EVar "msg_handler1", ENum 10))],
                                          EVar "g")))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet3 () =
    let res = parse "module test

                     handler msg_handler1 (n:int) =
                      let f x = x + 5 in
                      f 10
                    "

    let decls = [HandlerDef ("msg_handler1",
                             [("n","int")],
                             ELet (false, [("f", EFunc ("x", EAdd (EVar "x", ENum 5)))],
                                   EAp (EVar "f", ENum 10)))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet4 () =
    let res = parse "module test
                     handler msg_handler1 (n:int) =
                      let f x = x + 5 in
                      let g = 1000 in
                      f g
                    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n","int")],
                             ELet (false, [("f", EFunc ("x", EAdd (EVar "x", ENum 5)))],
                              ELet (false, [("g", ENum 1000)],
                               EAp (EVar "f", EVar "g"))))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLetRec1 () =
    let res = parse "module test
                     handler msg_handler1 (n:int) =
                      let rec fact x = fact (x - 1) in
                      let g = 1000 in
                      fact g
                    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n", "int")],
                             ELet (true, [("fact", EFunc ("x", EAp (EVar "fact", ESub (EVar "x", ENum 1))))],
                              ELet (false, [("g", ENum 1000)],
                               EAp (EVar "fact", EVar "g"))))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

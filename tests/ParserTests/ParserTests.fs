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

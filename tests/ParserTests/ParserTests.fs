// For emacs: -*- fsharp -*-

module LHMachineTests

open FSharp.Text.Lexing
open Parser
open ParserModule
open NUnit.Framework

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

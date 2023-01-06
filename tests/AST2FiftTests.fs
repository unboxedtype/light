module AST2FiftTests

open NUnit.Framework
open System
open Printf
open System.IO
open System.Diagnostics
open System.Threading.Tasks
open AST2Fift

let ExecuteCodeInVM fiftCode =
    let scriptPath = Environment.CurrentDirectory + "/test.fif"
    let program = fiftHeader @ fiftCode @ fiftFooter
    let file = File.CreateText(scriptPath)
    program |> List.map (fun s -> fprintfn file "%s" s) |> ignore
    file.Close()
    FiftExecutor.runFiftScript scriptPath

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let BoolFalseTest () =
    let ctx = Map []
    let s = EvalIRExpr (BoolVal (Bool false)) ctx
    Assert.AreEqual (["0 INT"], s);

[<Test>]
let BoolTrueTest () =
    let ctx = Map []
    let s = EvalIRExpr (BoolVal (Bool true)) ctx
    Assert.AreEqual (["-1 INT"], s);

[<Test>]
let NumberTest () =
    let ctx = Map []
    let s = EvalIRExpr (Number 1000) ctx
    Assert.AreEqual (["1000 INT"], s);

[<Test>]
let Add2Test () =
    let ctx = Map []
    let sum = EvalIRExpr (Add (Number 1000, Number 1234)) ctx
    Assert.AreEqual (["1000 INT"; "1234 INT"; "ADD"], sum)

[<Test>]
let ExecBoolUnit () =
    let ctx = Map []
    let code = EvalIRExpr (BoolVal (Bool true)) ctx
    Assert.AreEqual (ExecuteCodeInVM code, "-1")

[<Test>]
let ExecAddTest () =
    let ctx = Map []
    let code = EvalIRExpr (Add (Number 1000, Number 1234)) ctx
    Assert.AreEqual (ExecuteCodeInVM code, "2234")

[<Test>]
let ExecEqTest () =
    let ctx = Map []
    let l = Add (Number 1000, Number 1234)
    let r = Add (Number 1001, Number 1233)
    let code_eq = EvalIRExpr (BoolVal (Eq (l, r))) ctx
    Assert.AreEqual (ExecuteCodeInVM code_eq, "-1")

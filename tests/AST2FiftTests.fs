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
    let s = EvalIRExpr (BoolVal (Bool false))
    Assert.AreEqual (["0 INT"], s);

[<Test>]
let BoolTrueTest () =
    let s = EvalIRExpr (BoolVal (Bool true))
    Assert.AreEqual (["-1 INT"], s);

[<Test>]
let NumValTest () =
    let s = EvalIRExpr (NumVal 1000)
    Assert.AreEqual (["1000 INT"], s);

[<Test>]
let Add2Test () =
    let sum = EvalIRExpr (Add (NumVal 1000, NumVal 1234))
    Assert.AreEqual (["1000 INT"; "1234 INT"; "ADD"], sum)

[<Test>]
let ExecBoolUnit () =
    let code = EvalIRExpr (BoolVal (Bool true))
    Assert.AreEqual (ExecuteCodeInVM code, "-1")

[<Test>]
let ExecAddTest () =
    let code = EvalIRExpr (Add (NumVal 1000, NumVal 1234))
    Assert.AreEqual (ExecuteCodeInVM code, "2234")

module AST2FiftTests

open NUnit.Framework
open System
open Printf
open System.IO
open System.Diagnostics
open System.Threading.Tasks
open System.Collections.Generic
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
let ListTest () =
    let ctx = Map []
    let nil = EvalIRExpr (List Nil) ctx
    Assert.AreEqual (["NIL"], nil)

[<Test>]
let ListTest2 () =
    let ctx = Map []
    let list = EvalIRExpr (List (Cons (Number 1, Nil))) ctx
    Assert.AreEqual (["1 INT"; "NIL"; "CONS"], list)

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

[<Test>]
let ExecValueTest () =
    let ctx = Map [ ("a", Number 1000) ]
    let code_eq = EvalIRExpr (Var "a") ctx
    Assert.AreEqual (ExecuteCodeInVM code_eq, "1000")

[<Test>]
let ExecValueNotFoundTest () =
    let ctx = Map []
    let code_eq =
     try
         Some (EvalIRExpr (Var "a") ctx)
     with
         | :? KeyNotFoundException -> None
         | _ -> Some ([""])
    Assert.AreEqual (code_eq, None)

[<Test>]
let ExecValueAddTest () =
    let ctx = Map [ ("a", Number 1000); ("b", Number 2000);
                    ("c", Add (Var "a", Var "b"))]
    let code_eq = EvalIRExpr (Var "c") ctx
    Assert.AreEqual (ExecuteCodeInVM code_eq, "3000")

[<Test>]
let ExecValueAddTest2 () =
    let ctx = Map [ ("a", Add (Number 100, Number 200));
                    ("b", Add (Number 2000, Var "a"));
                    ("c", Add (Var "a", Var "b"))]
    let code_eq = EvalIRExpr (Var "c") ctx
    Assert.AreEqual (ExecuteCodeInVM code_eq, "2600")

[<Test>]
let ExecListTest () =
    let ctx = Map [ ("a", Number 100); ("b", Number 200) ]
    let code = EvalIRExpr (List (Cons (Var "b", (Cons (Var "a", Nil))))) ctx
    Assert.AreEqual (ExecuteCodeInVM code, "[ 200 [ 100 [] ] ]")

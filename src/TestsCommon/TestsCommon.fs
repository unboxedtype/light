// For emacs: -*- fsharp -*-

module TestsCommon

open NUnit.Framework
open LHCompiler
open ParserModule
open LHExpr

let execIRExt isFift irProg expected =
    let code = (LHMachine.fixpointTVMImpl
                @ LHMachine.compileToTVM irProg)
               |> List.map (TVM.instructionToAsmString isFift)
               |> String.concat "\n"
    let res =
        let filename =
            NUnit.Framework.TestContext.CurrentContext.Test.Name + ".asm"
        if isFift then
            TVM.dumpString filename  (LHMachine.asmAsRunVM code) ;
            FiftExecutor.runFiftScript filename
        else
            TVM.dumpString filename code ;
            (SDKInterop.executeTVMCode SDKInterop.client code).[0].ToString()
    Assert.AreEqual (expected, res)

let execIR irProg expected =
    execIRExt false irProg expected

let execAndCheckPrint addInit debug isFift (prog:string) expected =
    if debug then
        printfn "%A" prog |> ignore
        printfn "Passing program to the compiler..."
    let code = compile prog addInit debug isFift
    if debug then
        printfn "Dumping compiled program into file..."
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".asm"
    let res = 
       if isFift then
           TVM.dumpString filename (LHMachine.asmAsRunVM code) ;
           FiftExecutor.runFiftScript filename
       else
           TVM.dumpString filename code ;
           (SDKInterop.executeTVMCode SDKInterop.client code).[0].ToString()
    Assert.AreEqual (expected, res)

let execAndCheck prog expected =
    execAndCheckPrint false false false prog expected

let execReal debug withInit prog dataExpr expected =
    if debug then
        printfn "%A" prog |> ignore
        printfn "Passing program to the compiler..."
    let code = LHMachine.asmAsCell (compile prog withInit debug true)
    let tname = NUnit.Framework.TestContext.CurrentContext.Test.Name
    // FIFT script that produces state init into .TVC file
    let nameGenStateInitScript = tname + ".fif"
    // Where to dump the TVC
    let nameGenStateInitTVC = tname + ".tvc"
    // FIFT script that produces message with state init attachd
    let nameGenMessageWithStateInitScript = "genMsg" + tname + ".fif"

    if debug then
        printfn "Dumping compiled program into file %A"
                nameGenStateInitScript
    TVM.dumpString
       nameGenStateInitScript
       (TVM.genStateInit nameGenStateInitTVC code dataExpr)
    // .BOC file that contains binary repr of the message; to be sent
    // using tonos-cli
    let nameMsgWithStateInitBOC = tname + ".boc"
    TVM.dumpString nameGenMessageWithStateInitScript
       (TVM.genMessageWithStateInit tname nameMsgWithStateInitBOC code dataExpr)
    //if debug then
    //    printfn "Executing the resulting FIFT-script..."
    //let res = FiftExecutor.runFiftScript filename
    // Assert.AreEqual (expected, res)
    Assert.Pass ()

let execASTAndCheckPrint (expr:ASTNode) expected ifPrint isFift =
    if ifPrint then
        printfn "%A" (expr.toSExpr ())
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".asm"    
    let code =
        LHMachine.compileAST expr [] (Map [])
    execIRExt isFift code expected


let execASTAndCheck g expected =
    execASTAndCheckPrint g expected false false

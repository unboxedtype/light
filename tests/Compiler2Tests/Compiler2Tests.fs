module Compiler2Tests

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework

open System
open System.Collections.Generic
open Compiler2
open type TVM.Value

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let testCompiler2Factorial5 () =
    // fact n = if n == 0 then 1 else n * fact(n-1)
    // main = fact 5
    let coreProgGM =
        [("fact", ["n"],
          GMachine2.EIf (
            GMachine2.EIsZero (GMachine2.EVar "n"),
            GMachine2.ENum 1, // true branch
            GMachine2.EMul (GMachine2.EVar "n",
                           GMachine2.EAp (GMachine2.EVar "fact",
                                         GMachine2.EDec (GMachine2.EVar "n")))) // else branch
          )
         ("main", [], GMachine2.EAp (GMachine2.EVar "fact", GMachine2.ENum 5))]
    let gmInitSt = GMachine2.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testCompiler2Factorial5.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt true 5000)
    Assert.AreEqual (nnum 120, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

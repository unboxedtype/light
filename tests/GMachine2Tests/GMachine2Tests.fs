module GMachine2Tests

open NUnit.Framework

open GMachine2

[<SetUp>]
let Setup () =
    ()

[<Test>]
let testInc0 () =
    let coreProg =
        [("main", [], EInc (ENum 1))]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    Assert.AreEqual( NNum 2, res );

[<Test>]
let testInc1 () =
    let coreProg =
        [("main", [], EInc (EInc (ENum 1)))]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    Assert.AreEqual( NNum 3, res );

[<Test>]
let testFact () =
    let coreProg =
        // fact n = if n == 0 then 1 else n * fact(n-1)
        // main = fact 5
        [("fact", ["n"], EIf (EIsZero (EVar "n"),
                              ENum 1, // true branch
                              EMul (EVar "n", EAp (EVar "fact", EDec (EVar "n")))) // else branch
          )
         ("main", [], EAp (EVar "fact", ENum 5))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 120, res );

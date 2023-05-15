// For emacs: -*- fsharp -*-

module LHMachineTests

open FSharp.Text.Lexing
open Parser
open ParserModule
open NUnit.Framework

open type LHMachine.Expr
open type LHTypes.Type

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
let testDecl3 () =
    let res = parse "contract test
                     type State = { x : List }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", PT [("x", UserType "List")])])), res );

[<Test>]
[<Ignore("type List is not implemented")>]
let testDecl4 () =
    let res = parse "contract test
                     type State = { x : List; y : Bool }
    "
    Assert.AreEqual( Some (Module ("test", [TypeDef ("State", PT [("x", UserType "List");
                                                                  ("y", Bool)])])), res );

[<Test>]
let testDecl5 () =
    let res = parse "contract test
                     type UserData = { name : string; balance : int }
                     type State = { ud:UserData }
    "
    let decls = [TypeDef ("UserData", PT [("name", String); ("balance", Int 256)]);
                 TypeDef ("State", PT [("ud", UserType "UserData")])]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

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

[<Test>]
let testDecl7 () =
    let res = parse "contract test

                     type UserData =
                         | Borrower of name:string * amount:int
                         | Depositor of name:string * amount:int

                     type State = { user : UserData }
    "
    let decls = [TypeDef ("UserData",
                          ST [("Borrower", [String; Int 256]);
                              ("Depositor", [String; Int 256])]);
                 TypeDef ("State",
                          PT [("user", UserType "UserData")])]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler1 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if 1 > 5 then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x",Int 256)],
                             EIf (EGt (ENum 1, ENum 5), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler2 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if x > 5 then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x",Int 256)],
                             EIf (EGt (EVar "x", ENum 5), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler3 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if (x > 5) then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x",Int 256)],
                             EIf (EGt (EVar "x", ENum 5), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler4 () =
    let res = parse "contract test
                     handler test (x:int) =
                          if ( (1 + 1) > 2) then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x", Int 256)],
                             EIf (EGt (EAdd (ENum 1, ENum 1), ENum 2), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler5 () =
    // This sample will not pass the typechecker, but shall parse well.
    let res = parse "contract test
                     handler test (x:int) =
                          if (1 + (1 > 2)) then 1 else 0
    "
    let decls = [HandlerDef ("test", [("x",Int 256)],
                             EIf (EAdd (ENum 1, EGt (ENum 1, ENum 2)), ENum 1, ENum 0))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler6 () =
    let res = parse "contract test
                     handler fact (n:int) =
                          if (n > 1) then n * fact (n - 1) else 1
    "
    let decls = [HandlerDef ("fact", [("n", Int 256)],
                             EIf (EGt (EVar "n", ENum 1),
                                  EMul (EVar "n", EAp (EVar "fact", ESub (EVar "n", ENum 1))),
                                  ENum 1))]

    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testHandler7 () =
    let res = parse "contract test
                     handler msg_handler1 (n:int) =
                          n
                     handler msg_handler2 (n:int) =
                          n * 2
    "
    let decls = [HandlerDef ("msg_handler1", [("n", Int 256)], EVar "n");
                 HandlerDef ("msg_handler2", [("n", Int 256)], EMul (EVar "n", ENum 2))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet0 () =
    let res = parse "contract test
                     handler msg_handler1 (n:int) =
                       let f = 10 in f
    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n", Int 256)],
                             ELet ("f", ENum 10, EVar "f"))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet1 () =
    let res = parse "contract test
                     handler msg_handler1 (n:int) =
                       let f = 10 in f
    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n", Int 256)],
                             ELet ("f",ENum 10, EVar "f"))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet2 () =
    let res = parse "contract test

                     handler msg_handler1 (n:int) =
                       let f = 10 in
                       let g = msg_handler1 10 in
                       g
                    "

    let decls = [HandlerDef ("msg_handler1",
                             [("n",Int 256)],
                             ELet ("f", ENum 10,
                               ELet ("g", EAp (EVar "msg_handler1", ENum 10), EVar "g")))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet3 () =
    let res = parse "contract test

                     handler msg_handler1 (n:int) =
                      let f x = x + 5 in
                      f 10
                    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n", Int 256)],
                             ELet ("f", EFunc ("x", EAdd (EVar "x", ENum 5)),
                              EAp (EVar "f", ENum 10)))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet4 () =
    let res = parse "contract test
                     handler msg_handler1 (n:int) =
                      let f x = x + 5 in
                      let g = 1000 in
                      f g
                    "
    let decls = [HandlerDef ("msg_handler1",
                             [("n", Int 256)],
                             ELet ("f", EFunc ("x", EAdd (EVar "x", ENum 5)),
                              ELet ("g", ENum 1000,
                               EAp (EVar "f", EVar "g"))))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLet5 () =
    let res = parse "contract test
                     let f x y z = x + y + z ;;
                     let haa xy wy = xy wy ;;
                     let haaAAAA x y z = f x y z ;;
                     let haa_A_A12AA_ x y z = f x y z ;;
                    "
    let decls = [LetBinding
                  ("f", false,
                    EFunc ("x", EFunc ("y", EFunc ("z", EAdd (EVar "x", EAdd (EVar "y", EVar "z"))))));
                 LetBinding
                  ("haa", false, EFunc ("xy", EFunc ("wy", EAp (EVar "xy", EVar "wy"))));
                 LetBinding
                  ("haaAAAA", false, EFunc ("x",
                                            EFunc ("y",
                                                   EFunc ("z",
                                                          EAp (EVar "f", EAp (EVar "x", EAp (EVar "y", EVar "z")))))));
                 LetBinding
                  ("haa_A_A12AA_", false,
                   EFunc ("x",
                    EFunc ("y",
                     EFunc ("z", EAp (EVar "f", EAp (EVar "x", EAp (EVar "y", EVar "z")))))))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLetRec1 () =
    let res = parse "contract test
                     handler msg_handler1 (n:int) =
                      let rec fact x = fact (x - 1) in
                      let g = 1000 in
                      fact g
                    "
    let decls = [
        HandlerDef ("msg_handler1",
                    [("n", Int 256)],
                       ELet ("fact", EFunc ("x", EAp (EVar "fact", ESub (EVar "x", ENum 1))),
                        ELet ("g", ENum 1000,
                         EAp (EVar "fact", EVar "g"))))
    ]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLetBindings0 () =
    let res = parse "contract test
                     let avg l =
                        let s = sum l in
                        let rec length l = l in
                            s + length l
                     ;;
                    "
    let decls = [LetBinding ("avg", false,
                  EFunc ("l",
                   ELet ("s", EAp (EVar "sum", EVar "l"),
                    ELet ("length", EFunc ("l", EVar "l"),
                     EAdd (EVar "s", EAp (EVar "length", EVar "l"))))))]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testLetBindings1 () =
    let res = parse "contract test
                     let c = 10000 ;;
                     let rec fact x = if x > 1 then x * fact (x - 1) else 1 ;;
                     type UserData = { name : string; balance : int }
                     type State = { ud:UserData }
                     handler msg_handler1 (n:int) =
                      let rec fact x = fact (x - 1) in
                      let g = 1000 in
                      fact g
                    "
    let decls = [
        LetBinding ("c", false, ENum 10000);
        LetBinding ("fact", true,
                    EFunc ("x", EIf ( EGt (EVar "x", ENum 1),
                                      EMul (EVar "x", EAp (EVar "fact", ESub (EVar "x", ENum 1))),
                                      ENum 1) ));
        TypeDef ("UserData", PT [("name", String); ("balance", Int 256)]);
        TypeDef ("State", PT [("ud", UserType "UserData")]);
        HandlerDef ("msg_handler1",
                    [("n", Int 256)],
                       ELet ("fact", EFunc ("x", EAp (EVar "fact", ESub (EVar "x", ENum 1))),
                        ELet ("g", ENum 1000,
                         EAp (EVar "fact", EVar "g"))))
        ]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testMatchExpr0 () =
    let res = parse "contract test
                     handler msg_handler1 (m:List) =
                      match m with
                      | Nil -> 0
                      | Cons (h, t) -> 1 + msg_handler1 t
                    "
    let decls = [HandlerDef ("msg_handler1",
                             [("m", UserType "List")],
                             ECase (EVar "m",
                                    [(hash "Nil", [], ENum 0);
                                     (hash "Cons", ["h"; "t"],
                                      EAdd (ENum 1, EAp (EVar "msg_handler1", EVar "t")))]))
                             ]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testMatchExpr1 () =
    let res = parse "contract test
                     handler msg_handler1 (m:List) (l:List) =
                      match m with
                      | Nil ->
                           ( match l with
                             | Nil -> 0
                             | Cons (_, _) -> length l )
                      | Cons (h, t) -> 1 + msg_handler1 t
                    "
    let decls = [HandlerDef ("msg_handler1",
                  [("m",UserType "List"); ("l",UserType "List")],
                   ECase (EVar "m",
                    [(hash "Nil", [],
                       ECase (EVar "l",
                         [(hash "Nil", [], ENum 0);
                          (hash "Cons", ["_"; "_"], EAp (EVar "length", EVar "l"))]));
                     (hash "Cons", ["h"; "t"],
                       EAdd (ENum 1, EAp (EVar "msg_handler1", EVar "t")))]))
                    ]
    Assert.AreEqual( Some (Module ("test", decls)), res  );

[<Test>]
let testAssignment0 () =
    let res = parse "contract Simple

                     type State = {
                       counter: int;
                       sum: int
                     }

                     handler add_more =
                         state <- { counter = 0 ; sum = 0 }
                    "
    let decls = [TypeDef ("State", PT [("counter", Int 256); ("sum", Int 256)]);
                 HandlerDef ("add_more", [], EAssign (ERecord [ENum 0; ENum 0]))]
    Assert.AreEqual( Some (Module ("Simple", decls)), res  );

[<Test>]
let testSample0 () =
    let res = parse "contract Simple

                     type State = {
                       counter: int;
                       sum: int
                     }

                     let sum a b = a + b ;;

                     handler add_more (x: int) =
                         let sum' = sum state.counter b in
                         let counter' = b in
                         state <- { counter = counter' ; sum = sum' }
                    "
    let decls = [
        TypeDef ("State", PT [("counter", Int 256); ("sum", Int 256)]);
        LetBinding ("sum", false, EFunc ("a", EFunc ("b", EAdd (EVar "a", EVar "b"))));
        HandlerDef ("add_more", [("x", Int 256)],
                    ELet ("sum'",
                      EAp (EVar "sum",
                       EAp (ESelect (EVar "state", EVar "counter"), EVar "b")),
                        ELet ("counter'", EVar "b",
                         EAssign (ERecord [EVar "counter'"; EVar "sum'"]))))
    ]
    Assert.AreEqual( Some (Module ("Simple", decls)), res  );

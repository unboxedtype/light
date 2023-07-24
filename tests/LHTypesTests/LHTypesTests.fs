// For emacs: -*- fsharp -*-

module LHTypesTests

open NUnit.Framework
open FSharp.Text.Lexing
open type LHTypes.Type
open TestsCommon

let execAndCheck debug dataCell expected program =
    let fiftScript =
        "\"Asm.fif\" include\n" +
        dataCell + "   " +
        "<{ " + program + " }>s 1000000 gasrunvmcode drop .dump cr .dump cr"
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename fiftScript
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

[<SetUp>]
let Setup () =
    ()

(* *******************************************************************
   The algorithm will generate and add to the scope the following:
   let stateReader (c:VMCell) : State
   We want  to test  that it  works correctly for  any shape  of State
   type.
(* ******************************************************************* *) *)

let parse source : option<Module>  =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

// extract n-th type definition AST in a form of SExpr
let getTypeDefAst (n:int) (m:Module) : Type  =
    m.Decls.[n].typeDef
    |> (function | (_, t) -> t)

let getTypes debug (m:Module) : list<string * Type> =
    let types = ParserModule.getTypesDeclarationsRaw m.Decls
    let undefTypesNames =
         ParserModule.getPartiallyDefinedTypesNames types
    let undefTypesNamesList =
         undefTypesNames
         |> List.map (fun ((n, _), _) -> n)
    let defTypes =
         types
         |> List.filter (fun (n, t) -> not (List.contains n undefTypesNamesList))
    let completeTypes = ParserModule.patchPartTypes undefTypesNames defTypes
    defTypes @ completeTypes

[<Test>]
let testStateGet0 () =
    let prog = "contract StateGet
                type State = { x : int }"
    let dataCell = "<b 100 256 u, b>"
    let debug = false
    let expected = "[ 100 ]"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    parse prog
    |> Option.get
    |> getTypeDefAst 0
    |> LHTypes.deserializeValue ty
    |> execAndCheck debug dataCell expected

[<Test>]
let testStateGet1 () =
    let prog = "contract StateGet
                type State = { x : int; b : bool }"
    let dataCell = "<b 100 256 u, -1 2 i, b>"
    let debug = false
    let expected = "[ 100 -1 ]"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    parse prog
    |> Option.get
    |> getTypeDefAst 0
    |> LHTypes.deserializeValue ty
    |> execAndCheck debug dataCell expected

[<Test>]
let testStateGet2 () =
    let prog = "contract StateGet
                type Data = { x : int; b : bool }
                type State = { d : Data }"
    let dataCell = "<b 100 256 u, -1 2 i, b>"
    let debug = false
    let expected = "[ [ 100 -1 ] ]"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    (snd ty.[1])        // type without name
    |> LHTypes.deserializeValue ty
    |> execAndCheck debug dataCell expected

[<Test>]
let testStateGet3 () =
    let prog = "contract StateGet
                 type State = { bal : int }
                 type ActorState = {
                    seqno: int;
                    deployed: bool;
                    state: State
                 }"
    let dataCell = "<b 1 256 u, -1 2 i, 10000 256 u, b>"
    let debug = false
    let expected = "[ 1 -1 [ 10000 ] ]"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    (snd ty.[1])        // ActorState
    |> LHTypes.deserializeValue ty
    |> execAndCheck debug dataCell expected

[<Test>]
let testStateSet1 () =
    let prog = "contract StateGet
                 type State = { bal : int }
                 type ActorState = {
                    seqno: int;
                    deployed: bool;
                    state: State
                 }"
    let data = "100 true 1000 1 tuple 3 tuple "
    let debug = false
    let expected = "C{DC2A33271B62170F68949BB82FF51BAD0F41AC8C852F166354C732E950ABEE76}"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    (snd ty.[1])        // ActorState
    |> LHTypes.serializeValue ty
    |> execAndCheck debug data expected

[<Test>]
let testStateSet2 () =
    let prog = "contract StateGet
                 type State = { bal : int }
                 type Data = { deployed : bool }
                 type ActorState = {
                    seqno: int;
                    deployed: Data;
                    state: State
                 }"
    let data = "100 true 1 tuple 1000 1 tuple 3 tuple "
    let debug = false
    let expected = "C{DC2A33271B62170F68949BB82FF51BAD0F41AC8C852F166354C732E950ABEE76}"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    (snd ty.[2])        // ActorState
    |> LHTypes.serializeValue ty
    |> execAndCheck debug data expected

[<Test>]
let testId1 () =
    let prog = "contract StateGet
                 type State = { bal : int }
                 type Data = { deployed : bool }
                 type ActorState = {
                    seqno: int;
                    deployed: Data;
                    state: State
                 }"
    let data = "100 true 1 tuple 1000 1 tuple 3 tuple "
    let debug = false
    let expected = "[ 100 [ -1 ] [ 1000 ] ]"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    (snd ty.[2])        // ActorState
    |> (fun v -> LHTypes.serializeValue ty v +
                 LHTypes.deserializeValue ty v)
    |> execAndCheck debug data expected

[<Test>]
[<Ignore("this test will not work, because the type
          restore isn't working for deeply nested types")>]
let testId2 () =
    let prog = "contract StateGet
                 type State = { bal : int }
                 type Data = { st : State }
                 type Data2 = { d : Data }
                 type Data3 = { d : Data2 }
                 type ActorState = {
                    d: Data3
                 }"
    let data = "1000 1 tuple 1 tuple 1 tuple 1 tuple 1 tuple "
    let debug = true
    let expected = "[ [ [ [ [ 1000 ] ] ] ] ]"
    let ty =
      parse prog
      |> Option.get
      |> getTypes debug
    (snd ty.[4])        // ActorState
    |> (fun v -> LHTypes.serializeValue ty v +
                 LHTypes.deserializeValue ty v)
    |> execAndCheck debug data expected

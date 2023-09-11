// For emacs: -*- fsharp -*-
module SDKInterop

open EverscaleNet.Adapter.Rust
open EverscaleNet.Client
open EverscaleNet.Client.Models
open EverscaleNet.Models
open Microsoft.Extensions.Options
open System
open System.Runtime.InteropServices
open System.Text.Json
open System.Collections.Immutable

let EmptyCellB64 = "te6ccgEBAQEAAgAAAA=="
let [<Literal>] DllPath = "libever_assembler.so"
let DefaultGasVolume = 1_000_000_000
let DefaultWorkchainId = "0:"

[<DllImport(DllPath, CallingConvention = CallingConvention.Cdecl)>]
extern IntPtr compile_code_to_b64(IntPtr code)

let options = new OptionsWrapper<EverClientOptions>(new EverClientOptions())
let adapter = new EverClientRustAdapter(options)
let client = new EverClient(adapter)

let encodeStateInit (client:EverClient) codeB64 dataB64 =
    let mutable encSIParams = new ParamsOfEncodeStateInit ()
    encSIParams.Code <- codeB64 ;
    encSIParams.Data <- dataB64 ;
    let res =
        Async.AwaitTask (client.Boc.EncodeStateInit (encSIParams))
        |> Async.RunSynchronously
    res.StateInit

// Returns compiled byte code in a form of Base64.
let compileCode asmCode =
    let ptr = compile_code_to_b64 (Marshal.StringToCoTaskMemAnsi(asmCode))
    Marshal.PtrToStringAnsi(ptr)
    // TODO!! The memory must be de-allocated after use.

// Determine destination account id of the contract represented by
// the given state init. To create an address, you have to add
// chain id, like "0:"
let accountIdOfStateInit (client:EverClient) stateInitB64 =
    let parsOfHash = new ParamsOfHash ()
    parsOfHash.Data <- stateInitB64 ;
    let res =
        Async.AwaitTask (client.Crypto.Sha256 (parsOfHash))
        |> Async.RunSynchronously
    res.Hash

let encodeExtMsg (client:EverClient) addressFullHex bodyB64 =
    let extMsgPars = new ParamsOfEncodeExternalInMessage () ;
    extMsgPars.Dst <- addressFullHex
    extMsgPars.Body <- bodyB64 ;
    let res =
        Async.AwaitTask (client.Boc.EncodeExternalInMessage (extMsgPars))
        |> Async.RunSynchronously ;
    res.Message

let encodeInitMsg (client:EverClient) stateInitB64 =
    let extMsgPars = new ParamsOfEncodeExternalInMessage () ;
    extMsgPars.Dst <- "0:" + (accountIdOfStateInit client stateInitB64) ;
    extMsgPars.Init <- stateInitB64;
    let res =
        Async.AwaitTask (client.Boc.EncodeExternalInMessage (extMsgPars))
        |> Async.RunSynchronously ;
    res.Message

let encodeAccount (client:EverClient) stateInitB64 balance =
    let mutable pars = new ParamsOfEncodeAccount ()
    pars.StateInit <- stateInitB64 ;
    pars.Balance <- balance ;
    let resRE =
        Async.AwaitTask (client.Abi.EncodeAccount (pars))
        |> Async.RunSynchronously
    (resRE.Account, resRE.Id)

// Executes the given asm in an empty contract. Returns
// the data cell of the account, as a string in base64.
let executeCode (client:EverClient) asmCode : string =
    let codeB64 = compileCode asmCode
    let dataB64 = EmptyCellB64
    let msgBodyB64 = EmptyCellB64
    let stateInitB64 = encodeStateInit client codeB64 dataB64
    let mutable stateInitSrc = new StateInitSource.StateInit () ;
    stateInitSrc.Code <- codeB64
    stateInitSrc.Data <- dataB64
    let (acc, id) =
        encodeAccount client stateInitSrc (new System.Numerics.BigInteger (DefaultGasVolume))
    let msg = encodeExtMsg client (DefaultWorkchainId + id) EmptyCellB64
    let mutable parsOfRunExecutor = new ParamsOfRunExecutor () ;
    let mutable accExec = new AccountForExecutor.Account () ;
    accExec.Boc <- acc ;
    accExec.UnlimitedBalance <- false ;
    parsOfRunExecutor.Account <- accExec ;
    parsOfRunExecutor.Message <- msg ;
    parsOfRunExecutor.ReturnUpdatedAccount <- true ;
    let resRE =
        Async.AwaitTask (client.Tvm.RunExecutor (parsOfRunExecutor))
        |> Async.RunSynchronously
    resRE.Account

// Executes the given asm in an empty contract. Returns
// the data cell of the account, as a string in base64.
let executeTVMCode (client:EverClient) asmCode : list<Text.Json.JsonElement> =
    let codeB64 = compileCode asmCode
    let dataB64 = EmptyCellB64
    let msgBodyB64 = EmptyCellB64
    let stateInitB64 = encodeStateInit client codeB64 dataB64
    let mutable stateInitSrc = new StateInitSource.StateInit () ;
    stateInitSrc.Code <- codeB64 ;
    stateInitSrc.Data <- dataB64 ;
    let (acc, id) =
        encodeAccount client stateInitSrc (new System.Numerics.BigInteger (DefaultGasVolume))
    let mutable paramsRunGet = new ParamsOfRunGet () ;
    paramsRunGet.Account <- acc ;
    paramsRunGet.FunctionName <- "";
//  paramsRunGet.TupleListAsArray <- true;
    let mutable execOptions = new ExecutionOptions () ;
    paramsRunGet.ExecutionOptions <- execOptions ;
    let resRE =
        Async.AwaitTask (client.Tvm.RunGet (paramsRunGet))
        |> Async.RunSynchronously
    if resRE.Output.HasValue then
        // printfn "json result: %s" (resRE.Output.Value.ToString ())
        let mutable iter = resRE.Output.Value.EnumerateArray()
        let mutable res = []
        while iter.MoveNext () do
           res <- iter.Current :: res
        res
    else []

let parseAccount (client:EverClient) bocB64 =
    let mutable pars = new ParamsOfParse () ;
    pars.Boc <- bocB64 ;
    let resRE =
        Async.AwaitTask (client.Boc.ParseAccount (pars))
        |> Async.RunSynchronously
    resRE.Parsed

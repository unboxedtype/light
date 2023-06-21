// For emacs: -*- fsharp -*-
module SDKInterop

open EverscaleNet.Adapter.Rust
open EverscaleNet.Client
open EverscaleNet.Client.Models
open EverscaleNet.Models
open Microsoft.Extensions.Options
open System
open System.Runtime.InteropServices

let EmptyCellB64 = "te6ccgEBAQEAAgAAAA=="
let [<Literal>] DllPath = "libever_assembler.so"
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

// Determine destination address of the contract represented by
// the given state init. The address is given without workchain
// prefix, in hex.
let addrOfStateInit (client:EverClient) stateInitB64 =
    let parsOfHash = new ParamsOfHash ()
    parsOfHash.Data <- stateInitB64 ;
    let res =
        Async.AwaitTask (client.Crypto.Sha256 (parsOfHash))
        |> Async.RunSynchronously
    res.Hash

let encodeExtMsg (client:EverClient) addressFullHex bodyB64 =
    let extMsgPars = new ParamsOfEncodeExternalInMessage () ;
    extMsgPars.Dst <- addressFullHex ;
    extMsgPars.Body <- bodyB64 ;
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
        encodeAccount client stateInitSrc (new System.Numerics.BigInteger (1000000000))
    let msg = encodeExtMsg client ("0:" + id) EmptyCellB64
    printfn "account boc: %s" acc
    printfn "account id: %s" id
    printfn "message: %s" msg
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

let parseAccount (client:EverClient) bocB64 =
    let mutable pars = new ParamsOfParse () ;
    pars.Boc <- bocB64 ;
    let resRE =
        Async.AwaitTask (client.Boc.ParseAccount (pars))
        |> Async.RunSynchronously
    resRE.Parsed

// For emacs: -*- fsharp -*-

module FiftExecutor

open System
open System.IO
open System.Diagnostics
open System.Threading.Tasks

let FiftPath = "/usr/bin/fift"

type CommandResult = {
  ExitCode: int;
  StandardOutput: string;
  StandardError: string
}

let executeCommand (cmd: string) (args: string) =
    let psi = new Diagnostics.ProcessStartInfo(cmd, args)
    psi.UseShellExecute <- false
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.CreateNoWindow <- true
    let proc = Diagnostics.Process.Start(psi)
    let output = new Text.StringBuilder()
    let error = new Text.StringBuilder()
    proc.OutputDataReceived.Add(fun args -> output.AppendLine(args.Data) |> ignore)
    proc.ErrorDataReceived.Add(fun args -> error.AppendLine(args.Data) |> ignore)
    proc.BeginErrorReadLine()
    proc.BeginOutputReadLine()
    proc.WaitForExit()
    { ExitCode = proc.ExitCode;
      StandardOutput = output.ToString();
      StandardError = error.ToString() }

let executeShellCommand command arg =
    executeCommand command arg

let runFiftScript (scriptPath: string) : string =
    let res = executeShellCommand FiftPath scriptPath
    let out =
        res.StandardOutput.Split(Environment.NewLine) |>
            Array.collect (fun s -> [| s.Trim() |])
    if out.[0] = "0" then // VM successful completion
        out.[1]
    else
        "(empty)"

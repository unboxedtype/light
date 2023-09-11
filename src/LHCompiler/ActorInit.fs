// For emacs: -*- fsharp -*-

// Initialization code for an actor.
// Contains basic replay protection and state reading/writing.
module ActorInit

let actorInitCode =
 "
(* ActorInitParams is exactly what the Virtual Machine
   passes to the smart-contract in the beginning of execution. *)

type ActorInitArgs = {
  accBalance : int;
  msgBalance : int;
  msgCell: VMCell;
  msgBody: VMSlice;
  isExternal: bool
}

(* ActorState contains the system state of the Actor. *)
(* Replay protection is as follows:
      1. Read 4-byte integer from the message body (message identifier)
      2. Read 4-byte integer from the state        (last processed msg identifier)
      3. If integer1 is less than integer2 then proceed,
         otherwise throw error 100 (replay detected). *)
type ActorState = {
  seqNo: uint32;   (* Sending actors must consequently increase this counter *)
  deployed: bool;  (* Is actor already live inside the blockchain?           *)
  salt: uint;      (* Needed to randomise actor identifier                   *)
  state: State     (* Application state of the actor                         *)
}

type MessageBody = {
  seqNo: uint32;          (* Basic replay protection   *)
  actorMsg: ActorMessage  (* User-level message data   *)
}

type Message = {
  src: ActorId;
  dst: ActorId;
  body: MessageBody
}

let messageReader (body:VMSlice) =
  (* temporary hack not to mess with ActorId's (addresses)
     at this point *)
  let parsedBody = messageBodyReaderSlice body in
  { src = 0; dst = 0; body =  parsedBody }
;;

let putC4 (c4 : VMCell) =
  assembly { POPCTR c4; NULL } :> unit
;;

let getC4 () =
  assembly { PUSHCTR c4 } :> VMCell
;;

let acceptActor () =
  assembly { ACCEPT } :> unit
;;

(* actorStateReader and actorStateWriter functions are added
   by the compiler *)
let actorInitPost (initArgs:ActorInitArgs) =
  let actState = actorStateReader (getC4 ()) in
  (* replay protection is run only if the actor
     is already deployed, otherwise it makes no sense *)
  if actState.deployed then
      let msg = messageReader (initArgs.msgBody) in
      let msgSeqNo = msg.body.seqNo in
      if msgSeqNo <= actState.seqNo then
        failwith 100
      else
        let st = actState.state in
        (* execute the main actor code *)
        let st' = main msg.body.actorMsg st in
        let actState' =
            { seqNo = msgSeqNo;
              deployed = true;
              salt = actState.salt;
              state = st' } in
        putC4 (actorStateWriter actState')
  else
      acceptActor () ;
      (* when actor gets deployed, do not execute main;
         just save the initial state and put deployed flag
         to true *)
      let actState' = { seqNo = actState.seqNo;
                        deployed = true;
                        salt = actState.salt;
                        state = actState.state } in
      putC4 (actorStateWriter actState')
;;

let actorInit =
    actorInitPost (actorArgs)
;;
"

// For emacs: -*- fsharp -*-

// Initialization code for an actor.
// Contains basic replay protection and state reading/writing.
module ActorInit

// State type and main function shall be defined
// before this code.
// readActorState : () -> ActorState
// writeActorState : ActorState -> ()

// Replay protection is as follows:
// 1. Read 4-byte integer from the message body (message identifier)
// 2. Read 4-byte integer from the state        (last processed msg identifier)
// 3. If integer1 does not equal integer2 then proceed,
//    otherwise throw (replay detected).


// ActorInitParams is exactly what virtual machine passes to the
// smart-contract in the beginning of execution.
// This code shall be put after user code.
let actorInitCode =
  "
   type ActorInitParams = {
     accBalance : Coins;
     msgBalance : Coins;
     msgCell: VMCell;
     msgBody: VMSlice;
     isExternal: bool
   }

   type ActorState = {
     seqno: int;
     deployed: bool;
     state: State
   }

   let msgReadSeqNo (msg:VMSlice) =
       assembly \"CTOS 32 LDU DROP\" :> int ;;

   let actorStateRead () =
       { seqno = 1;
         deployed = false;
         state = stateDefault } ;;

   let actorStateWrite (st:ActorState) =
       () ;;

   let actorInitPost (initArgs:ActorInitParams) =
     let actState = actorStateRead () in
     let msgSeqNo = msgReadSeqNo initArgs.msgBody in
     if msgSeqNo  = actState.seqno then
        failwith 100
     else
        let st = actState.state in
        let st' = main initArgs.msgCell st in
        let actState' =
            { seqno = msgSeqNo;
              state = st';
              deployed = true } in
        actorStateWrite actState'
   ;;

   let actorInit =
       let actorArgs =
           (assembly \" 5 TUPLE \" :> ActorInitParams)
       in actorInitPost actorArgs
"

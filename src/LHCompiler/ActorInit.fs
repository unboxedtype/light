// For emacs: -*- fsharp -*-

// Initialization code for an actor.
// Contains basic replay protection and state reading/writing.
module ActorInit

// State type and main function shall be defined
// before this code.
// readActorState : () -> ActorState
// writeActorState : ActorState -> ()

let actorInitCode =
  "
  (* ActorInitParams is exactly what the Virtual Machine
     passes to the smart-contract in the beginning of execution. *)

   type ActorInitParams = {
     accBalance : Coins;
     msgBalance : Coins;
     msgCell: VMCell;
     msgBody: VMSlice;
     isExternal: bool
   }

   (* ActorState contains the system state of the Actor. *)
   (* Replay protection is as follows:
      1. Read 4-byte integer from the message body (message identifier)
      2. Read 4-byte integer from the state        (last processed msg identifier)
      3. If integer1 does not equal integer2 then proceed,
      otherwise throw (replay detected). *)
   type ActorState = {
     seqno: int;      (* sending actors must consequently increase this counter *)
     deployed: bool;  (* true if put inside the blockchain; false otherwise     *)
     state: State     (* application state of the actor                         *)
   }

   let msgReadSeqNo (msg : VMSlice) =
     assembly \"32 LDU DROP\" :> int ;;

   let actorStateReader (cell:VMCell) =
     { seqno = 1;
       deployed = false;
       state = stateDefault } ;;

   let actorStateWriter (st:ActorState) =
     assembly \"NEWC ENDC\" :> VMCell ;;

   let actorInitPost (initArgs:ActorInitParams) =
     let actState = actorStateReader (getC4 ()) in
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
        putC4 (actorStateWriter actState')
   ;;

   let actorInit =
       actorInitPost (actorArgs ())
   ;;
"

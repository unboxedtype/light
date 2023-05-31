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
   type ActorInitParam = {
     accBalance : Coins;
     msgBalance : Coins;
     msg: VMCell;
     msgBody: VMSlice;
     isExternal: bool
   }

   type ActorState = {
     seqno: int;
     deployed: bool;
     state: State
   }

   let msgReadSeqNo (msg:VMCell) =
       assembly \"CTOS 32 LDU DROP\" ;;

   let actorInit (initArgs:ActorInitParams) =
     let actorStateRead () =
        { seqno = 0; state = (); deployed = false } in
     let actorStateWrite st = () in
     let act_st = actorStateRead () in
     let msg_seqno = initArgs.msgBody in
     if msg_seqno  = act_st.seqno then
        failwith 100
     else
        let st = act_st.state in
        let st' = main msgCell st in
        let act_st' = { seqno = msg_seqno; state = st'; deployed = true } in
        actorStateWrite act_st'
   ;;
"

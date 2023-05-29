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


// This code shall be put after user code.
let actorInitCode =
 "type ActorState = {
   seqno: int;
   state: State
  }

  let actorInit msg is_external =
     let act_st = actorStateRead () in
     let msg_seqno = msgSeqNo msg in
     if msg_seqno  = act_st.seqno then
        failwith \"Replay detected. Rejecting the message.\"
     else
        let st = act_st.state in
        let st' = actorMain msg st in
        let act_st' = { seqno = msg_seqno; state = st' } in
        actorStateWrite act_st'
  ;;"

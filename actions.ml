type ('msg) action =
  | SendMessage of 'msg * int * int
  | Reserve of int * int

module type Actor = sig
  type state
  type inMsg
  type outMsg
  (* default function returns the default state variable values *)
  val default : state
  (* actor message handler *)
  val receive : state -> inMsg -> state * outMsg action list
end

type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

let left x =
  match x with
  | Left p -> p
  | _ -> failwith "right"

let right x =
  match x with
  | Right p -> p
  | _ -> failwith "left"

module Lifter (A:Actor) (B:Actor) = struct
  type outMsg = (A.outMsg, B.outMsg) either
  let liftA (x:A.outMsg) : outMsg  = Left x
  let liftB (x:B.outMsg) : outMsg = Right x
  let liftActA (x:A.outMsg action) : outMsg action =
    match x with
    | SendMessage (msg,id,v) -> SendMessage (liftA msg, id, v)
    | Reserve (i,p) -> Reserve (i,p)
  let liftActB (x:B.outMsg action) : outMsg action =
    match x with
    | SendMessage (msg,id,v) -> SendMessage (liftB msg, id, v)
    | Reserve (i,p) -> Reserve (i,p)
end

(* make a union of two behaviours, A and B *)
module Union (A:Actor) (B:Actor) = struct
  type state = A.state * B.state
  type inMsg = (A.inMsg, B.inMsg) either
  include Lifter (A) (B)
  type outMsg = (A.outMsg, B.outMsg) either
  let default = (A.default, B.default)

  let receive (st:state) (msg:inMsg) : state * outMsg action list  =
    match msg with
    | Left m ->
       let r = A.receive (fst st) m in  (* r = (A.state, A.outMsg action list) *)
       ((fst r, snd st), List.map liftActA (snd r))
    | Right m ->
       let r = B.receive (snd st) m in
       ((fst st, fst r), List.map liftActB (snd r))
end

(* Extend the behavior of A with the behavior of B, i.e. add new message
   types and handlers for them *)
(* Extension is allowed iff B has the same state type *)
module Extend (A:Actor) (B:Actor with type state = A.state) = struct
  type state = A.state
  type inMsg = (A.inMsg, B.inMsg) either
  include Lifter (A) (B)
  type outMsg = (A.outMsg, B.outMsg) either
  let default = A.default
  let lmsg msg : inMsg = Left msg
  let rmsg msg : inMsg = Right msg
  let receive (st:state) (msg:inMsg) : state * outMsg action list =
    match msg with
    | Left m ->
       let r = A.receive st m in
       (fst r, List.map liftActA (snd r))
    | Right m ->
       let r = B.receive st m in
       (fst r, List.map liftActB (snd r))
end

(* A patch is a new msg handler function for some distinguished
   messages, together with a function that distinguishes which
   messages to patch *)
module type Patch = sig
  type state
  type inMsg
  type outMsg
  (* shall return true for the message to be marshalled into
     new_handler *)
  val check_msg: inMsg -> bool
  (* defines new behavior for messages that pass check_msg
     filter *)
  val new_handler: state -> inMsg -> state * outMsg action list
end

(* Redefine the behavior of existing message handlers *)
module ApplyPatch (B:Actor) (P:Patch with type state = B.state and
                                          type inMsg = B.inMsg and
                                          type outMsg = B.outMsg) = struct
  type state = B.state
  type inMsg = B.inMsg
  type outMsg = B.outMsg
  let default = B.default
  let receive (st:state) (msg:inMsg) : state * outMsg action list =
    if P.check_msg msg then
      let (st', acts') = B.receive st msg in
      P.new_handler st' msg
    else
      B.receive st msg
end

module A = struct
  type state = { a : int }
  type inMsg =
    | AMessage1 of int
    | AMessage2 of int * int
  type outMsg =
    | OutMsg1 of int
    | OutMsg2 of string
  let default = { a = 0 }
  let receive (st:state) (msg:inMsg) : state * outMsg action list =
    match msg with
    | AMessage1 n ->
       ({ a = n }, [])
    | AMessage2 (n,m) ->
       ({ a = n + m }, [])
end

module B = struct
  type state = { b : int; c : int }
  type inMsg =
    | BMessage1 of int * int * int
    | BMessage2 of int * int
  type outMsg = unit
  let default = { b = 0; c = 0 }
  let receive (st:state) (msg:inMsg) : state * outMsg action list =
    match msg with
    | BMessage1 (b,c,d) ->
       ({ b = b; c = c + d }, [])
    | BMessage2 (b,c) ->
       ({ b = c; c = b }, [])
end

module C = Union (A) (B) ;;

C.receive ( { a = 10 }, { b = 1; c = 2 } ) (Right (BMessage1 (10, 20, 30))) ;;

module PatchB = struct
  type state = B.state
  type inMsg = B.inMsg
  type outMsg = B.outMsg
  let check_msg (msg:inMsg) =
    match msg with
    | BMessage2 _ -> true
    | _ -> false
  let new_handler (st:state) (msg:inMsg) : state * outMsg action list =
    match msg with
    | BMessage2 (b, c) ->
       ({ b = b + 1; c = c * 2 }, [])
    | _ ->
       failwith "unsupported message type"
end

module PatchedB = ApplyPatch (B) (PatchB)

let ast' : A.state = { a = 10 } ;;
let bst' : B.state = { b = 1; c = 2 } ;;
let st'' = (ast', bst') ;;
B.receive bst' (BMessage2 (1, 2)) ;;
PatchedB.receive bst' (BMessage2 (1, 2)) ;;

module AExt = struct
  type state = A.state
  type inMsg =
    | AExtMsg1 of int
  type outMsg = A.outMsg
  let default = A.default
  let receive (st:state) (msg:inMsg) : state * outMsg action list =
    (* ": state" is crucial here for type inference *)
    match msg with
    | AExtMsg1 n -> ({ a = n * 2 }, [])
end

module AExtended = Extend (A) (AExt) ;;

AExtended.receive { a = 10 } (AExtended.rmsg (AExtMsg1 100)) ;;
AExtended.receive { a = 10 } (AExtended.lmsg (AMessage2 (100, 200))) ;;

let actions = ref [] ;;
let sendmsg1 (msg:int) (val0:int) (flags:int) : unit =
  let acts' = !actions @ [SendMessage (msg, val0, flags)] in
  actions := acts'
;;

let mainbody1 st inmsg : state * int action list =
  let a = 10 + 20 in
  let b = a + 100 in
  sendmsg1 32443 100 1 ;
  let c = b + 1000 in
  sendmsg1 c 200 2 ;
  (st, !actions)
;;

mainbody1 { a = 100 } 200
;;

let actorMain st msg : state * int action list =
  let actions = ref [] in
  let sendmsg1 (msg:int) (val0:int) (flags:int) : unit =
    let acts' = !actions @ [SendMessage (msg, val0, flags)] in
    actions := acts'
  in
  sendmsg1 100 200 3 ;
  (st, !actions)
;;

actorMain { a = 10 } 100
;;
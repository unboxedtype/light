type action =
  | SendMessage of int * int * int
  | Reserve of int * int

module type Actor = sig
  type state
  type actmsg
  (* default function returns the default state variable values *)
  val default : state
  (* actor message handler *)
  val receive : state -> actmsg -> state * action list 
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

(* make a union of two behaviours, A and B *)
module Union (A:Actor) (B:Actor) = struct
  type state = A.state * B.state
  type actmsg = (A.actmsg, B.actmsg) either
  let default = (A.default, B.default)
  let receive (st:state) (msg:actmsg) =
    match msg with
    | Left m ->
       let r = A.receive (fst st) m in
       ((fst r, snd st), snd r)
    | Right m ->
       let r = B.receive (snd st) m in
       ((fst st, fst r), snd r)
end

(* Extend the behavior of A with the behavior of B *)
(* Extension is allowed iff B has the same state type *)
module Extend (A:Actor) (B:Actor with type state = A.state) = struct
  type state = A.state
  type actmsg = (A.actmsg, B.actmsg) either
  let default = A.default
  let lmsg msg : actmsg = Left msg
  let rmsg msg : actmsg = Right msg
  let receive (st:state) (msg:actmsg) =
    match msg with
    | Left m ->
       A.receive st m
    | Right m ->
       B.receive st m
end

(* A patch is a new msg handler function for some distinguished
   messages, together with a function that distinguishes which
   messages to patch *)
module type Patch = sig
  type state
  type actmsg
  (* shall return true for the message to be marshalled into new_handler *)
  val check_msg: actmsg -> bool
  (* defines new behavior for messages that pass check_msg filter *)
  val new_handler: state -> actmsg -> state
end

(* Redefine the behavior of existing message handlers *)
module ApplyPatch (B:Actor) (P:Patch with type state = B.state and type actmsg = B.actmsg) = struct
  type state = B.state
  type actmsg = B.actmsg
  let default = B.default
  let receive (st:state) (msg:actmsg) =
    if P.check_msg msg then
      P.new_handler st msg
    else
      B.receive st msg      
end

module A = struct
  type state = { a : int }
  type actmsg =
    | AMessage1 of int
    | AMessage2 of int * int
  let default = { a = 0 }
  let receive (st:state) (msg:actmsg) =
    match msg with
        | AMessage1 n -> { a = n }
        | AMessage2 (n,m) -> { a = n + m }
end

module B = struct
  type state = { b : int; c : int }
  type actmsg =
    | BMessage1 of int * int * int
    | BMessage2 of int * int
  let default = { b = 0; c = 0 }
  let receive (st:state) (msg:actmsg) =
    match msg with
    | BMessage1 (b,c,d) -> { b = b; c = c + d }
    | BMessage2 (b,c) -> { b = c; c = b }
end

module C = Union (A) (B) ;;

C.receive ( { a = 10 }, { b = 1; c = 2 } ) (Right (BMessage1 (10, 20, 30))) ;;

module PatchB = struct
  type state = B.state
  type actmsg = B.actmsg
  let check_msg (msg:actmsg) =
    match msg with
    | BMessage2 _ -> true
    | _ -> false
  let new_handler (st:state) (msg:actmsg) : state =
    match msg with
    | BMessage2 (b, c) ->
       { b = b; c = c }
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
  type actmsg =
    | AExtMsg1 of int
  let default = A.default
  let receive (st:state) (msg:actmsg) : state =   (* ": state" is crucial here for type inference *)
    match msg with
    | AExtMsg1 n -> { a = n * 2 }
end

module AExtended = Extend (A) (AExt) ;;

AExtended.receive { a = 10 } (AExtended.rmsg (AExtMsg1 100)) ;;
AExtended.receive { a = 10 } (AExtended.lmsg (AMessage2 (100, 200))) ;;
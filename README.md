**Disclaimer: The provided software  is a developing prototype in its
early days, not a released product.  It is provided only to be
evaluated together with  Venom Hackathon submission.   Lots of  details
described in this README are planned features, not yet implemented**


# Light

**Light**   is  a   next-generation  programming   language  targeting
TON-inspired blockchains, especially [EverX]() and [Venom](). Light is
a   statically-typed  functional   reactive  actor-based   programming
language with  lots of features  coming for the  first time ever  in a
modern blockchain programming landscape.

Light  is a  part of  bigger _Lighthouse_  programming system  aiming to
significantly boost developers productivity and program safety,
_reducing time-to-market_ and _lowering project delivery risks_.
For details, have a look at our [LightHouse Whitepaper](https://docs.google.com/document/d/1v5oPb1T8g-Vd-OBStiSlsjDg3VuqJCJdq3loqoc8KoY/edit#).

## Language Features

We highlight the following features of the Light language:

* *Algebraic Data Types with Type Parameters*

  "Product" types for records,  and "sum"-types for variants, recursive
  type  definitions,   etc.  This  type  system   provides  means  for
  specifying rich message and storage data schemes.

  ```OCaml
  (* State type defines the content and shape of the actor state *)
  type State = {
    pubkey: PubKey ;
    deposits: map<ActorId, uint> ;
    requests: list<ActorId>
  }

  (* Sum (or Variant) type define several possible constructors
     for values; you may use only one of them *)
  type Token =
  | FungibleToken of n:uint
  | NonFungibleToken of id:ActorId

  (* Recursive data types *)
  type List<'T> =
  | Nil
  | Cons of (h : T) * (t : List<T>)

  (* Optional type *)
  type Option<'T> =
  | None
  | Some of (n:T)
  ```

* *Functions as First-Class Objects*

  Function is not a dead weight, but a convenient unit of business logic
  that you  can execute,  send between actors, store,  extend or  shrink. You  can also
  store data  in the form of  a function. Functions are  recursive, with
  tail-recursion available.

  ```OCaml
  (* factorial function *)
   let rec fac n =
      if (n > 1) then n * fac (n - 1)
      else 1

   let sum a b = a + b        (* sum of two numbers, just for example *)
   let sum5 = sum 5           (* partial function application *)
   let sum105 = sum5 100      (* this equals 5 + 100 *)

   (* Tail-recursive sum of numbers list *)
   (* example: sum_list2 [1;2;3] 0  =  6   *)
   let rec sum_list2 lst acc =
     match lst with
     | [] -> acc
     | h :: t -> sum_list t (h + acc)
  ```

* *Message-oriented control flow*

  The language  provides several operators that  allow structuring the
  control flow around the message processing.
  - operator *receive*
  - operator *send (!)*

  Operator *receive* gives opportunity to express logic in a form of dialogs
  between smart-contracts.

  ```OCaml
  receive
  | Deposit (NonFungibleTokens n) ->
    if n < 100 then
      sender ! DepositFeedback (SendExtraTokens (100 - n))
      receive
      | Deposit (NonFungibleTokens p) when ctx.msg.src = sender  ->
         assert (n + p > 100) ;
         depositTokens ctx.msg.src (n + p)
      after 100 ->
         failWith #"extra deposit request failed"
  after 100 ->
    failWith #"amount is too small"
  end
  ```

  The "receive" operator "suspends" actor  execution until a new message
  arrives;  after  that, the  actor  does  the pattern-matching  on  the
  message content.  If the corresponding  pattern is found, the  body of
  the corresponding pattern handler  is executed. Unmatched messages may
  be skipped or bounced back. The operator "receive" can be nested.

* *Optional Mutability*

  Functional   programming  encourages   programming  with   immutable
  variables, but  when you  need mutability, you  still have  it, with
  familiar cycles, exceptions etc.

  ```OCaml
  try
    let mutable cond = false in
    let mutable n = 0 in
    while not cond do
      n <- n + 1 ;
      if (n > 100) then
         cond <- true ;
      if (n > 1000) then
         raise (Overflow n) ;
    done
  with
  | Overflow k ->
      // specific exception handler goes here
  | e ->
      // general exception handler goes here
  ```

* *Actors as First-class Objects*

   The language provides means to spawn ('create') other actors on the
   fly,  with convenient  programming constructs.  The actor  logic is
   passed either as module definition or as a function.

   ```OCaml
   type ActorMessage =
   | Say of (s:string)
   | Quit

   (* This is a body of another actor *)
   let rec actorFun () =
     receive
     | Say of s ->
        print s ;
        (* recursive call to itself after message received *)
        actorFun ()
     | Quit -> ()

   (* create new actor with empty state *)
   let actId = spawn actFun () in
   actId  ! Say "hi!" ;         (* Send some messages *)
   actId  ! Say "hello!" ;
   actId  ! Quit

   ```

   Spawning actors "in-place" is also possible:
   ```OCaml
   spawn ( fun () -> ctx.sender ! ("hi!") ) ;
   ```


* Static Typing with Automatic Inference

  If the program compiles, it is considered safe (runtime exception safety)
  most of the time. Strong static type system safe programmers from subtle bugs.
  However, specifying types may be dauting task. This is why Light provide
  automatic type inference.

  Types are automatically  inferred from the context.  The type safety
  is guaranteed by the compiler.

```OCaml
  let print_string s =
     print s

  (* this is also correct *)
  let print_string (s:string) =
     print s
```

* *Delayed (Lazy) Execution*

  Some pieces  of logic should be  executed only when and  if they are
  needed,  not when  they are  defined.  This  lets you  define things
  without worrying too much about suboptimal gas usage. This, in turn,
  removes the temptation  of doing premature optimization  that is, as
  we all know, the root of all evil.

  Lazy computation construct allows exactly this, in a type-safe way.

  ```OCaml
  (* We do not know how many sequence numbers we will
     need in the future. This is why we generate infinite
     stream of them, taking one at a time when we need them. *)
  let nextNumber () : Lazy<uint> =
    let mutable n:uint = 0 in
    while true do
      n <- n + 1 ;
      yield n
    done
  in
    let x = eval (nextNumber ()) in   (* x = 1 *)
    let y = eval (nextNumber ()) in   (* y = 2 *)
    x + y   (* =3 *)
  ```

## Prototype restrictions

The vision stated  in the Overview section  implemented only partially
at  the moment.   Currently,  we  implemented Light  Core  - the  core
language that lets you build all described constructs atop of it.


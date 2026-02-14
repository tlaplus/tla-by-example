import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "v11-notify-nondeterministic",
  title: "v11: Non-deterministic Notification",
  section: "blocking-queue",
  description: `A critical bugfix: the notification mechanism now non-deterministically selects which waiting thread to wake up.

## What Changed

Previously, the spec assumed a specific thread would be notified. Now it models the real behavior of notify() in Java: any one of the waiting threads can be selected.

## The Bug

If we always notify a specific thread, we miss executions where a different thread gets notified — which could lead to deadlock.

## Key Concept

When modeling a system, you must capture **all** possible behaviors, not just the ones you expect. Non-determinism is how TLA+ models situations where the system can make any of several choices.`,
  spec: `--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\\ Producers # {}                      (* at least one producer *)
       /\\ Consumers # {}                      (* at least one consumer *)
       /\\ Producers \\intersect Consumers = {} (* no thread is both consumer and producer *)
       /\\ BufCapacity \\in (Nat \\ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \\cup Consumers) \\ waitSet

(* @see java.lang.Object#notify *)       
Notify == IF waitSet # {}
          THEN \\E x \\in waitSet: waitSet' = waitSet \\ {x}
          ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\\ waitSet' = waitSet \\cup {t}
           /\\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
   \\/ /\\ Len(buffer) < BufCapacity
      /\\ buffer' = Append(buffer, d)
      /\\ Notify
   \\/ /\\ Len(buffer) = BufCapacity
      /\\ Wait(t)
      
Get(t) ==
   \\/ /\\ buffer # <<>>
      /\\ buffer' = Tail(buffer)
      /\\ Notify
   \\/ /\\ buffer = <<>>
      /\\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\\ buffer = <<>>
        /\\ waitSet = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next ==
     \\/ Notify /\\ UNCHANGED buffer \\* At each step notify all waiting threads.
     \\/ \\E t \\in RunningThreads: \\/ /\\ t \\in Producers
                                    /\\ Put(t, t) \\* Add some data to buffer
                                 \\/ /\\ t \\in Consumers
                                    /\\ Get(t)

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\\ buffer \\in Seq(Producers)
           /\\ Len(buffer) \\in 0..BufCapacity
           /\\ waitSet \\subseteq (Producers \\cup Consumers)

(* No Deadlock *)
Invariant == waitSet # (Producers \\cup Consumers)

=============================================================================`,
  cfg: `\\* SPECIFICATION
CONSTANTS
    BufCapacity = 3
    Producers = {p1,p2,p3,p4}
    Consumers = {c1,c2,c3}

INIT Init
NEXT Next

INVARIANT Invariant
INVARIANT TypeInv

CONSTANTS 
    curBuf <- AliascurBuf
    nxtBuf <- AliasnxtBuf
    Waiting <- AliasWaiting
    Scheduled <- AliasScheduled
    ConsBuf <- AliasConsBuf
    
ALIAS AnimAlias

INVARIANT AnimInv`,
};

export default lesson;

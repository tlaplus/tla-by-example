import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "v08-inequation",
  title: "v08: Deadlock-Free Inequation",
  section: "blocking-queue",
  description: `Now we infer the **inequation** under which the system is deadlock-free.

## What Changed

The spec and config are extended to systematically check when the deadlock invariant holds and when it does not.

## Key Insight

TLC finds that the system is deadlock-free when BufCapacity >= (Producers + Consumers - 1). This is a precise characterization discovered through model checking.`,
  spec: `--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\\ Producers # {}                      (* at least one producer *)
       /\\ Consumers # {}                      (* at least one consumer *)
       /\\ Producers \\intersect Consumers = {} (* no thread is both consumer and producer *)
       /\\ BufCapacity \\in (Nat \\ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet, producers, consumers, bufCapacity
vars == <<buffer, waitSet, producers, consumers, bufCapacity>>

RunningThreads == (producers \\cup consumers) \\ waitSet

(* @see java.lang.Object#notify *)       
Notify == IF waitSet # {}
          THEN \\E x \\in waitSet: waitSet' = waitSet \\ {x}
          ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\\ waitSet' = waitSet \\cup {t}
           /\\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
   \\/ /\\ Len(buffer) < bufCapacity
      /\\ buffer' = Append(buffer, d)
      /\\ Notify
   \\/ /\\ Len(buffer) = bufCapacity
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
        /\\ producers \\in (SUBSET Producers) \\ {{}}
        /\\ consumers \\in (SUBSET Consumers) \\ {{}}
        /\\ bufCapacity \\in 1..BufCapacity

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == 
    /\\  UNCHANGED <<producers, consumers, bufCapacity>>
    /\\ \\E t \\in RunningThreads: \\/ /\\ t \\in producers
                                    /\\ Put(t, t) \\* Add some data to buffer
                                 \\/ /\\ t \\in consumers
                                    /\\ Get(t)

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\\ buffer \\in Seq(Producers)
           /\\ Len(buffer) \\in 0..bufCapacity
           /\\ waitSet \\subseteq (producers \\cup consumers)

(* No Deadlock *)
Invariant == IF waitSet # (producers \\cup consumers)
             THEN TRUE \\* Inv not violated.
             ELSE PrintT(<<"InvVio", bufCapacity, Cardinality(producers \\cup consumers)>>) /\\ FALSE

(* The Permutations operator is defined in the TLC module. *)
Sym == Permutations(Producers) \\union Permutations(Consumers)

=============================================================================`,
  cfg: `\\* SPECIFICATION
CONSTANTS
    BufCapacity = 3
    Producers = {p1,p2,p3,p4}
    Consumers = {c1,c2,c3,c4}

INIT Init
NEXT Next

SYMMETRY Sym

INVARIANT Invariant
INVARIANT TypeInv`,
};

export default lesson;

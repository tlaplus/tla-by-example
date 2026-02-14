import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "v04-debug-config",
  title: "v04: Debug State Graph",
  section: "blocking-queue",
  description: `A debug configuration with 2 producers, 1 consumer, and buffer capacity 1.

## What Changed

Again just a configuration change. Different configurations expose different behaviors. The deadlock might be easier or harder to find depending on the number of producers and consumers.`,
  spec: `--------------------------- MODULE BlockingQueue ---------------------------
(***************************************************************************)
(* Original problem and spec by Michel Charpentier                         *)
(* http://www.cs.unh.edu/~charpov/programming-tlabuffer.html               *)
(***************************************************************************)
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
Next == \\E t \\in RunningThreads: \\/ /\\ t \\in Producers
                                    /\\ Put(t, t) \\* Add some data to buffer
                                 \\/ /\\ t \\in Consumers
                                    /\\ Get(t)

=============================================================================`,
  cfg: `\\* SPECIFICATION
CONSTANTS
    BufCapacity = 1
    Producers = {p1}
    Consumers = {c1,c2}

INIT Init
NEXT Next`,
};

export default lesson;

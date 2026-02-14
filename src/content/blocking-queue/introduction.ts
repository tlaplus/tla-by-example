import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "introduction",
  title: "Introduction",
  section: "blocking-queue",
  commitSha: "11410864",
  commitUrl: "https://github.com/lemmy/BlockingQueue/commit/11410864",
  description: `Tutorial-style talk **"Weeks of debugging can save you hours of TLA+"**.

This section is an adaptation of the tutorial by Markus Kuppe from the [BlockingQueue GitHub repository](https://github.com/lemmy/BlockingQueue). It was inspired by Michel Charpentier's [An Example of Debugging Java with a Model Checker](http://www.cs.unh.edu/~charpov/programming-tlabuffer.html) and Challenge 14 of the [c2 wiki](http://wiki.c2.com/?ExtremeProgrammingChallengeFourteen).

![State graph p1c1b1](/bq-images/p1c1b1.svg)

The problem we model is a **bounded buffer** (blocking queue) shared between producer and consumer threads. Producers add items to the buffer. Consumers remove items from the buffer. When the buffer is full, producers wait. When the buffer is empty, consumers wait.

## Running the Java Implementation

\`\`\`
git clone https://github.com/lemmy/BlockingQueue.git
cd BlockingQueue
java -cp impl/src/ org.kuppe.App
\`\`\`

This launches the application with the default configuration **p4c3b3** (4 producers, 3 consumers, buffer capacity 3). The application may deadlock — that is the bug we will investigate with TLA+.

## Running the C Implementation

\`\`\`
cd impl
make
./producer_consumer 3 4 3
\`\`\`

This is a C implementation of the same blocking buffer problem.

You can follow along using the [TLA+ VS Code extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) or via [Gitpod](https://gitpod.io/) / [GitHub Codespaces](https://github.com/features/codespaces).`,
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
    Consumers = {c1}

INIT Init
NEXT Next`,
  extraTabs: [
    {
      label: "Java",
      content: `// === App.java ===
package org.kuppe;

import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class App {
\tpublic static void main(String[] args) throws InterruptedException {
        final Configuration conf = new Configuration(args);
\t\tfinal int k = conf.bufCapacity;
\t\tfinal BlockingQueue<String> queue = new BlockingQueue<>(k);
\t\tfinal Collection<Callable<Void>> tasks = new HashSet<>();
\t\tfor (int i = 0; i < conf.producers; i++) {
\t\t\ttasks.add(new Producer(Integer.toString(tasks.size()), queue));
\t\t}
\t\tfor (int i = 0; i < conf.consumers; i++) {
\t\t\ttasks.add(new Consumer(queue));
\t\t}
\t\tfinal ExecutorService pool = Executors.newCachedThreadPool();
\t\tpool.invokeAll(tasks);
\t\tpool.shutdown();
\t\tpool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
\t}
\tprivate static class Configuration {
\t\tpublic final int bufCapacity;
\t\tpublic final int producers;
\t\tpublic final int consumers;
\t\tpublic Configuration(String args[]) {
\t\t\tif (args.length == 3) {
\t\t\t\tthis.bufCapacity = Integer.parseInt(args[0]);
\t\t\t\tthis.producers = Integer.parseInt(args[1]);
\t\t\t\tthis.consumers = Integer.parseInt(args[2]);
\t\t\t} else {
\t\t\t\tthis.bufCapacity = 3;
\t\t\t\tthis.producers = 4;
\t\t\t\tthis.consumers = 3;
\t\t\t}
\t\t}
\t}
}

// === BlockingQueue.java ===
package org.kuppe;

public final class BlockingQueue<E> {
\tprivate final E[] store;
\tprivate int head;
\tprivate int tail;
\tprivate int size;

\t@SuppressWarnings("unchecked")
\tpublic BlockingQueue(final int capacity) {
\t\tthis.store = (E[]) new Object[capacity];
\t}

\tpublic synchronized void put(final E e) throws InterruptedException {
\t\twhile (isFull()) {
\t\t\tSystem.out.println("Buffer full; P waits");
\t\t\twait();
\t\t\tSystem.out.println("P notified");
\t\t}
\t\tnotify();
\t\tappend(e);
\t}

\tpublic synchronized E take() throws InterruptedException {
\t\twhile (isEmpty()) {
\t\t\tSystem.out.println("Buffer empty; C waits");
\t\t\twait();
\t\t\tSystem.out.println("C notified");
\t\t}
\t\tnotify();
\t\treturn head();
\t}

\tprivate void append(final E e) {
\t\tstore[tail] = e;
\t\ttail = (tail + 1) % store.length;
\t\tsize++;
\t}

\tprivate E head() {
\t\tfinal E e = store[head];
\t\tstore[head] = null;
\t\thead = (head + 1) % store.length;
\t\tsize--;
\t\treturn e;
\t}

\tprivate boolean isFull() {
\t\treturn size == store.length;
\t}

\tprivate boolean isEmpty() {
\t\treturn size == 0;
\t}
}

// === Producer.java ===
package org.kuppe;

import java.util.Random;
import java.util.concurrent.Callable;

class Producer implements Callable<Void> {
\tprivate final int sleepProd = 42;
\tprivate final Random rand = new Random();
\tprivate final BlockingQueue<String> queue;
\tprivate final String name;

\tpublic Producer(final String name, final BlockingQueue<String> queue) {
\t\tthis.name = name;
\t\tthis.queue = queue;
\t}

\t@Override
\tpublic Void call() throws Exception {
\t\twhile (true) {
\t\t\tqueue.put(name);
\t\t\tSystem.out.printf("P put %s\\n", name);
\t\t\tThread.sleep(rand.nextInt(sleepProd));
\t\t}
\t}
}

// === Consumer.java ===
package org.kuppe;

import java.util.Random;
import java.util.concurrent.Callable;

class Consumer implements Callable<Void> {
\tprivate static final int sleepCons = 23;
\tprivate final Random rand = new Random();
\tprivate final BlockingQueue<String> queue;

\tpublic Consumer(final BlockingQueue<String> queue) {
\t\tthis.queue = queue;
\t}

\t@Override
\tpublic Void call() throws Exception {
\t\twhile (true) {
\t\t\tfinal Object take = queue.take();
\t\t\tif (take == null) throw new NullPointerException();
\t\t\tSystem.out.printf("C took %s\\n", take);
\t\t\tThread.sleep(rand.nextInt(sleepCons));
\t\t}
\t}
}`,
    },
    {
      label: "C",
      content: `// Implementation kindly provided by Aman Jain

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>

uint32_t buff_size, numProducers, numConsumers;
uint32_t *buffer;
uint32_t fillIndex, useIndex, count = 0;

pthread_cond_t empty, full; 
pthread_mutex_t mutex;

void append(uint32_t value) {
\tbuffer[fillIndex] = value;
\tfillIndex = (fillIndex + 1) % buff_size;
\tcount++;
}

uint32_t head() {
\tuint32_t tmp = buffer[useIndex];
\tuseIndex = (useIndex + 1) % buff_size;
\tcount--;
\treturn tmp;
}

void *producer (void * arg) {
\twhile(1) {
\t\tpthread_mutex_lock(&mutex);
\t\twhile (count == buff_size) {
\t\t    pthread_cond_wait(&empty, &mutex);
\t\t}
\t\tappend(rand() % (10));
\t\tpthread_cond_signal(&full);
        pthread_mutex_unlock(&mutex);
\t}
}

void *consumer (void * arg) {
\tuint32_t id = *((uint32_t *) arg);
\twhile(1) {
\t\tpthread_mutex_lock(&mutex);
\t\twhile (count == 0) {
\t\t\tpthread_cond_wait(&full, &mutex);
\t\t}
\t\thead();
\t\tpthread_cond_signal(&empty);
\t\tpthread_mutex_unlock(&mutex);
\t} 
}

int main(int argc, char * argv[]) {
\tif (argc < 4) {
\t\tprintf("Usage: ./producer_consumer <buffer_size> <#producers> <#consumers>\\n");
\t\texit(1);
\t}
\tsrand(999);
\tbuff_size = atoi(argv[1]);
\tnumProducers = atoi(argv[2]);
\tnumConsumers = atoi(argv[3]);

\tpthread_mutex_init(&mutex, NULL);
\tpthread_cond_init(&empty, NULL);
\tpthread_cond_init(&full, NULL);

\tbuffer = malloc(sizeof(int) * buff_size);
\tpthread_t prods[numProducers], cons[numConsumers];
\tuint32_t threadIds[numConsumers];

\tfor (uint32_t i = 0; i < numProducers; i++)
\t\tpthread_create(&prods[i], NULL, producer, NULL);
\tfor (uint32_t i = 0; i < numConsumers; i++) {
\t\tthreadIds[i] = i;
\t\tpthread_create(&cons[i], NULL, consumer, &threadIds[i]);
\t}

\tfor (uint32_t i = 0; i < numProducers; i++) 
\t\tpthread_join(prods[i], NULL);
\tfor (uint32_t i = 0; i < numConsumers; i++)
\t\tpthread_join(cons[i], NULL);
\treturn 0;
}`,
    },
  ],
};

export default lesson;

-------------------------- MODULE Concurrent  --------------------------

EXTENDS Naturals

VARIABLES shared, pc, local

vars == << shared, pc, local >>

N == 5

Threads == 0..(N - 1)

TypeOK == 
    /\ shared \in Nat
    /\ DOMAIN local = Threads
    /\ \A t \in Threads: local[t] \in 0..N
    /\ DOMAIN pc = Threads
    /\ \A v \in Threads: pc[v] \in { "fetch", "store", "done" }

Init ==
  /\ shared = 0
  /\ pc = [t \in Threads |-> "fetch"]
  /\ local = [t \in Threads |-> 0]

Fetch(t) == \* local = local + 1
  /\ pc[t] = "fetch"
  /\ local' = [local EXCEPT ![t] = shared]
  /\ pc' = [pc EXCEPT ![t] = "store"]
  /\ UNCHANGED << shared >>

Store(t) == \* shared = local
  /\ pc[t] = "store"
  /\ shared' = local[t] + 1
  /\ pc' = [pc EXCEPT ![t] = "done"]
  /\ UNCHANGED << local >>

Inc(t) ==
  /\ pc[t] = "fetch"
  /\ shared' = shared + 1
  /\ pc' = [pc EXCEPT ![t] = "done"]
  /\ UNCHANGED << local >>

Terminating ==
  /\ \A t \in Threads : pc[t] = "done"
  /\ UNCHANGED vars

Next == 
\*   \/ \E t \in Threads : Fetch(t)
\*   \/ \E t \in Threads : Store(t)
  \/ \E t \in Threads : Inc(t)
  \/ Terminating \* OK to stay in final state pc[t] = "done"

\* Progress == TRUE

Progress == \A t \in Threads : WF_shared(Next)

Spec == Init /\ [][Next]_vars /\ Progress

\* Correctness == TRUE

Correctness == <>(shared = N)

====

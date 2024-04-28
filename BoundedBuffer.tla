-------------------------- MODULE BoundedBuffer  --------------------------
 
EXTENDS Integers, Sequences, TLC, Naturals, FiniteSets \* dunno in profs?
 
CONSTANTS
    PSize,      \* num of printers
    WSize,      \* num of workstations
    PQCapacity  \* how many orders in the shared queue before it circles back around?
 
VARIABLES
    sharedPQ,   \* array, accessed by printers and workstations for print jobs
    size,
    head,       \* int, tracks front position in sharedPQ
    rear,       \* int, tracks end position in sharedPQ
 
    pr,         \* program counter, printer
    ws,         \* program counter, workstations
    jobCount    \* int, count of processing print jobs (those within sharedPQ)
 
vars == <<sharedPQ, size, head, rear, jobCount, pr, ws>> \* for spec
 
PrintJob == {"hello", "world", "this", "might", "work"}
 
\* to create the threads (concurrent structures interacting with sharedPQ)
Workstations == 0..(WSize - 1)
Printers == 0..(PSize - 1)
 
TypeOK ==
    \* shared circular queue consistency
    /\ sharedPQ \in [0..(PQCapacity - 1) -> STRING]     \* restricted to printjobs (represented as strings)
    /\ size <= PQCapacity  \* can't offer more print jobs to sharedPQ than its capacity
    /\ size >= 0           \* can't poll if no print jobs present
    /\ head \in 0..(PQCapacity - 1)
    /\ rear \in 0..(PQCapacity - 1)
    /\ jobCount \in Nat
    /\ pr \in [Printers -> {"start", "done"}]
    /\ ws \in [Workstations -> {"start", "done"}]
 
Init ==
    /\ head = 0
    /\ rear = PQCapacity - 1
    /\ size = 0
    /\ sharedPQ = [i \in 0..(PQCapacity - 1) |-> ""]  \* Initialize as empty strings
    /\ jobCount = 0
    /\ pr = [p \in Printers |-> "start"]
    /\ ws = [w \in Workstations |-> "start"]
 
\* OFFER = add to sharedPrinterQueue and changes "local" workstation printjob
Offer(printJob, workstation) ==
    /\ size < PQCapacity
    /\ size' = size + 1
    /\ sharedPQ' = [sharedPQ EXCEPT ![rear] = printJob]  
    /\ rear' = (rear + 1) % PQCapacity \* circle around
    /\ jobCount' = jobCount + 1
    /\ ws[workstation] = "start" \* the workstation shouldn't have sent anything yet    
    /\ ws' = [ws EXCEPT ![workstation] = "done"]
    /\ UNCHANGED <<head, pr>>
 
\* POLL = retrieves from sharedPQ and changes "pc" printer pj
Poll(printer) ==
    /\ size > 0
    /\ size' = size - 1
    /\ head' = (head + 1) % PQCapacity  \* circle around
    /\ sharedPQ' = [sharedPQ EXCEPT ![head] = ""]  
    /\ jobCount' = jobCount - 1
    /\ pr[printer] = "start"
    /\ pr' = [pr EXCEPT ![printer] = "done"]
    /\ UNCHANGED << rear, ws>>
 
Terminating ==
    /\ \A w \in Workstations : ws[w] = "done"
    /\ \A p \in Printers : pr[p] = "done"
    /\ UNCHANGED <<vars>>
 
Next ==
    \/ \E v \in PrintJob, w \in Workstations : Offer(v, w)
    \/ \E p \in Printers: Poll(p)
    \/ Terminating
 
\* TEMPORAL PROPERTIES
Progress ==
    \* ensure the workstations/printers are sending things to shared queue
    /\ \A w \in Workstations : WF_sharedPQ(Next)
    /\ \A p \in Printers : WF_sharedPQ(Next)
 
\* if workstations adds to jobCount (+1), every print should process them (-1) leaving 0
EventualConsistency == <>(jobCount = 0)
 
\* print queue (sharedPrintQueue variable) should eventually be empty
Termination == <>(\A i \in 0..(PQCapacity - 1) : sharedPQ[i] = "")
 
Spec == Init /\ [][Next]_vars /\ Progress /\ Termination /\ EventualConsistency
 
\*Correctness ==<>(jobCount = 0)
====
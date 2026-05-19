------------------------ MODULE Procedures1p1tArrayC -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N

(* PlusCal options (-label ) *)

(*--algorithm dummy {

variables ar = [ ind \in Nodes |-> ind ],  
          i = 2;


procedure change(arr, k)
{
    P1:
        arr[k] := 0;
    P2:
	    return;
}

process ( w = 1 )
variables l = 2;
{
    I:
	    i := 1;
    C:
        call change(ar,i);
    A:
	    await ar[1] = 0;
        i := i + 1;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c9b833a5" /\ chksum(tla) = "d97c74d4")
CONSTANT defaultInitValue
VARIABLES pc, ar, i, stack, arr, k, l

vars == << pc, ar, i, stack, arr, k, l >>

ProcSet == {1}

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ ar = [ ind \in Nodes |-> ind ]
        /\ i = 2
        (* Procedure change *)
        /\ arr = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ k = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        (* Process w *)
        /\ l = 2
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"I">>]

P1(self, thread) == /\ pc[self][thread] = "P1"
                    /\ arr' = [arr EXCEPT ![self][thread][k[self][thread]] = 0]
                    /\ pc' = [pc EXCEPT ![self][thread] = "P2"]
                    /\ UNCHANGED << ar, i, stack, k, l >>

P2(self, thread) == /\ pc[self][thread] = "P2"
                    /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                    /\ arr' = [arr EXCEPT ![self][thread] = Head(stack[self][thread]).arr]
                    /\ k' = [k EXCEPT ![self][thread] = Head(stack[self][thread]).k]
                    /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                    /\ UNCHANGED << ar, i, l >>

change(self, thread) == P1(self, thread) \/ P2(self, thread)

I == /\ pc[1][1]  = "I"
     /\ i' = 1
     /\ pc' = [pc EXCEPT ![1][1] = "C"]
     /\ UNCHANGED << ar, stack, arr, k, l >>

C == /\ pc[1][1]  = "C"
     /\ /\ arr' = [arr EXCEPT ![1][1] = ar]
        /\ k' = [k EXCEPT ![1][1] = i]
        /\ stack' = [stack EXCEPT ![1][1] = << [ procedure |->  "change",
                                                 pc        |->  "A",
                                                 arr       |->  arr[1][1],
                                                 k         |->  k[1][1] ] >>
                                             \o stack[1][1]]
     /\ pc' = [pc EXCEPT ![1][1] = "P1"]
     /\ UNCHANGED << ar, i, l >>

A == /\ pc[1][1]  = "A"
     /\ ar[1] = 0
     /\ i' = i + 1
     /\ pc' = [pc EXCEPT ![1][1] = "Done"]
     /\ UNCHANGED << ar, stack, arr, k, l >>

w_thread_1 == I \/ C \/ A

w == w_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == w
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  change(self, thread))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
	"compare_to": ""
}

------------------------ MODULE Procedures1p1tRecC -------------------------
EXTENDS TLC, Integers, Sequences

N == 5

(* PlusCal options (-label) *)
 
(*--algorithm Dummy {
variable c = 0,
         acc = [i \in 0 .. N |-> 0];

procedure fact(n,res) {
    Start:
        acc[n] := res;
        if ( n = 0 ) {
            c := res;
            return;
        }
        else {
            res := res * ( n-1 );
            call fact(n-1, res);
        };
    End:
        return;
}

process (id = 2)
variable lp = 3;
{
    Before:
        lp := lp + 1;
    Sdr:
        call fact(lp,1);
    After:
        skip;
} 

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "4db5b55a" /\ chksum(tla) = "3324be2b")
CONSTANT defaultInitValue
VARIABLES pc, c, acc, stack, n, res, lp

vars == << pc, c, acc, stack, n, res, lp >>

ProcSet == {2}

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ c = 0
        /\ acc = [i \in 0 .. N |-> 0]
        (* Procedure fact *)
        /\ n = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ res = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        (* Process id *)
        /\ lp = 3
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Before">>]

Start(self, thread) == /\ pc[self][thread] = "Start"
                       /\ acc' = [acc EXCEPT ![n[self][thread]] = res[self][thread]]
                       /\ IF n[self][thread] = 0
                             THEN /\ c' = res[self][thread]
                                  /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                                  /\ n' = [n EXCEPT ![self][thread] = Head(stack[self][thread]).n]
                                  /\ res' = [res EXCEPT ![self][thread] = Head(stack[self][thread]).res]
                                  /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                             ELSE /\ res' = [res EXCEPT ![self][thread] = res[self][thread] * ( n[self][thread]-1 )]
                                  /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_1"]
                                  /\ UNCHANGED << c, stack, n >>
                       /\ lp' = lp

Lbl_1(self, thread) == /\ pc[self][thread] = "Lbl_1"
                       /\ /\ n' = [n EXCEPT ![self][thread] = n[self][thread]-1]
                          /\ res' = [res EXCEPT ![self][thread] = res[self][thread]]
                          /\ stack' = [stack EXCEPT ![self][thread] = << [ procedure |->  "fact",
                                                                           pc        |->  "End",
                                                                           n         |->  n[self][thread],
                                                                           res       |->  res[self][thread] ] >>
                                                                       \o stack[self][thread]]
                       /\ pc' = [pc EXCEPT ![self][thread] = "Start"]
                       /\ UNCHANGED << c, acc, lp >>

End(self, thread) == /\ pc[self][thread] = "End"
                     /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                     /\ n' = [n EXCEPT ![self][thread] = Head(stack[self][thread]).n]
                     /\ res' = [res EXCEPT ![self][thread] = Head(stack[self][thread]).res]
                     /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                     /\ UNCHANGED << c, acc, lp >>

fact(self, thread) == Start(self, thread) \/ Lbl_1(self, thread)
                         \/ End(self, thread)

Before == /\ pc[2][1]  = "Before"
          /\ lp' = lp + 1
          /\ pc' = [pc EXCEPT ![2][1] = "Sdr"]
          /\ UNCHANGED << c, acc, stack, n, res >>

Sdr == /\ pc[2][1]  = "Sdr"
       /\ /\ n' = [n EXCEPT ![2][1] = lp]
          /\ res' = [res EXCEPT ![2][1] = 1]
          /\ stack' = [stack EXCEPT ![2][1] = << [ procedure |->  "fact",
                                                   pc        |->  "After",
                                                   n         |->  n[2][1],
                                                   res       |->  res[2][1] ] >>
                                               \o stack[2][1]]
       /\ pc' = [pc EXCEPT ![2][1] = "Start"]
       /\ UNCHANGED << c, acc, lp >>

After == /\ pc[2][1]  = "After"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![2][1] = "Done"]
         /\ UNCHANGED << c, acc, stack, n, res, lp >>

id_thread_1 == Before \/ Sdr \/ After

id == id_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  fact(self, thread))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
    "compare_to": ""
}

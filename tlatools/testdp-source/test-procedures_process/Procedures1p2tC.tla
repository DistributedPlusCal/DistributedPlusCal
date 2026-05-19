------------------------ MODULE Procedures1p2tC -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N
 
(* PlusCal options (-label  ) *)

(*--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 0;
{
    Add:
        c := x + 1;
        lv := lv + 2;
        x := lv + 3;
        return;
}

process (id = N+1)
variable lp = 10, res = 1;
{
    Before:
        lp := lp + 1;
    Sdr:
        call f(lp);
    After:
        res := lp;
} 
{
    BeforeS:
        lp := lp + 1;
    SdrS:
        call f(lp);
    AfterS:
        res := lp;
} 

} 
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3e8aadcd" /\ chksum(tla) = "a92e4061")
CONSTANT defaultInitValue
VARIABLES pc, c, stack, x, lv, lp, res

vars == << pc, c, stack, x, lv, lp, res >>

ProcSet == {N+1}

SubProcSet == [self \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lv = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Process id *)
        /\ lp = 10
        /\ res = 1
        /\ stack = [self \in ProcSet |-> << <<>> , <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Before","BeforeS">>]

Add(self, thread) == /\ pc[self][thread] = "Add"
                     /\ c' = x[self][thread] + 1
                     /\ lv' = [lv EXCEPT ![self][thread] = lv[self][thread] + 2]
                     /\ x' = [x EXCEPT ![self][thread] = lv'[self][thread] + 3]
                     /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_1"]
                     /\ UNCHANGED << stack, lp, res >>

Lbl_1(self, thread) == /\ pc[self][thread] = "Lbl_1"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lv' = [lv EXCEPT ![self][thread] = Head(stack[self][thread]).lv]
                       /\ x' = [x EXCEPT ![self][thread] = Head(stack[self][thread]).x]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << c, lp, res >>

f(self, thread) == Add(self, thread) \/ Lbl_1(self, thread)

Before == /\ pc[N+1][1]  = "Before"
          /\ lp' = lp + 1
          /\ pc' = [pc EXCEPT ![N+1][1] = "Sdr"]
          /\ UNCHANGED << c, stack, x, lv, res >>

Sdr == /\ pc[N+1][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![N+1][1] = << [ procedure |->  "f",
                                                     pc        |->  "After",
                                                     lv        |->  lv[N+1][1],
                                                     x         |->  x[N+1][1] ] >>
                                                 \o stack[N+1][1]]
          /\ x' = [x EXCEPT ![N+1][1] = lp]
       /\ lv' = [lv EXCEPT ![N+1][1] = 0]
       /\ pc' = [pc EXCEPT ![N+1][1] = "Add"]
       /\ UNCHANGED << c, lp, res >>

After == /\ pc[N+1][1]  = "After"
         /\ res' = lp
         /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
         /\ UNCHANGED << c, stack, x, lv, lp >>

id_thread_1 == Before \/ Sdr \/ After

BeforeS == /\ pc[N+1][2]  = "BeforeS"
           /\ lp' = lp + 1
           /\ pc' = [pc EXCEPT ![N+1][2] = "SdrS"]
           /\ UNCHANGED << c, stack, x, lv, res >>

SdrS == /\ pc[N+1][2]  = "SdrS"
        /\ /\ stack' = [stack EXCEPT ![N+1][2] = << [ procedure |->  "f",
                                                      pc        |->  "AfterS",
                                                      lv        |->  lv[N+1][2],
                                                      x         |->  x[N+1][2] ] >>
                                                  \o stack[N+1][2]]
           /\ x' = [x EXCEPT ![N+1][2] = lp]
        /\ lv' = [lv EXCEPT ![N+1][2] = 0]
        /\ pc' = [pc EXCEPT ![N+1][2] = "Add"]
        /\ UNCHANGED << c, lp, res >>

AfterS == /\ pc[N+1][2]  = "AfterS"
          /\ res' = lp
          /\ pc' = [pc EXCEPT ![N+1][2] = "Done"]
          /\ UNCHANGED << c, stack, x, lv, lp >>

id_thread_2 == BeforeS \/ SdrS \/ AfterS

id == id_thread_1 \/ id_thread_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  f(self, thread))
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

------------------------ MODULE Procedures2p1tAltC -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N
 
(* PlusCal options (-label ) *)

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

process (idm \in Nodes)
variable lp = 10, res = 1;
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
\* BEGIN TRANSLATION (chksum(pcal) = "baf5f5e0" /\ chksum(tla) = "81b942fe")
\* Process variable lp of process id#id_thread_1# at line 23 col 10 changed to lp_
\* Process variable res of process id#id_thread_1# at line 23 col 19 changed to res_
CONSTANT defaultInitValue
VARIABLES pc, c, stack, x, lv, lp_, res_, lp, res

vars == << pc, c, stack, x, lv, lp_, res_, lp, res >>

ProcSet == {N+1} \cup (Nodes)

SubProcSet == [self \in ProcSet |->  CASE self = N+1 -> 1..1
                                     []   self \in Nodes -> 1..1 ]

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lv = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Process id *)
        /\ lp_ = 10
        /\ res_ = 1
        (* Process idm *)
        /\ lp = [self \in Nodes |-> 10]
        /\ res = [self \in Nodes |-> 1]
        /\ stack = [self \in ProcSet |-> CASE self = N+1 -> << <<>> >>
                                           [] self \in Nodes -> << <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self = N+1 -> <<"Before">>
                                        [] self \in Nodes -> <<"BeforeS">>]

Add(self, thread) == /\ pc[self][thread] = "Add"
                     /\ c' = x[self][thread] + 1
                     /\ lv' = [lv EXCEPT ![self][thread] = lv[self][thread] + 2]
                     /\ x' = [x EXCEPT ![self][thread] = lv'[self][thread] + 3]
                     /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_1"]
                     /\ UNCHANGED << stack, lp_, res_, lp, res >>

Lbl_1(self, thread) == /\ pc[self][thread] = "Lbl_1"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lv' = [lv EXCEPT ![self][thread] = Head(stack[self][thread]).lv]
                       /\ x' = [x EXCEPT ![self][thread] = Head(stack[self][thread]).x]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << c, lp_, res_, lp, res >>

f(self, thread) == Add(self, thread) \/ Lbl_1(self, thread)

Before == /\ pc[N+1][1]  = "Before"
          /\ lp_' = lp_ + 1
          /\ pc' = [pc EXCEPT ![N+1][1] = "Sdr"]
          /\ UNCHANGED << c, stack, x, lv, res_, lp, res >>

Sdr == /\ pc[N+1][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![N+1][1] = << [ procedure |->  "f",
                                                     pc        |->  "After",
                                                     lv        |->  lv[N+1][1],
                                                     x         |->  x[N+1][1] ] >>
                                                 \o stack[N+1][1]]
          /\ x' = [x EXCEPT ![N+1][1] = lp_]
       /\ lv' = [lv EXCEPT ![N+1][1] = 0]
       /\ pc' = [pc EXCEPT ![N+1][1] = "Add"]
       /\ UNCHANGED << c, lp_, res_, lp, res >>

After == /\ pc[N+1][1]  = "After"
         /\ res_' = lp_
         /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
         /\ UNCHANGED << c, stack, x, lv, lp_, lp, res >>

id_thread_1 == Before \/ Sdr \/ After

id == id_thread_1

BeforeS(self) == /\ pc[self][1]  = "BeforeS"
                 /\ lp' = [lp EXCEPT ![self] = lp[self] + 1]
                 /\ pc' = [pc EXCEPT ![self][1] = "SdrS"]
                 /\ UNCHANGED << c, stack, x, lv, lp_, res_, res >>

SdrS(self) == /\ pc[self][1]  = "SdrS"
              /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                             pc        |->  "AfterS",
                                                             lv        |->  lv[self][1],
                                                             x         |->  x[self][1] ] >>
                                                         \o stack[self][1]]
                 /\ x' = [x EXCEPT ![self][1] = lp[self]]
              /\ lv' = [lv EXCEPT ![self][1] = 0]
              /\ pc' = [pc EXCEPT ![self][1] = "Add"]
              /\ UNCHANGED << c, lp_, res_, lp, res >>

AfterS(self) == /\ pc[self][1]  = "AfterS"
                /\ res' = [res EXCEPT ![self] = lp[self]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << c, stack, x, lv, lp_, res_, lp >>

idm_thread_1(self) == BeforeS(self) \/ SdrS(self) \/ AfterS(self)

idm(self) == idm_thread_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  f(self, thread))
           \/ (\E self \in Nodes: idm(self))
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

------------------------ MODULE Procedures2p1tC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label ) *)

N == 2
Nodes == 1 .. N
 
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
variable lpS = 10, resS = 1;
{
    BeforeS:
        lpS := lpS + 1;
    SdrS:
        call f(lpS);
    AfterS:
        resS := lpS;
} 

} 
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ec3d6339" /\ chksum(tla) = "5038d4ef")
CONSTANT defaultInitValue
VARIABLES pc, c, stack, x, lv, lp, res, lpS, resS

vars == << pc, c, stack, x, lv, lp, res, lpS, resS >>

ProcSet == {N+1} \cup (Nodes)

SubProcSet == [self \in ProcSet |->  CASE self = N+1 -> 1..1
                                     []   self \in Nodes -> 1..1 ]

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lv = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Process id *)
        /\ lp = 10
        /\ res = 1
        (* Process idm *)
        /\ lpS = [self \in Nodes |-> 10]
        /\ resS = [self \in Nodes |-> 1]
        /\ stack = [self \in ProcSet |-> CASE self = N+1 -> << <<>> >>
                                           [] self \in Nodes -> << <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self = N+1 -> <<"Before">>
                                        [] self \in Nodes -> <<"BeforeS">>]

Add(self, thread) == /\ pc[self][thread] = "Add"
                     /\ c' = x[self][thread] + 1
                     /\ lv' = [lv EXCEPT ![self][thread] = lv[self][thread] + 2]
                     /\ x' = [x EXCEPT ![self][thread] = lv'[self][thread] + 3]
                     /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_1"]
                     /\ UNCHANGED << stack, lp, res, lpS, resS >>

Lbl_1(self, thread) == /\ pc[self][thread] = "Lbl_1"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lv' = [lv EXCEPT ![self][thread] = Head(stack[self][thread]).lv]
                       /\ x' = [x EXCEPT ![self][thread] = Head(stack[self][thread]).x]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << c, lp, res, lpS, resS >>

f(self, thread) == Add(self, thread) \/ Lbl_1(self, thread)

Before == /\ pc[N+1][1]  = "Before"
          /\ lp' = lp + 1
          /\ pc' = [pc EXCEPT ![N+1][1] = "Sdr"]
          /\ UNCHANGED << c, stack, x, lv, res, lpS, resS >>

Sdr == /\ pc[N+1][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![N+1][1] = << [ procedure |->  "f",
                                                     pc        |->  "After",
                                                     lv        |->  lv[N+1][1],
                                                     x         |->  x[N+1][1] ] >>
                                                 \o stack[N+1][1]]
          /\ x' = [x EXCEPT ![N+1][1] = lp]
       /\ lv' = [lv EXCEPT ![N+1][1] = 0]
       /\ pc' = [pc EXCEPT ![N+1][1] = "Add"]
       /\ UNCHANGED << c, lp, res, lpS, resS >>

After == /\ pc[N+1][1]  = "After"
         /\ res' = lp
         /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
         /\ UNCHANGED << c, stack, x, lv, lp, lpS, resS >>

id_thread_1 == Before \/ Sdr \/ After

id == id_thread_1

BeforeS(self) == /\ pc[self][1]  = "BeforeS"
                 /\ lpS' = [lpS EXCEPT ![self] = lpS[self] + 1]
                 /\ pc' = [pc EXCEPT ![self][1] = "SdrS"]
                 /\ UNCHANGED << c, stack, x, lv, lp, res, resS >>

SdrS(self) == /\ pc[self][1]  = "SdrS"
              /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                             pc        |->  "AfterS",
                                                             lv        |->  lv[self][1],
                                                             x         |->  x[self][1] ] >>
                                                         \o stack[self][1]]
                 /\ x' = [x EXCEPT ![self][1] = lpS[self]]
              /\ lv' = [lv EXCEPT ![self][1] = 0]
              /\ pc' = [pc EXCEPT ![self][1] = "Add"]
              /\ UNCHANGED << c, lp, res, lpS, resS >>

AfterS(self) == /\ pc[self][1]  = "AfterS"
                /\ resS' = [resS EXCEPT ![self] = lpS[self]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << c, stack, x, lv, lp, res, lpS >>

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
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
	"compare_to": ""
}

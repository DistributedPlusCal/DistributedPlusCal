------------------------ MODULE Procedures2p2tFailC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label ) *)

\* CONSTANT N 
N == 2
\* CONSTANT Nodes
Nodes == 1 .. N
 
(*--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 0;
{
    Add:
        lv := lv + x + lp + c;
        c := x + 1;
        return;
}

process (pid \in Nodes)
variable lp = 10, res = 1;
{
    Before:
	    lp := lp + 1;
    Sdr:
        call f(lp);
    After:
	    res := lp;
} 

process (qid = N+1)
variable lq = 11, resq = 4;
{
    Beforeq:
	    lq := lq + 1;
    Sdrq: \* the procedure uses a variable local to process(es) pid and thus, can't be called from another process
        call f(lq);
    Afterq:
	    resq := lq;
} 
} 
*)
\* BEGIN TRANSLATION (chksum(pcal) = "92e50975" /\ chksum(tla) = "8afacb08")
CONSTANT defaultInitValue
VARIABLES pc, c, stack, x, lv, lp, res, lq, resq

vars == << pc, c, stack, x, lv, lp, res, lq, resq >>

ProcSet == (Nodes) \cup {N+1}

SubProcSet == [self \in ProcSet |->  CASE self \in Nodes -> 1..1
                                     []   self = N+1 -> 1..1 ]

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lv = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Process pid *)
        /\ lp = [self \in Nodes |-> 10]
        /\ res = [self \in Nodes |-> 1]
        (* Process qid *)
        /\ lq = 11
        /\ resq = 4
        /\ stack = [self \in ProcSet |-> CASE self \in Nodes -> << <<>> >>
                                           [] self = N+1 -> << <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Before">>
                                        [] self = N+1 -> <<"Beforeq">>]

Add(self, thread) == /\ pc[self][thread] = "Add"
                     /\ lv' = [lv EXCEPT ![self][thread] = lv[self][thread] + x[self][thread] + lp[self] + c]
                     /\ c' = x[self][thread] + 1
                     /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_1"]
                     /\ UNCHANGED << stack, x, lp, res, lq, resq >>

Lbl_1(self, thread) == /\ pc[self][thread] = "Lbl_1"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lv' = [lv EXCEPT ![self][thread] = Head(stack[self][thread]).lv]
                       /\ x' = [x EXCEPT ![self][thread] = Head(stack[self][thread]).x]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << c, lp, res, lq, resq >>

f(self, thread) == Add(self, thread) \/ Lbl_1(self, thread)

Before(self) == /\ pc[self][1]  = "Before"
                /\ lp' = [lp EXCEPT ![self] = lp[self] + 1]
                /\ pc' = [pc EXCEPT ![self][1] = "Sdr"]
                /\ UNCHANGED << c, stack, x, lv, res, lq, resq >>

Sdr(self) == /\ pc[self][1]  = "Sdr"
             /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                            pc        |->  "After",
                                                            lv        |->  lv[self][1],
                                                            x         |->  x[self][1] ] >>
                                                        \o stack[self][1]]
                /\ x' = [x EXCEPT ![self][1] = lp[self]]
             /\ lv' = [lv EXCEPT ![self][1] = 0]
             /\ pc' = [pc EXCEPT ![self][1] = "Add"]
             /\ UNCHANGED << c, lp, res, lq, resq >>

After(self) == /\ pc[self][1]  = "After"
               /\ res' = [res EXCEPT ![self] = lp[self]]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << c, stack, x, lv, lp, lq, resq >>

pid_thread_1(self) == Before(self) \/ Sdr(self) \/ After(self)

pid(self) == pid_thread_1(self)

Beforeq == /\ pc[N+1][1]  = "Beforeq"
           /\ lq' = lq + 1
           /\ pc' = [pc EXCEPT ![N+1][1] = "Sdrq"]
           /\ UNCHANGED << c, stack, x, lv, lp, res, resq >>

Sdrq == /\ pc[N+1][1]  = "Sdrq"
        /\ /\ stack' = [stack EXCEPT ![N+1][1] = << [ procedure |->  "f",
                                                      pc        |->  "Afterq",
                                                      lv        |->  lv[N+1][1],
                                                      x         |->  x[N+1][1] ] >>
                                                  \o stack[N+1][1]]
           /\ x' = [x EXCEPT ![N+1][1] = lq]
        /\ lv' = [lv EXCEPT ![N+1][1] = 0]
        /\ pc' = [pc EXCEPT ![N+1][1] = "Add"]
        /\ UNCHANGED << c, lp, res, lq, resq >>

Afterq == /\ pc[N+1][1]  = "Afterq"
          /\ resq' = lq
          /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
          /\ UNCHANGED << c, stack, x, lv, lp, res, lq >>

qid_thread_1 == Beforeq \/ Sdrq \/ Afterq

qid == qid_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == qid
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  f(self, thread))
           \/ (\E self \in Nodes: pid(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "expect-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
	"compare_to": ""
}

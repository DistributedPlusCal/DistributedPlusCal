------------------------ MODULE Procedures2p2t2pC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label ) *)

N == 2
Nodes == 1 .. N
 
(*--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 0;
{
    Addf:
        lv := lv + x + lp + c;
        c := x + 1;
        lp := lp + 11;
        return;
}

procedure foo(y)
variable lvf = 0;
{
    Addfoo:
        lvf := lvf + y + lq + c;
        lq := lq + 22;
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
{
    BeforeS:
	    lp := lp + 1;
    SdrS:
        call f(lp);
	AfterS:
	    res := lp;
} 

process (qid = N+1)
variable lq = 11, resq = 4;
{
    Beforeq:
        lq := lq + 1;
    Sdrq:
        call foo(lq);
    Afterq:
	    resq := lq;
} 
} 
*)
\* BEGIN TRANSLATION (chksum(pcal) = "efaf30d2" /\ chksum(tla) = "428222a8")
CONSTANT defaultInitValue
VARIABLES pc, c, stack, x, lv, y, lvf, lp, res, lq, resq

vars == << pc, c, stack, x, lv, y, lvf, lp, res, lq, resq >>

ProcSet == (Nodes) \cup {N+1}

SubProcSet == [self \in ProcSet |->  CASE self \in Nodes -> 1..2
                                     []   self = N+1 -> 1..1 ]

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lv = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Procedure foo *)
        /\ y = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lvf = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Process pid *)
        /\ lp = [self \in Nodes |-> 10]
        /\ res = [self \in Nodes |-> 1]
        (* Process qid *)
        /\ lq = 11
        /\ resq = 4
        /\ stack = [self \in ProcSet |-> CASE self \in Nodes -> << <<>> , <<>> >>
                                           [] self = N+1 -> << <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Before","BeforeS">>
                                        [] self = N+1 -> <<"Beforeq">>]

Addf(self, thread) == /\ pc[self][thread] = "Addf"
                      /\ lv' = [lv EXCEPT ![self][thread] = lv[self][thread] + x[self][thread] + lp[self] + c]
                      /\ c' = x[self][thread] + 1
                      /\ lp' = [lp EXCEPT ![self] = lp[self] + 11]
                      /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_1"]
                      /\ UNCHANGED << stack, x, y, lvf, res, lq, resq >>

Lbl_1(self, thread) == /\ pc[self][thread] = "Lbl_1"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lv' = [lv EXCEPT ![self][thread] = Head(stack[self][thread]).lv]
                       /\ x' = [x EXCEPT ![self][thread] = Head(stack[self][thread]).x]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << c, y, lvf, lp, res, lq, resq >>

f(self, thread) == Addf(self, thread) \/ Lbl_1(self, thread)

Addfoo(self, thread) == /\ pc[self][thread] = "Addfoo"
                        /\ lvf' = [lvf EXCEPT ![self][thread] = lvf[self][thread] + y[self][thread] + lq + c]
                        /\ lq' = lq + 22
                        /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_2"]
                        /\ UNCHANGED << c, stack, x, lv, y, lp, res, resq >>

Lbl_2(self, thread) == /\ pc[self][thread] = "Lbl_2"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lvf' = [lvf EXCEPT ![self][thread] = Head(stack[self][thread]).lvf]
                       /\ y' = [y EXCEPT ![self][thread] = Head(stack[self][thread]).y]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << c, x, lv, lp, res, lq, resq >>

foo(self, thread) == Addfoo(self, thread) \/ Lbl_2(self, thread)

Before(self) == /\ pc[self][1]  = "Before"
                /\ lp' = [lp EXCEPT ![self] = lp[self] + 1]
                /\ pc' = [pc EXCEPT ![self][1] = "Sdr"]
                /\ UNCHANGED << c, stack, x, lv, y, lvf, res, lq, resq >>

Sdr(self) == /\ pc[self][1]  = "Sdr"
             /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                            pc        |->  "After",
                                                            lv        |->  lv[self][1],
                                                            x         |->  x[self][1] ] >>
                                                        \o stack[self][1]]
                /\ x' = [x EXCEPT ![self][1] = lp[self]]
             /\ lv' = [lv EXCEPT ![self][1] = 0]
             /\ pc' = [pc EXCEPT ![self][1] = "Addf"]
             /\ UNCHANGED << c, y, lvf, lp, res, lq, resq >>

After(self) == /\ pc[self][1]  = "After"
               /\ res' = [res EXCEPT ![self] = lp[self]]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << c, stack, x, lv, y, lvf, lp, lq, resq >>

pid_thread_1(self) == Before(self) \/ Sdr(self) \/ After(self)

BeforeS(self) == /\ pc[self][2]  = "BeforeS"
                 /\ lp' = [lp EXCEPT ![self] = lp[self] + 1]
                 /\ pc' = [pc EXCEPT ![self][2] = "SdrS"]
                 /\ UNCHANGED << c, stack, x, lv, y, lvf, res, lq, resq >>

SdrS(self) == /\ pc[self][2]  = "SdrS"
              /\ /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "f",
                                                             pc        |->  "AfterS",
                                                             lv        |->  lv[self][2],
                                                             x         |->  x[self][2] ] >>
                                                         \o stack[self][2]]
                 /\ x' = [x EXCEPT ![self][2] = lp[self]]
              /\ lv' = [lv EXCEPT ![self][2] = 0]
              /\ pc' = [pc EXCEPT ![self][2] = "Addf"]
              /\ UNCHANGED << c, y, lvf, lp, res, lq, resq >>

AfterS(self) == /\ pc[self][2]  = "AfterS"
                /\ res' = [res EXCEPT ![self] = lp[self]]
                /\ pc' = [pc EXCEPT ![self][2] = "Done"]
                /\ UNCHANGED << c, stack, x, lv, y, lvf, lp, lq, resq >>

pid_thread_2(self) == BeforeS(self) \/ SdrS(self) \/ AfterS(self)

pid(self) == pid_thread_1(self) \/ pid_thread_2(self)

Beforeq == /\ pc[N+1][1]  = "Beforeq"
           /\ lq' = lq + 1
           /\ pc' = [pc EXCEPT ![N+1][1] = "Sdrq"]
           /\ UNCHANGED << c, stack, x, lv, y, lvf, lp, res, resq >>

Sdrq == /\ pc[N+1][1]  = "Sdrq"
        /\ /\ stack' = [stack EXCEPT ![N+1][1] = << [ procedure |->  "foo",
                                                      pc        |->  "Afterq",
                                                      lvf       |->  lvf[N+1][1],
                                                      y         |->  y[N+1][1] ] >>
                                                  \o stack[N+1][1]]
           /\ y' = [y EXCEPT ![N+1][1] = lq]
        /\ lvf' = [lvf EXCEPT ![N+1][1] = 0]
        /\ pc' = [pc EXCEPT ![N+1][1] = "Addfoo"]
        /\ UNCHANGED << c, x, lv, lp, res, lq, resq >>

Afterq == /\ pc[N+1][1]  = "Afterq"
          /\ resq' = lq
          /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
          /\ UNCHANGED << c, stack, x, lv, y, lvf, lp, res, lq >>

qid_thread_1 == Beforeq \/ Sdrq \/ Afterq

qid == qid_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == qid
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  f(self, thread) \/ foo(self, thread))
           \/ (\E self \in Nodes: pid(self))
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

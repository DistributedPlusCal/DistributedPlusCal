------------------------ MODULE Procedures2p2tFixC -------------------------
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

process (pid = N)
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
    Sdrq:
        call foo(lq);
    Afterq:
	    resq := lq;
} 
} 
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c12a9bf" /\ chksum(tla) = "1b5a8edc")
CONSTANT defaultInitValue
VARIABLES pc, c, stack, x, lv, y, lvf, lp, res, lq, resq

vars == << pc, c, stack, x, lv, y, lvf, lp, res, lq, resq >>

ProcSet == {N} \cup {N+1}

SubProcSet == [self \in ProcSet |->  CASE self = N -> 1..1
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
        /\ lp = 10
        /\ res = 1
        (* Process qid *)
        /\ lq = 11
        /\ resq = 4
        /\ stack = [self \in ProcSet |-> CASE self = N -> << <<>> >>
                                           [] self = N+1 -> << <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self = N -> <<"Before">>
                                        [] self = N+1 -> <<"Beforeq">>]

Addf(self, thread) == /\ pc[self][thread] = "Addf"
                      /\ lv' = [lv EXCEPT ![self][thread] = lv[self][thread] + x[self][thread] + lp + c]
                      /\ c' = x[self][thread] + 1
                      /\ lp' = lp + 11
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

Before == /\ pc[N][1]  = "Before"
          /\ lp' = lp + 1
          /\ pc' = [pc EXCEPT ![N][1] = "Sdr"]
          /\ UNCHANGED << c, stack, x, lv, y, lvf, res, lq, resq >>

Sdr == /\ pc[N][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![N][1] = << [ procedure |->  "f",
                                                   pc        |->  "After",
                                                   lv        |->  lv[N][1],
                                                   x         |->  x[N][1] ] >>
                                               \o stack[N][1]]
          /\ x' = [x EXCEPT ![N][1] = lp]
       /\ lv' = [lv EXCEPT ![N][1] = 0]
       /\ pc' = [pc EXCEPT ![N][1] = "Addf"]
       /\ UNCHANGED << c, y, lvf, lp, res, lq, resq >>

After == /\ pc[N][1]  = "After"
         /\ res' = lp
         /\ pc' = [pc EXCEPT ![N][1] = "Done"]
         /\ UNCHANGED << c, stack, x, lv, y, lvf, lp, lq, resq >>

pid_thread_1 == Before \/ Sdr \/ After

pid == pid_thread_1

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

Next == pid \/ qid
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  f(self, thread) \/ foo(self, thread))
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

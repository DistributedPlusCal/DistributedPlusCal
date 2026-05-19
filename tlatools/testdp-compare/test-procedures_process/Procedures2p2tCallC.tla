------------------------ MODULE Procedures2p2tCallC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label ) *)

\* CONSTANT N 
N == 2
\* CONSTANT Nodes
Nodes == 1 .. N
 
(*--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 2;
{
    Addf:
        c := c + x + 3;
        return;
}

procedure foo(y)
variable lvf = 0;
{
    Foo:
        lvf := 1;
        c := c + y + 1;
    Callf:
        call f(lvf);
        return;
}

process (pid \in Nodes)
variable lp = 10, res = 1;
{
    Sdr:
        call foo(lp);
} 
{
    SdrS:
        call foo(lp);
} 

process (qid = N+1)
variable lq = 11, resq = 4;
{
    Sdrq:
        call foo(lq);
} 
} 
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2cad4759" /\ chksum(tla) = "eec73bfa")
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
        /\ lv = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 2]]
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
                                           
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Sdr","SdrS">>
                                        [] self = N+1 -> <<"Sdrq">>]

Addf(self, thread) == /\ pc[self][thread] = "Addf"
                      /\ c' = c + x[self][thread] + 3
                      /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                      /\ lv' = [lv EXCEPT ![self][thread] = Head(stack[self][thread]).lv]
                      /\ x' = [x EXCEPT ![self][thread] = Head(stack[self][thread]).x]
                      /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                      /\ UNCHANGED << y, lvf, lp, res, lq, resq >>

f(self, thread) == Addf(self, thread)

Foo(self, thread) == /\ pc[self][thread] = "Foo"
                     /\ lvf' = [lvf EXCEPT ![self][thread] = 1]
                     /\ c' = c + y[self][thread] + 1
                     /\ pc' = [pc EXCEPT ![self][thread] = "Callf"]
                     /\ UNCHANGED << stack, x, lv, y, lp, res, lq, resq >>

Callf(self, thread) == /\ pc[self][thread] = "Callf"
                       /\ /\ lvf' = [lvf EXCEPT ![self][thread] = Head(stack[self][thread]).lvf]
                          /\ stack' = [stack EXCEPT ![self][thread] = << [ procedure |->  "f",
                                                                           pc        |->  Head(stack[self][thread]).pc,
                                                                           lv        |->  lv[self][thread],
                                                                           x         |->  x[self][thread] ] >>
                                                                       \o Tail(stack[self][thread])]
                          /\ x' = [x EXCEPT ![self][thread] = lvf[self][thread]]
                       /\ lv' = [lv EXCEPT ![self][thread] = 2]
                       /\ pc' = [pc EXCEPT ![self][thread] = "Addf"]
                       /\ UNCHANGED << c, y, lp, res, lq, resq >>

foo(self, thread) == Foo(self, thread) \/ Callf(self, thread)

Sdr(self) == /\ pc[self][1]  = "Sdr"
             /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "foo",
                                                            pc        |->  "Done",
                                                            lvf       |->  lvf[self][1],
                                                            y         |->  y[self][1] ] >>
                                                        \o stack[self][1]]
                /\ y' = [y EXCEPT ![self][1] = lp[self]]
             /\ lvf' = [lvf EXCEPT ![self][1] = 0]
             /\ pc' = [pc EXCEPT ![self][1] = "Foo"]
             /\ UNCHANGED << c, x, lv, lp, res, lq, resq >>

pid_thread_1(self) == Sdr(self)

SdrS(self) == /\ pc[self][2]  = "SdrS"
              /\ /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "foo",
                                                             pc        |->  "Done",
                                                             lvf       |->  lvf[self][2],
                                                             y         |->  y[self][2] ] >>
                                                         \o stack[self][2]]
                 /\ y' = [y EXCEPT ![self][2] = lp[self]]
              /\ lvf' = [lvf EXCEPT ![self][2] = 0]
              /\ pc' = [pc EXCEPT ![self][2] = "Foo"]
              /\ UNCHANGED << c, x, lv, lp, res, lq, resq >>

pid_thread_2(self) == SdrS(self)

pid(self) == pid_thread_1(self) \/ pid_thread_2(self)

Sdrq == /\ pc[N+1][1]  = "Sdrq"
        /\ /\ stack' = [stack EXCEPT ![N+1][1] = << [ procedure |->  "foo",
                                                      pc        |->  "Done",
                                                      lvf       |->  lvf[N+1][1],
                                                      y         |->  y[N+1][1] ] >>
                                                  \o stack[N+1][1]]
           /\ y' = [y EXCEPT ![N+1][1] = lq]
        /\ lvf' = [lvf EXCEPT ![N+1][1] = 0]
        /\ pc' = [pc EXCEPT ![N+1][1] = "Foo"]
        /\ UNCHANGED << c, x, lv, lp, res, lq, resq >>

qid_thread_1 == Sdrq

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
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
	"compare_to": """
}

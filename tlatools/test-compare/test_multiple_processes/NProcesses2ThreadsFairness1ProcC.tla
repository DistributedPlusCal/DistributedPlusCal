------------------------ MODULE NProcesses2ThreadsFairness1ProcC -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-label -distpcal) *)

PROCSet == 1..2

(*--algorithm Dummy {
    variables
	    x = 4,
 		i = 1;
	
    procedure f(y)
    variable lvf = 0;
    {
        FPL1:+
            lvf := lvf + 11;
        FPL2:+
            lvf := lvf + 12;
        FML1:-
			y := lvf + 21;
        FML2:-
			y := lvf + 22;
        return;
    }

    fair process(qid \in 3..4)
    {
        i := i + 4;
    }
    {
        call f(i);
    }

    fair+ process(sid = 5)
    variables lvqid = 1;
    {
        x := lvqid;
    }
    {
        i := i + 6;
        call f(23);
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "9449d94b" /\ chksum(tla) = "f732b7c6")
CONSTANT defaultInitValue
VARIABLES x, i, pc, stack, y, lvf, lvqid

vars == << x, i, pc, stack, y, lvf, lvqid >>

ProcSet == (3..4) \cup {5}

SubProcSet == [self \in ProcSet |->  CASE self \in 3..4 -> 1..2
                                     []   self = 5 -> 1..2 ]

Init == (* Global variables *)
        /\ x = 4
        /\ i = 1
        (* Procedure f *)
        /\ y = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lvf = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Process sid *)
        /\ lvqid = 1
        /\ stack = [self \in ProcSet |-> CASE self \in 3..4 -> << <<>> , <<>> >>
                                           [] self = 5 -> << <<>> , <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self \in 3..4 -> <<"Lbl_1","Lbl_2">>
                                        [] self = 5 -> <<"Lbl_3","Lbl_4">>]

FPL1(self, thread) == /\ pc[self][thread] = "FPL1"
                      /\ lvf' = [lvf EXCEPT ![self][thread] = lvf[self][thread] + 11]
                      /\ pc' = [pc EXCEPT ![self][thread] = "FPL2"]
                      /\ UNCHANGED << x, i, stack, y, lvqid >>

FPL2(self, thread) == /\ pc[self][thread] = "FPL2"
                      /\ lvf' = [lvf EXCEPT ![self][thread] = lvf[self][thread] + 12]
                      /\ pc' = [pc EXCEPT ![self][thread] = "FML1"]
                      /\ UNCHANGED << x, i, stack, y, lvqid >>

FML1(self, thread) == /\ pc[self][thread] = "FML1"
                      /\ y' = [y EXCEPT ![self][thread] = lvf[self][thread] + 21]
                      /\ pc' = [pc EXCEPT ![self][thread] = "FML2"]
                      /\ UNCHANGED << x, i, stack, lvf, lvqid >>

FML2(self, thread) == /\ pc[self][thread] = "FML2"
                      /\ y' = [y EXCEPT ![self][thread] = lvf[self][thread] + 22]
                      /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_5"]
                      /\ UNCHANGED << x, i, stack, lvf, lvqid >>

Lbl_5(self, thread) == /\ pc[self][thread] = "Lbl_5"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lvf' = [lvf EXCEPT ![self][thread] = Head(stack[self][thread]).lvf]
                       /\ y' = [y EXCEPT ![self][thread] = Head(stack[self][thread]).y]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << x, i, lvqid >>

f(self, thread) == FPL1(self, thread) \/ FPL2(self, thread)
                      \/ FML1(self, thread) \/ FML2(self, thread)
                      \/ Lbl_5(self, thread)

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 4
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << x, stack, y, lvf, lvqid >>

qid_thread_1(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self][2]  = "Lbl_2"
               /\ /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "f",
                                                              pc        |->  "Done",
                                                              lvf       |->  lvf[self][2],
                                                              y         |->  y[self][2] ] >>
                                                          \o stack[self][2]]
                  /\ y' = [y EXCEPT ![self][2] = i]
               /\ lvf' = [lvf EXCEPT ![self][2] = 0]
               /\ pc' = [pc EXCEPT ![self][2] = "FPL1"]
               /\ UNCHANGED << x, i, lvqid >>

qid_thread_2(self) == Lbl_2(self)

qid(self) == qid_thread_1(self) \/ qid_thread_2(self)

Lbl_3 == /\ pc[5][1]  = "Lbl_3"
         /\ x' = lvqid
         /\ pc' = [pc EXCEPT ![5][1] = "Done"]
         /\ UNCHANGED << i, stack, y, lvf, lvqid >>

sid_thread_1 == Lbl_3

Lbl_4 == /\ pc[5][2]  = "Lbl_4"
         /\ i' = i + 6
         /\ /\ stack' = [stack EXCEPT ![5][2] = << [ procedure |->  "f",
                                                     pc        |->  "Done",
                                                     lvf       |->  lvf[5][2],
                                                     y         |->  y[5][2] ] >>
                                                 \o stack[5][2]]
            /\ y' = [y EXCEPT ![5][2] = 23]
         /\ lvf' = [lvf EXCEPT ![5][2] = 0]
         /\ pc' = [pc EXCEPT ![5][2] = "FPL1"]
         /\ UNCHANGED << x, lvqid >>

sid_thread_2 == Lbl_4

sid == sid_thread_1 \/ sid_thread_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ (\E self \in ProcSet: \E thread \in SubProcSet[self] :  f(self, thread))
           \/ (\E self \in 3..4: qid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 3..4 : WF_vars(qid_thread_1(self))
        /\ \A self \in 3..4 : /\ WF_vars(qid_thread_2(self))
                              /\ WF_vars((pc[self][2] \notin {"FML1", "FML2"}) /\ f(self, 2))
                              /\ SF_vars(FPL1(self, 2)) /\ SF_vars(FPL2(self, 2))
        /\ SF_vars(sid_thread_1)
        /\ /\ SF_vars(sid_thread_2)
           /\ SF_vars((pc[5][2] \notin {"FML1", "FML2"}) /\ f(5, 2))

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
        "defaultInitValue": 0
    },
    "compare_to": "test_multiple_processes/NProcesses2ThreadsFairness1ProcC.tla"
}


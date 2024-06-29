------------------------ MODULE NProcesses2ThreadsFairness2ProcSetC -------------------------
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

    procedure g(z)
    variable lvg = 0;
    {
        GPL:+
            lvg := lvg + 31;
        GML:-
			z := lvg + 32;
        return;
    }

    fair process(qid \in 3..4)
    {
        i := i + 4;
        call f(54);
    }
    {
        call g(i);
        call f(i);
    }

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "8ec79859" /\ chksum(tla) = "5da341c2")
CONSTANT defaultInitValue
VARIABLES x, i, pc, stack, y, lvf, z, lvg

vars == << x, i, pc, stack, y, lvf, z, lvg >>

ProcSet == (3..4)

SubProcSet == [self \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ x = 4
        /\ i = 1
        (* Procedure f *)
        /\ y = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lvf = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        (* Procedure g *)
        /\ z = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> defaultInitValue]]
        /\ lvg = [ self \in ProcSet |-> [ thread \in SubProcSet[self] |-> 0]]
        /\ stack = [self \in ProcSet |-> << <<>> , <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Lbl_1","Lbl_2">>]

FPL1(self, thread) == /\ pc[self][thread] = "FPL1"
                      /\ lvf' = [lvf EXCEPT ![self][thread] = lvf[self][thread] + 11]
                      /\ pc' = [pc EXCEPT ![self][thread] = "FPL2"]
                      /\ UNCHANGED << x, i, stack, y, z, lvg >>

FPL2(self, thread) == /\ pc[self][thread] = "FPL2"
                      /\ lvf' = [lvf EXCEPT ![self][thread] = lvf[self][thread] + 12]
                      /\ pc' = [pc EXCEPT ![self][thread] = "FML1"]
                      /\ UNCHANGED << x, i, stack, y, z, lvg >>

FML1(self, thread) == /\ pc[self][thread] = "FML1"
                      /\ y' = [y EXCEPT ![self][thread] = lvf[self][thread] + 21]
                      /\ pc' = [pc EXCEPT ![self][thread] = "FML2"]
                      /\ UNCHANGED << x, i, stack, lvf, z, lvg >>

FML2(self, thread) == /\ pc[self][thread] = "FML2"
                      /\ y' = [y EXCEPT ![self][thread] = lvf[self][thread] + 22]
                      /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_4"]
                      /\ UNCHANGED << x, i, stack, lvf, z, lvg >>

Lbl_4(self, thread) == /\ pc[self][thread] = "Lbl_4"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lvf' = [lvf EXCEPT ![self][thread] = Head(stack[self][thread]).lvf]
                       /\ y' = [y EXCEPT ![self][thread] = Head(stack[self][thread]).y]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << x, i, z, lvg >>

f(self, thread) == FPL1(self, thread) \/ FPL2(self, thread)
                      \/ FML1(self, thread) \/ FML2(self, thread)
                      \/ Lbl_4(self, thread)

GPL(self, thread) == /\ pc[self][thread] = "GPL"
                     /\ lvg' = [lvg EXCEPT ![self][thread] = lvg[self][thread] + 31]
                     /\ pc' = [pc EXCEPT ![self][thread] = "GML"]
                     /\ UNCHANGED << x, i, stack, y, lvf, z >>

GML(self, thread) == /\ pc[self][thread] = "GML"
                     /\ z' = [z EXCEPT ![self][thread] = lvg[self][thread] + 32]
                     /\ pc' = [pc EXCEPT ![self][thread] = "Lbl_5"]
                     /\ UNCHANGED << x, i, stack, y, lvf, lvg >>

Lbl_5(self, thread) == /\ pc[self][thread] = "Lbl_5"
                       /\ pc' = [pc EXCEPT ![self][thread] = Head(stack[self][thread]).pc]
                       /\ lvg' = [lvg EXCEPT ![self][thread] = Head(stack[self][thread]).lvg]
                       /\ z' = [z EXCEPT ![self][thread] = Head(stack[self][thread]).z]
                       /\ stack' = [stack EXCEPT ![self][thread] = Tail(stack[self][thread])]
                       /\ UNCHANGED << x, i, y, lvf >>

g(self, thread) == GPL(self, thread) \/ GML(self, thread)
                      \/ Lbl_5(self, thread)

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 4
               /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                              pc        |->  "Done",
                                                              lvf       |->  lvf[self][1],
                                                              y         |->  y[self][1] ] >>
                                                          \o stack[self][1]]
                  /\ y' = [y EXCEPT ![self][1] = 54]
               /\ lvf' = [lvf EXCEPT ![self][1] = 0]
               /\ pc' = [pc EXCEPT ![self][1] = "FPL1"]
               /\ UNCHANGED << x, z, lvg >>

qid_thread_1(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self][2]  = "Lbl_2"
               /\ /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "g",
                                                              pc        |->  "Lbl_3",
                                                              lvg       |->  lvg[self][2],
                                                              z         |->  z[self][2] ] >>
                                                          \o stack[self][2]]
                  /\ z' = [z EXCEPT ![self][2] = i]
               /\ lvg' = [lvg EXCEPT ![self][2] = 0]
               /\ pc' = [pc EXCEPT ![self][2] = "GPL"]
               /\ UNCHANGED << x, i, y, lvf >>

Lbl_3(self) == /\ pc[self][2]  = "Lbl_3"
               /\ /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "f",
                                                              pc        |->  "Done",
                                                              lvf       |->  lvf[self][2],
                                                              y         |->  y[self][2] ] >>
                                                          \o stack[self][2]]
                  /\ y' = [y EXCEPT ![self][2] = i]
               /\ lvf' = [lvf EXCEPT ![self][2] = 0]
               /\ pc' = [pc EXCEPT ![self][2] = "FPL1"]
               /\ UNCHANGED << x, i, z, lvg >>

qid_thread_2(self) == Lbl_2(self) \/ Lbl_3(self)

qid(self) == qid_thread_1(self) \/ qid_thread_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: \E thread \in SubProcSet[self] :  f(self, thread) \/ g(self, thread))
           \/ (\E self \in 3..4: qid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 3..4 : /\ WF_vars(qid_thread_1(self))
                              /\ WF_vars((pc[self][1] \notin {"FML1", "FML2"}) /\ f(self, 1))
                              /\ SF_vars(FPL1(self, 1)) /\ SF_vars(FPL2(self, 1))
        /\ \A self \in 3..4 : /\ WF_vars(qid_thread_2(self))
                              /\ WF_vars((pc[self][2] # "GML") /\ g(self, 2))
                              /\ SF_vars(GPL(self, 2))                              /\ WF_vars((pc[self][2] \notin {"FML1", "FML2"}) /\ f(self, 2))
                              /\ SF_vars(FPL1(self, 2)) /\ SF_vars(FPL2(self, 2))

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
        "defaultInitValue": 0
    },
    "compare_to": "test_multiple_processes/NProcesses2ThreadsFairness2ProcSetC.tla"
}


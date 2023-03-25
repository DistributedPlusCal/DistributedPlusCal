------------------------ MODULE NProcesses2ThreadsFairness2ProcIdC -------------------------
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

    fair process(sid = 5)
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
\* BEGIN TRANSLATION (chksum(pcal) = "d737fcaa" /\ chksum(tla) = "89688db3")
CONSTANT defaultInitValue
VARIABLES x, i, pc, stack, y, lvf, z, lvg

vars == << x, i, pc, stack, y, lvf, z, lvg >>

ProcSet == {5}

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ x = 4
        /\ i = 1
        (* Procedure f *)
        /\ y = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ lvf = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> 0]]
        (* Procedure g *)
        /\ z = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ lvg = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> 0]]
        /\ stack = [self \in ProcSet |-> << <<>> , <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Lbl_1","Lbl_2">>]

FPL1(self, subprocess) == /\ pc[self][subprocess] = "FPL1"
                          /\ lvf' = [lvf EXCEPT ![self][subprocess] = lvf[self][subprocess] + 11]
                          /\ pc' = [pc EXCEPT ![self][subprocess] = "FPL2"]
                          /\ UNCHANGED << x, i, stack, y, z, lvg >>

FPL2(self, subprocess) == /\ pc[self][subprocess] = "FPL2"
                          /\ lvf' = [lvf EXCEPT ![self][subprocess] = lvf[self][subprocess] + 12]
                          /\ pc' = [pc EXCEPT ![self][subprocess] = "FML1"]
                          /\ UNCHANGED << x, i, stack, y, z, lvg >>

FML1(self, subprocess) == /\ pc[self][subprocess] = "FML1"
                          /\ y' = [y EXCEPT ![self][subprocess] = lvf[self][subprocess] + 21]
                          /\ pc' = [pc EXCEPT ![self][subprocess] = "FML2"]
                          /\ UNCHANGED << x, i, stack, lvf, z, lvg >>

FML2(self, subprocess) == /\ pc[self][subprocess] = "FML2"
                          /\ y' = [y EXCEPT ![self][subprocess] = lvf[self][subprocess] + 22]
                          /\ pc' = [pc EXCEPT ![self][subprocess] = "Lbl_4"]
                          /\ UNCHANGED << x, i, stack, lvf, z, lvg >>

Lbl_4(self, subprocess) == /\ pc[self][subprocess] = "Lbl_4"
                           /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                           /\ lvf' = [lvf EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).lvf]
                           /\ y' = [y EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).y]
                           /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                           /\ UNCHANGED << x, i, z, lvg >>

f(self, subprocess) == FPL1(self, subprocess) \/ FPL2(self, subprocess)
                          \/ FML1(self, subprocess)
                          \/ FML2(self, subprocess)
                          \/ Lbl_4(self, subprocess)

GPL(self, subprocess) == /\ pc[self][subprocess] = "GPL"
                         /\ lvg' = [lvg EXCEPT ![self][subprocess] = lvg[self][subprocess] + 31]
                         /\ pc' = [pc EXCEPT ![self][subprocess] = "GML"]
                         /\ UNCHANGED << x, i, stack, y, lvf, z >>

GML(self, subprocess) == /\ pc[self][subprocess] = "GML"
                         /\ z' = [z EXCEPT ![self][subprocess] = lvg[self][subprocess] + 32]
                         /\ pc' = [pc EXCEPT ![self][subprocess] = "Lbl_5"]
                         /\ UNCHANGED << x, i, stack, y, lvf, lvg >>

Lbl_5(self, subprocess) == /\ pc[self][subprocess] = "Lbl_5"
                           /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                           /\ lvg' = [lvg EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).lvg]
                           /\ z' = [z EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).z]
                           /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                           /\ UNCHANGED << x, i, y, lvf >>

g(self, subprocess) == GPL(self, subprocess) \/ GML(self, subprocess)
                          \/ Lbl_5(self, subprocess)

Lbl_1 == /\ pc[5][1]  = "Lbl_1"
         /\ i' = i + 4
         /\ /\ stack' = [stack EXCEPT ![5][1] = << [ procedure |->  "f",
                                                     pc        |->  "Done",
                                                     lvf       |->  lvf[5][1],
                                                     y         |->  y[5][1] ] >>
                                                 \o stack[5][1]]
            /\ y' = [y EXCEPT ![5][1] = 54]
         /\ lvf' = [lvf EXCEPT ![5][1] = 0]
         /\ pc' = [pc EXCEPT ![5][1] = "FPL1"]
         /\ UNCHANGED << x, z, lvg >>

sid1 == Lbl_1

Lbl_2 == /\ pc[5][2]  = "Lbl_2"
         /\ /\ stack' = [stack EXCEPT ![5][2] = << [ procedure |->  "g",
                                                     pc        |->  "Lbl_3",
                                                     lvg       |->  lvg[5][2],
                                                     z         |->  z[5][2] ] >>
                                                 \o stack[5][2]]
            /\ z' = [z EXCEPT ![5][2] = i]
         /\ lvg' = [lvg EXCEPT ![5][2] = 0]
         /\ pc' = [pc EXCEPT ![5][2] = "GPL"]
         /\ UNCHANGED << x, i, y, lvf >>

Lbl_3 == /\ pc[5][2]  = "Lbl_3"
         /\ /\ stack' = [stack EXCEPT ![5][2] = << [ procedure |->  "f",
                                                     pc        |->  "Done",
                                                     lvf       |->  lvf[5][2],
                                                     y         |->  y[5][2] ] >>
                                                 \o stack[5][2]]
            /\ y' = [y EXCEPT ![5][2] = i]
         /\ lvf' = [lvf EXCEPT ![5][2] = 0]
         /\ pc' = [pc EXCEPT ![5][2] = "FPL1"]
         /\ UNCHANGED << x, i, z, lvg >>

sid2 == Lbl_2 \/ Lbl_3

sid == sid1 \/ sid2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess) \/ g(self, subprocess))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(sid1)
           /\ WF_vars((pc[5][1] \notin {"FML1", "FML2"}) /\ f(5, 1))
           /\ SF_vars(FPL1(5, 1)) /\ SF_vars(FPL2(5, 1))
        /\ /\ WF_vars(sid2)
           /\ WF_vars((pc[5][2] # "GML") /\ g(5, 2)) /\ SF_vars(GPL(5, 2))
           /\ WF_vars((pc[5][2] \notin {"FML1", "FML2"}) /\ f(5, 2))
           /\ SF_vars(FPL1(5, 2)) /\ SF_vars(FPL2(5, 2))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
        "defaultInitValue": 0
    },
    "compare_to": "test_multiple_processes/NProcesses2ThreadsFairness2ProcIdC.tla"
}


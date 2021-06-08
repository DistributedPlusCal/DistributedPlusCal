------------------------ MODULE Procedures1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variable c = 0;

procedure f(x) {
    Add:
        x := x + 1;
        return;
}

process (x = 1)
{
    Sdr:
        call f(c);
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c2e52613b2f41d1a88612896d2de7950
\* Process x at line 21 col 1 changed to x_
CONSTANT defaultInitValue
VARIABLES c, pc, stack, x

vars == << c, pc, stack, x >>

ProcSet == {1}

SubProcSet == [_n \in ProcSet |-> 1]


Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Sdr">>]

Add(self, subprocess) == /\ pc[self][subprocess] = "Add"
                         /\ x' = [x EXCEPT ![self][subprocess] = x[self][subprocess] + 1]
                         /\ pc' = [pc EXCEPT ![self][subprocess] = "Lbl_1"]
                         /\ UNCHANGED << c, stack >>

Lbl_1(self, subprocess) == /\ pc[self][subprocess] = "Lbl_1"
                           /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                           /\ x' = [x EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).x]
                           /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                           /\ c' = c

f(self, subprocess) == Add(self, subprocess) \/ Lbl_1(self, subprocess)

Sdr == /\ pc[1] = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![1][1] = << [ procedure |->  "f",
                                                   pc        |->  "Done",
                                                   x         |->  x[self][1] ] >>
                                               \o stack[self][1]]
          /\ x' = [x EXCEPT ![1] = c]
       /\ pc' = [pc EXCEPT ![1][1] = "Add"]
       /\ c' = c

x_ ==  \/ Sdr

Next == x_
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9dcbd78663457d6bda7c5231809d5fb0


=========================================================

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

process (d = 1)
{
    Sdr:
        call f(c);
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-eebc6372eb6bc6922c1f9af067b1e62d
CONSTANT defaultInitValue
VARIABLES c, pc, stack, x

vars == << c, pc, stack, x >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


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

Sdr == /\ pc[1][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![1][1] = << [ procedure |->  "f",
                                                   pc        |->  "Done",
                                                   x         |->  x[1][1] ] >>
                                               \o stack[1][1]]
          /\ x' = [x EXCEPT ![1][1] = c]
       /\ pc' = [pc EXCEPT ![1][1] = "Add"]
       /\ c' = c

d == Sdr

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == d
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-575fe38411e70bc9589bc0bb79ad5947


=========================================================

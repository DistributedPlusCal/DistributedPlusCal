------------------------ MODULE Procedures1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N
 
(*
--algorithm LamportMutex {
variable c = 0;

procedure f(x) {
    Add:
        x := x + 1;
        return;
}

process (id = 1)
variable y;
{
   y := y + 1;
   Sdr:
        call f(c);
} 

process (idm \in Nodes)
variable z;
{
   z := z + 1;
   Sdrm:
        call f(c);
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f56a5e9e9c9c6de8d5dbe7286552c7c8
CONSTANT defaultInitValue
VARIABLES c, pc, stack, x, y, z

vars == << c, pc, stack, x, y, z >>

ProcSet == {1} \cup (Nodes)

SubProcSet == [n \in ProcSet |-> IF n = 1 THEN 1..1
                           ELSE (**Nodes**) 1..1]

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        (* Process id *)
        /\ y = defaultInitValue
        (* Process idm *)
        /\ z = [self \in Nodes |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> CASE self = 1 -> << <<>> >>
                                           [] self \in Nodes -> << <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> <<"Lbl_1">>
                                        [] self \in Nodes -> <<"Lbl_2">>]

Add(self, subprocess) == /\ pc[self][subprocess] = "Add"
                         /\ x' = [x EXCEPT ![self][subprocess] = x[self][subprocess] + 1]
                         /\ pc' = [pc EXCEPT ![self][subprocess] = "Lbl_3"]
                         /\ UNCHANGED << c, stack, y, z >>

Lbl_3(self, subprocess) == /\ pc[self][subprocess] = "Lbl_3"
                           /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                           /\ x' = [x EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).x]
                           /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                           /\ UNCHANGED << c, y, z >>

f(self, subprocess) == Add(self, subprocess) \/ Lbl_3(self, subprocess)

Lbl_1 == /\ pc[1][1]  = "Lbl_1"
         /\ y' = y + 1
         /\ pc' = [pc EXCEPT ![1][1] = "Sdr"]
         /\ UNCHANGED << c, stack, x, z >>

Sdr == /\ pc[1][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![1][1] = << [ procedure |->  "f",
                                                   pc        |->  "Done",
                                                   x         |->  x[1][1] ] >>
                                               \o stack[1][1]]
          /\ x' = [x EXCEPT ![1] = c]
       /\ pc' = [pc EXCEPT ![1][1] = "Add"]
       /\ UNCHANGED << c, y, z >>

id == Lbl_1 \/ Sdr

Lbl_2(self) == /\ pc[self][1]  = "Lbl_2"
               /\ z' = [z EXCEPT ![self] = z[self] + 1]
               /\ pc' = [pc EXCEPT ![self][1] = "Sdrm"]
               /\ UNCHANGED << c, stack, x, y >>

Sdrm(self) == /\ pc[self][1]  = "Sdrm"
              /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                             pc        |->  "Done",
                                                             x         |->  x[self][1] ] >>
                                                         \o stack[self][1]]
                 /\ x' = [x EXCEPT ![self] = c]
              /\ pc' = [pc EXCEPT ![self][1] = "Add"]
              /\ UNCHANGED << c, y, z >>

idm(self) == Lbl_2(self) \/ Sdrm(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))
           \/ (\E self \in Nodes: idm(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-56dfcb46c6cdf347086826f21286c391
=============================================================================

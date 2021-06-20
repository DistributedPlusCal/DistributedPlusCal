------------------------ MODULE Procedures1p1t -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
\* ASSUME N \in Nat 
\* Nodes == 1 .. N

(* PlusCal options (-distpcal) *)
 
(*
--algorithm Dummy {
variable c = 0;
procedure f(x)
variable lv = 0;
{
    Add:
        c := x + 1;
				lv := lv + 2;
				x := lv + 3;
        Lab:
        return;
}
process (id = 2)
variable lp = 10, res = 1;
{
   Before:
	      lp := lp + 1;
   Sdr:
        call f(lp);
	 After:
	      res := lp;
} 
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-68bfe5486c606720efab935f25fbcff3
CONSTANT defaultInitValue
VARIABLES c, pc, stack, x, lv, lp, res

vars == << c, pc, stack, x, lv, lp, res >>

ProcSet == {2}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ lv = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> 0]]
        (* Process id *)
        /\ lp = 10
        /\ res = 1
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Before">>]

Add(self, subprocess) == /\ pc[self][subprocess] = "Add"
                         /\ c' = x[self][subprocess] + 1
                         /\ lv' = [lv EXCEPT ![self][subprocess] = lv[self][subprocess] + 2]
                         /\ x' = [x EXCEPT ![self][subprocess] = lv'[self][subprocess] + 3]
                         /\ pc' = [pc EXCEPT ![self][subprocess] = "Lab"]
                         /\ UNCHANGED << stack, lp, res >>

Lab(self, subprocess) == /\ pc[self][subprocess] = "Lab"
                         /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                         /\ lv' = [lv EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).lv]
                         /\ x' = [x EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).x]
                         /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                         /\ UNCHANGED << c, lp, res >>

f(self, subprocess) == Add(self, subprocess) \/ Lab(self, subprocess)

Before == /\ pc[2][1]  = "Before"
          /\ lp' = lp + 1
          /\ pc' = [pc EXCEPT ![2][1] = "Sdr"]
          /\ UNCHANGED << c, stack, x, lv, res >>

Sdr == /\ pc[2][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![2][1] = << [ procedure |->  "f",
                                                   pc        |->  "After",
                                                   lv        |->  lv[2][1],
                                                   x         |->  x[2][1] ] >>
                                               \o stack[2][1]]
          /\ x' = [x EXCEPT ![2][1] = lp]
       /\ lv' = [lv EXCEPT ![2][1] = 0]
       /\ pc' = [pc EXCEPT ![2][1] = "Add"]
       /\ UNCHANGED << c, lp, res >>

After == /\ pc[2][1]  = "After"
         /\ res' = lp
         /\ pc' = [pc EXCEPT ![2][1] = "Done"]
         /\ UNCHANGED << c, stack, x, lv, lp >>

id == Before \/ Sdr \/ After

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e58d5027b051029996a3c1dbd53deff6
=============================================================================

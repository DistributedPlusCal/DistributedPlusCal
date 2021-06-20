------------------------ MODULE Procedures1p2t -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT Nodes     (* Set of process indexes *)
Nodes == 1 .. N
 
(*
--algorithm LamportMutex {
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
process (id = N+1)
variable lp = 10, res = 1;
{
   Before:
	      lp := lp + 1;
   Sdr:
        call f(lp);
	 After:
	      res := lp;
} 
process (idm \in Nodes)
variable lpS = 10, resS = 1;
{
   BeforeS:
	      lpS := lpS + 1;
   SdrS:
        call f(lpS);
	 AfterS:
	      resS := lpS;
} 
} 
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-17036f7cd9b22abbc6d320677a51c579
CONSTANT defaultInitValue
VARIABLES c, pc, stack, x, lv, lp, res, lpS, resS

vars == << c, pc, stack, x, lv, lp, res, lpS, resS >>

ProcSet == {N+1} \cup (Nodes)

SubProcSet == [_n42 \in ProcSet |-> IF _n42 = N+1 THEN 1..1
                                 ELSE (**Nodes**) 1..1]

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ lv = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> 0]]
        (* Process id *)
        /\ lp = 10
        /\ res = 1
        (* Process idm *)
        /\ lpS = [self \in Nodes |-> 10]
        /\ resS = [self \in Nodes |-> 1]
        /\ stack = [self \in ProcSet |-> CASE self = N+1 -> << <<>> >>
                                           [] self \in Nodes -> << <<>> >>]
                                           
        /\ pc = [self \in ProcSet |-> CASE self = N+1 -> <<"Before">>
                                        [] self \in Nodes -> <<"BeforeS">>]

Add(self, subprocess) == /\ pc[self][subprocess] = "Add"
                         /\ c' = x[self][subprocess] + 1
                         /\ lv' = [lv EXCEPT ![self][subprocess] = lv[self][subprocess] + 2]
                         /\ x' = [x EXCEPT ![self][subprocess] = lv'[self][subprocess] + 3]
                         /\ pc' = [pc EXCEPT ![self][subprocess] = "Lab"]
                         /\ UNCHANGED << stack, lp, res, lpS, resS >>

Lab(self, subprocess) == /\ pc[self][subprocess] = "Lab"
                         /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                         /\ lv' = [lv EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).lv]
                         /\ x' = [x EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).x]
                         /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                         /\ UNCHANGED << c, lp, res, lpS, resS >>

f(self, subprocess) == Add(self, subprocess) \/ Lab(self, subprocess)

Before == /\ pc[N+1][1]  = "Before"
          /\ lp' = lp + 1
          /\ pc' = [pc EXCEPT ![N+1][1] = "Sdr"]
          /\ UNCHANGED << c, stack, x, lv, res, lpS, resS >>

Sdr == /\ pc[N+1][1]  = "Sdr"
       /\ /\ stack' = [stack EXCEPT ![N+1][1] = << [ procedure |->  "f",
                                                     pc        |->  "After",
                                                     lv        |->  lv[N+1][1],
                                                     x         |->  x[N+1][1] ] >>
                                                 \o stack[N+1][1]]
          /\ x' = [x EXCEPT ![N+1][1] = lp]
       /\ lv' = [lv EXCEPT ![N+1][1] = 0]
       /\ pc' = [pc EXCEPT ![N+1][1] = "Add"]
       /\ UNCHANGED << c, lp, res, lpS, resS >>

After == /\ pc[N+1][1]  = "After"
         /\ res' = lp
         /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
         /\ UNCHANGED << c, stack, x, lv, lp, lpS, resS >>

id == Before \/ Sdr \/ After

BeforeS(self) == /\ pc[self][1]  = "BeforeS"
                 /\ lpS' = [lpS EXCEPT ![self] = lpS[self] + 1]
                 /\ pc' = [pc EXCEPT ![self][1] = "SdrS"]
                 /\ UNCHANGED << c, stack, x, lv, lp, res, resS >>

SdrS(self) == /\ pc[self][1]  = "SdrS"
              /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                             pc        |->  "AfterS",
                                                             lv        |->  lv[self][1],
                                                             x         |->  x[self][1] ] >>
                                                         \o stack[self][1]]
                 /\ x' = [x EXCEPT ![self][1] = lpS[self]]
              /\ lv' = [lv EXCEPT ![self][1] = 0]
              /\ pc' = [pc EXCEPT ![self][1] = "Add"]
              /\ UNCHANGED << c, lp, res, lpS, resS >>

AfterS(self) == /\ pc[self][1]  = "AfterS"
                /\ resS' = [resS EXCEPT ![self] = lpS[self]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << c, stack, x, lv, lp, res, lpS >>

idm(self) == BeforeS(self) \/ SdrS(self) \/ AfterS(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))
           \/ (\E self \in Nodes: idm(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9562eb3f56b8f68409a89c86aa2d6f4e
=============================================================================

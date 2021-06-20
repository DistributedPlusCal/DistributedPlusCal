------------------------ MODULE ProceduresRec -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
N == 5
\* ASSUME N \in Nat 
\* Nodes == 1 .. N

(* PlusCal options (-distpcal) *)
 
(*
--algorithm Dummy {

variable c = 0,
         acc = [i \in 0 .. N |-> 0];

procedure fact(n,res) {
  Start:
	  acc[n] := res;
    if ( n = 0 ) {
        c := res;
        return;
    }
    else {
        res := res * ( n-1 );
        call fact(n-1, res);
    };
  End:
	  return;
}

process (id = 2)
variable lp = 3;
{
   Before:
	      lp := lp + 1;
   Sdr:
        call fact(lp,1);
	 After:
	      skip;
} 
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ada7bc46c5ec20065023330854484228
CONSTANT defaultInitValue
VARIABLES c, acc, pc, stack, n, res, lp

vars == << c, acc, pc, stack, n, res, lp >>

ProcSet == {2}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ c = 0
        /\ acc = [i \in 0 .. N |-> 0]
        (* Procedure fact *)
        /\ n = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ res = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        (* Process id *)
        /\ lp = 3
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Before">>]

Start(self, subprocess) == /\ pc[self][subprocess] = "Start"
                           /\ acc' = [acc EXCEPT ![n[self][subprocess]] = res[self][subprocess]]
                           /\ IF n[self][subprocess] = 0
                                 THEN /\ c' = res[self][subprocess]
                                      /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                                      /\ n' = [n EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).n]
                                      /\ res' = [res EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).res]
                                      /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                                 ELSE /\ res' = [res EXCEPT ![self][subprocess] = res[self][subprocess] * ( n[self][subprocess]-1 )]
                                      /\ pc' = [pc EXCEPT ![self][subprocess] = "Lbl_1"]
                                      /\ UNCHANGED << c, stack, n >>
                           /\ lp' = lp

Lbl_1(self, subprocess) == /\ pc[self][subprocess] = "Lbl_1"
                           /\ /\ n' = [n EXCEPT ![self][subprocess] = n[self][subprocess]-1]
                              /\ res' = [res EXCEPT ![self][subprocess] = res[self][subprocess]]
                              /\ stack' = [stack EXCEPT ![self][subprocess] = << [ procedure |->  "fact",
                                                                                   pc        |->  "End",
                                                                                   n         |->  n[self][subprocess],
                                                                                   res       |->  res[self][subprocess] ] >>
                                                                               \o stack[self][subprocess]]
                           /\ pc' = [pc EXCEPT ![self][subprocess] = "Start"]
                           /\ UNCHANGED << c, acc, lp >>

End(self, subprocess) == /\ pc[self][subprocess] = "End"
                         /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                         /\ n' = [n EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).n]
                         /\ res' = [res EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).res]
                         /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                         /\ UNCHANGED << c, acc, lp >>

fact(self, subprocess) == Start(self, subprocess)
                             \/ Lbl_1(self, subprocess)
                             \/ End(self, subprocess)

Before == /\ pc[2][1]  = "Before"
          /\ lp' = lp + 1
          /\ pc' = [pc EXCEPT ![2][1] = "Sdr"]
          /\ UNCHANGED << c, acc, stack, n, res >>

Sdr == /\ pc[2][1]  = "Sdr"
       /\ /\ n' = [n EXCEPT ![2][1] = lp]
          /\ res' = [res EXCEPT ![2][1] = 1]
          /\ stack' = [stack EXCEPT ![2][1] = << [ procedure |->  "fact",
                                                   pc        |->  "After",
                                                   n         |->  n[2][1],
                                                   res       |->  res[2][1] ] >>
                                               \o stack[2][1]]
       /\ pc' = [pc EXCEPT ![2][1] = "Start"]
       /\ UNCHANGED << c, acc, lp >>

After == /\ pc[2][1]  = "After"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![2][1] = "Done"]
         /\ UNCHANGED << c, acc, stack, n, res, lp >>

id == Before \/ Sdr \/ After

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == id
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  fact(self, subprocess))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-30f8195f1eba7b521325b2d707c19e1f

=============================================================================

------------------------ MODULE OneProcessMultiThread1aC -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {
variables cur = "none",
          i = 1;
process ( w \in Nodes )
variables l = 2;
{
	Write:
  	while ( TRUE ) 
  	{
          i := i+1;
					l := l+2;
  	}
} {
	Read:
  	while ( TRUE ) {
          i := i+1;
					l := l+2;    	    
  	}
}
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-be73ce9fab46f590f1458c29ea1b0729
VARIABLES cur, i, pc, l

vars == << cur, i, pc, l >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ cur = "none"
        /\ i = 1
        (* Process w *)
        /\ l = [self \in Nodes |-> 2]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ i' = i+1
               /\ l' = [l EXCEPT ![self] = l[self]+2]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]
               /\ cur' = cur

Read(self) == /\ pc[self][2]  = "Read"
              /\ i' = i+1
              /\ l' = [l EXCEPT ![self] = l[self]+2]
              /\ pc' = [pc EXCEPT ![self][2] = "Read"]
              /\ cur' = cur

w(self) == Write(self) \/ Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-83ace762c60aa14a753a3518904447f8


=============================================================================

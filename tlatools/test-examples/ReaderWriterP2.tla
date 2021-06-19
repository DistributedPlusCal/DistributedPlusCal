------------------------ MODULE ReaderWriterP2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo


channel chan;

process w = "Writer"
variable cur = "none";
begin
	Write:
  	while ( TRUE ) do
      	    send(chan, "msg");
  	end while;
end process;
begin
	Read:
  	while ( TRUE ) do
    	    receive(chan, cur);
  	end while;
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6876cd532f3a7485d52bc516057b894c
VARIABLES chan, pc, cur

vars == << chan, pc, cur >>

ProcSet == {"Writer"}

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = {}
        (* Process w *)
        /\ cur = "none"
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write == /\ pc["Writer"][1]  = "Write"
         /\ chan' = (chan \cup {"msg"})
         /\ pc' = [pc EXCEPT !["Writer"][1] = "Write"]
         /\ cur' = cur

Read == /\ pc["Writer"][2]  = "Read"
        /\ \E _c149 \in chan:
             /\ chan' = chan \ {_c149}
             /\ cur' = _c149
        /\ pc' = [pc EXCEPT !["Writer"][2] = "Read"]

w == Write \/ Read

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == w
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a408b2da71fd6e7d21e074dc5723677e

==========================================================

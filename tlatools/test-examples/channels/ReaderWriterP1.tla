------------------------ MODULE ReaderWriterP1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm f_queue_algo

variable cur = "none";
fifo f_queue;

process w = "writer"
begin
	Write:
  	while ( TRUE ) do
    	    send(f_queue, "msg");
  	end while;
end process;
begin
	Read:
  	while ( TRUE ) do
    	     receive(f_queue, cur);
  	end while;
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c4307087891719bcb71f35f945fb8fd4
VARIABLES cur, f_queue, pc

vars == << cur, f_queue, pc >>

ProcSet == {"writer"}

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ cur = "none"
        /\ f_queue = <<>>
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write == /\ pc["writer"][1]  = "Write"
         /\ f_queue' =  Append(f_queue, "msg")
         /\ pc' = [pc EXCEPT !["writer"][1] = "Write"]
         /\ cur' = cur

Read == /\ pc["writer"][2]  = "Read"
        /\ Len(f_queue) > 0 
        /\ cur' = Head(f_queue)
        /\ f_queue' =  Tail(f_queue)
        /\ pc' = [pc EXCEPT !["writer"][2] = "Read"]

w == Write \/ Read

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == w
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ef1aad069ff53304e4c701977f700025

==========================================================

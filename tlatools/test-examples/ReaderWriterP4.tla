------------------------ MODULE ReaderWriterP4 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

variable cur = "none";
fifo f_chan[Nodes];

process w \in Nodes
begin
	Write:
  	while ( TRUE ) do
      	    send(f_chan[self], "msg");
  	end while;
end process;
begin
	Read:
		receive(f_chan[self], cur);
end subprocess;

process r = 99
begin
	Clear:  	
    	    clear(f_chan);  	
end process;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a61e9c3a0a14f79aecc36f18621c1513
VARIABLES cur, f_chan, pc

vars == << cur, f_chan, pc >>

ProcSet == (Nodes) \cup {99}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Nodes THEN 1..2
                                   ELSE (**99**) 1..1]

Init == (* Global variables *)
        /\ cur = "none"
        /\ f_chan = [_n430 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Write","Read">>
                                        [] self = 99 -> <<"Clear">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ f_chan' = [f_chan EXCEPT ![self] =  Append(@, "msg")]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]
               /\ cur' = cur

Read(self) == /\ pc[self][2]  = "Read"
              /\ Len(f_chan[self]) > 0 
              /\ cur' = Head(f_chan[self])
              /\ f_chan' = [f_chan EXCEPT ![self] =  Tail(@) ]
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) == Write(self) \/ Read(self)

Clear == /\ pc[99][1]  = "Clear"
         /\ f_chan' = [_n0 \in Nodes |-> <<>>]
         /\ pc' = [pc EXCEPT ![99][1] = "Done"]
         /\ cur' = cur

r == Clear

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == r
           \/ (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c39c85587c9ff6aeb6e49607616168d1

==========================================================

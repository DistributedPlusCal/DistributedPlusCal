------------------------ MODULE ReaderWriterC4 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
channel f_chan[Nodes];

process ( w \in Nodes )
{
	Write:
  	while ( TRUE ) 
  	{
            send(f_chan[self], "msg");
  	}
} {
	Read:
  	while ( TRUE ) {
    	     receive(f_chan[self], cur);
  	}
} {
	Clear:
	   clear(f_chan);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0367f4c5dd46e452a8c183c9b4756bac
VARIABLES cur, f_chan, pc

vars == << cur, f_chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ cur = "none"
        /\ f_chan = [_n0 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"Write","Read","Clear">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ f_chan' = [f_chan EXCEPT ![self] = f_chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]
               /\ cur' = cur

Read(self) == /\ pc[self] [2] = "Read"
              /\ \E _f149 \in f_chan[self]:
                   /\ cur' = _f149
                   /\ f_chan' = [f_chan EXCEPT ![self] = f_chan[self] \ {_f149}]
              /\ pc' = [pc EXCEPT ![self][2] = "Read"]

Clear(self) == /\ pc[self] [3] = "Clear"
               /\ f_chan' = [_n0 \in Nodes |-> {}]
               /\ pc' = [pc EXCEPT ![self][3] = "Done"]
               /\ cur' = cur

w(self) ==  \/ Write(self) \/ Read(self) \/ Clear(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-d5b9df1aa98ffdfe3f5332f48bf2d4c1

==========================================================

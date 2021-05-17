------------------------ MODULE ReaderWriterC3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
channel chan[Nodes];

process ( w \in Nodes )
{
	Write:
  	while ( TRUE ) 
  	{
            send(chan[self], "msg");
  	}
} {
	Read:
  	while ( TRUE ) {
    	     receive(chan[self], cur);
  	}
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-dcaeb3042df49dd73005b89124f0a5d8
VARIABLES cur, chan

vars == << cur, chan >>

ProcSet == (Nodes)

SubProcSet == [n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [n0 \in Nodes |-> {}]

w(self) == /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
           /\ cur' = cur

w(self) == \E c149 \in chan[self]:
             /\ chan' = [chan EXCEPT ![self] = chan[self] \ {c149}]
             /\ cur' = c149

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6b64f80b651a41bbdcad0f19d35d629b

==========================================================

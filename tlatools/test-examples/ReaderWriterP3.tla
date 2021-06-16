------------------------ MODULE ReaderWriterP3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel chan;

process w \in Nodes
variable msg;
begin
	Rec:
      	    receive(chan, msg);
end process;
begin
     Send:
          send(chan, "msg");
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c59a496be840eb786ff4d919258c9ae2
CONSTANT defaultInitValue
VARIABLES chan, pc, msg

vars == << chan, pc, msg >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = {}
        (* Process w *)
        /\ msg = [self \in Nodes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> <<"Rec","Send">>]

Rec(self) == /\ pc[self] = "Rec"
             /\ \E _c139 \in chan:
                  /\ chan' = chan \ {_c139}
                  /\ msg' = [msg EXCEPT ![self] = _c139]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]

Send(self) == /\ pc[self] = "Send"
              /\ chan' = (chan \cup {"msg"})
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]
              /\ msg' = msg

w(self) ==  \/ Rec(self) \/ Send(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b7f97d1a959ed6bf17b455358c43c0c0

==========================================================

------------------------ MODULE ReaderWriterP3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel chan[Nodes];

process w \in Nodes
variable msg;
begin
	Rec:
      	receive(chan[self], msg);
end process;
begin
     Send:
          broadcast(chan, "msg");
end subprocess;
begin 
     Cl:
          clear(chan);
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bed943d666d7983c0536018372bed1da
CONSTANT defaultInitValue
VARIABLES chan, pc, msg

vars == << chan, pc, msg >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ msg = [self \in Nodes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> <<"Rec","Send","Cl">>]

Rec(self) == /\ pc[self][1]  = "Rec"
             /\ \E _c139 \in chan[self]:
                  /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c139}]
                  /\ msg' = [msg EXCEPT ![self] = _c139]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]

Send(self) == /\ pc[self][2]  = "Send"
              /\ chan' = [_n0 \in Nodes |-> chan[_n0] \cup {"msg"}]
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]
              /\ msg' = msg

Cl(self) == /\ pc[self][3]  = "Cl"
            /\ chan' = [_n0 \in Nodes |-> {}]
            /\ pc' = [pc EXCEPT ![self][3] = "Done"]
            /\ msg' = msg

w(self) == Rec(self) \/ Send(self) \/ Cl(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4f5ed2cf9e9d36931e51e30129c947fe

==========================================================

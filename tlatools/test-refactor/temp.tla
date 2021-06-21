------------------------ MODULE temp  -------------------------
EXTENDS Naturals, TLC

NODES == 1..3
T == 1..5

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

channel network[Nodes, Nodes];

process ( pid2 \in Nodes )
variable c = [q \in T |-> 0];
channel chan[T];
{
        Label:
                send(chan[self], "msg");
                c[self] := c[self] + 1;
        RC:
                send(network[self, self], "asd");

}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e13146cc0a52be9b743259277d4af023
VARIABLES network, pc, c, chan

vars == << network, pc, c, chan >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ network = [_mn430 \in Nodes, _mn441 \in Nodes |-> {}]
        (* Process pid2 *)
        /\ c = [self \in Nodes |-> [q \in T |-> 0]]
        /\ chan = [_nmd438 \in Nodes |-> [_nmd498 \in T |-> {}]]
        /\ pc = [self \in ProcSet |-> <<"Label">>]

Label(self) == /\ pc[self][1]  = "Label"
               /\ chan' = [chan EXCEPT ![self][self] = chan[self][self] \cup {"msg"}]
               /\ c' = [c EXCEPT ![self][self] = c[self][self] + 1]
               /\ pc' = [pc EXCEPT ![self][1] = "RC"]
               /\ UNCHANGED network

RC(self) == /\ pc[self][1]  = "RC"
            /\ network' = [network EXCEPT ![self, self] = network[self, self] \cup {"asd"}]
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]
            /\ UNCHANGED << c, chan >>

pid2(self) == Label(self) \/ RC(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: pid2(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : \A subprocess \in SubProcSet[self] : WF_vars(pid2(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-72f1c08828cc94e74f643c135d3fe7d2




================================================================================

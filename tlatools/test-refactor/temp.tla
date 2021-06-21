------------------------ MODULE temp  -------------------------
EXTENDS Naturals, TLC

NODES == 1..3
T == 1..5

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

channel network[Nodes, Nodes];

process ( pid2 \in Nodes )
variable c = [q \in Nodes |-> 0];
channel chan;
{
        Label:
                send(chan, "msg");
                c[self] := c[self] + 1;
        RC:
                send(network[self, self], "asd");

}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-5161ae7263337492ebc7492a5241c608
VARIABLES network, pc, c, chan

vars == << network, pc, c, chan >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ network = [_mn430 \in Nodes, _mn441 \in Nodes |-> {}]
        (* Process pid2 *)
        /\ c = [self \in Nodes |-> [q \in Nodes |-> 0]]
        /\ chan = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"Label">>]

Label(self) == /\ pc[self][1]  = "Label"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-92430e56e508ec57783b2b6860061c81




================================================================================

------------------------ MODULE ReaderWriterP3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

variables x = 0;
fifo chan[Nodes, Nodes];

process w \in Nodes
variable y = 0;
begin
	Clear2:
      	    clear(chan[self]);
end process;
begin
        Clear:
                clear(chan);
end subprocess;
begin
        Clear3:
                clear(chan[self, self]);
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-5324b25fd2b827b4bdf261ec1af121b0
VARIABLES x, chan, pc, y

vars == << x, chan, pc, y >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ x = 0
        /\ chan = [_n0 \in Nodes, _n1 \in Nodes |-> <<>>]
        (* Process w *)
        /\ y = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Clear2","Clear","Clear3">>]

Clear2(self) == /\ pc[self] [1] = "Clear2"
                /\ chan' = [_n0, _n1 \in Nodes |->  IF _n0 = self THEN <<>>  ELSE chan[_n0, _n1]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << x, y >>

Clear(self) == /\ pc[self] [2] = "Clear"
               /\ chan' = [_n0, _n1 \in Nodes |-> <<>>]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << x, y >>

Clear3(self) == /\ pc[self] [3] = "Clear3"
                /\ chan' = [chan EXCEPT ![self, self] = <<>>]
                /\ pc' = [pc EXCEPT ![self][3] = "Done"]
                /\ UNCHANGED << x, y >>

w(self) ==  \/ Clear2(self) \/ Clear(self) \/ Clear3(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2b35ee1b47e079911215ed560d1de697

==========================================================

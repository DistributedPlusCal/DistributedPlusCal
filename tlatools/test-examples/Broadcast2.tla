------------------------ MODULE Broadcast2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

fifo fchan[Nodes];

process w \in Nodes
begin
	broad2:
                 broadcast(fchan[self], "msg");
end process;
begin
        broad:
                broadcast(fchan, "msg");
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-968ed195826e7c6946b4ab1444850582
VARIABLES fchan, pc

vars == << fchan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ fchan = [_n430 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"broad2","broad">>]

broad2(self) == /\ pc[self][1]  = "broad2"
                /\ fchan' = [fchan EXCEPT ![self] =  Append(@, "msg")]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

broad(self) == /\ pc[self][2]  = "broad"
               /\ fchan' = [_n0 \in Nodes |->  Append(fchan[_n0] , "msg")]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) == broad2(self) \/ broad(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f348ac23e33a030b5bfd33637ee875ea


==========================================================

------------------------ MODULE FreshVars -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variables _n = 1, n1 = 2;
fifo chan[Nodes];

process (x = N+1)
variables t = <<1,2,3	>>;
{
    Simple:
		   t[1] := 1;
    Sdr:
        send(chan[1], "msg");
} 

process (id \in Nodes)
variables s = [no \in Nodes |-> 1];
{
    Simple:
		   s[self] := 2;
    Sdr:
        send(chan[self], "msg");
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-77b97222624eea39b46bad834cdb9178
VARIABLES _n, n1, chan, pc, t, s

vars == << _n, n1, chan, pc, t, s >>

ProcSet == {N+1} \cup (Nodes)

SubProcSet == [_n42 \in ProcSet |-> IF _n42 = N+1 THEN 1..1
                                 ELSE (**Nodes**) 1..1]

Init == (* Global variables *)
        /\ _n = 1
        /\ n1 = 2
        /\ chan = [_n430 \in Nodes |-> <<>>]
        (* Process x *)
        /\ t = <<1,2,3   >>
        (* Process id *)
        /\ s = [self \in Nodes |-> [no \in Nodes |-> 1]]
        /\ pc = [self \in ProcSet |-> CASE self = N+1 -> <<"Simple">>
                                        [] self \in Nodes -> <<"Simple">>]

Simple == /\ pc[N+1][1]  = "Simple"
          /\ t' = [t EXCEPT ![1] = 1]
          /\ pc' = [pc EXCEPT ![N+1][1] = "Sdr"]
          /\ UNCHANGED << _n, n1, chan, s >>

Sdr == /\ pc[N+1][1]  = "Sdr"
       /\ chan' = [chan EXCEPT ![1] =  Append(@, "msg")]
       /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
       /\ UNCHANGED << _n, n1, t, s >>

x == Simple \/ Sdr

Simple(self) == /\ pc[self][1]  = "Simple"
                /\ s' = [s EXCEPT ![self][self] = 2]
                /\ pc' = [pc EXCEPT ![self][1] = "Sdr"]
                /\ UNCHANGED << _n, n1, chan, t >>

Sdr(self) == /\ pc[self][1]  = "Sdr"
             /\ chan' = [chan EXCEPT ![self] =  Append(@, "msg")]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << _n, n1, t, s >>

id(self) == Simple(self) \/ Sdr(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == x
           \/ (\E self \in Nodes: id(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2e899177c34a34c2d11fa378b7f862d9
=========================================================

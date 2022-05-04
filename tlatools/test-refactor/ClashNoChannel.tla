------------------------ MODULE ClashNoChannel -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
N == 2
\* ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

\* variables _n = 1, n1 = 2;
variables _n42 = 1, n1 = 2;

process (x = N+1)
variables t = <<1,2,3	>>;
{
    One:
		   t[1] := 1;
} 

process (id \in Nodes)
variables s = [no \in Nodes |-> 1];
{
    Two:
		   s[self] := 2;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9eb3a51eece6ff45e63bc6f8d960fd98
VARIABLES _n42, n1, pc, t, s

vars == << _n42, n1, pc, t, s >>

ProcSet == {N+1} \cup (Nodes)

SubProcSet == [_n42 \in ProcSet |-> IF _n42 = N+1 THEN 1..1
                                 ELSE (**Nodes**) 1..1]

Init == (* Global variables *)
        /\ _n42 = 1
        /\ n1 = 2
        (* Process x *)
        /\ t = <<1,2,3   >>
        (* Process id *)
        /\ s = [self \in Nodes |-> [no \in Nodes |-> 1]]
        /\ pc = [self \in ProcSet |-> CASE self = N+1 -> <<"One">>
                                        [] self \in Nodes -> <<"Two">>]

One == /\ pc[N+1][1]  = "One"
       /\ t' = [t EXCEPT ![1] = 1]
       /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
       /\ UNCHANGED << _n42, n1, s >>

x == One

Two(self) == /\ pc[self][1]  = "Two"
             /\ s' = [s EXCEPT ![self][self] = 2]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << _n42, n1, t >>

id(self) == Two(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == x
           \/ (\E self \in Nodes: id(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c3f984b862bf031bdd1356f10dd31071
=========================================================

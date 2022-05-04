------------------------ MODULE NoProcessBroadcast -------------------------
EXTENDS Naturals, Sequences, TLC

\* CONSTANT N      (* Size of arrays *)
N == 3
Nodes == 1..2

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..2 ],  (* Array of N integers in 0..MAXINT *)
    x = 1,               
    i = 1;
    channel chan, cc[Nodes], cd[Nodes,Nodes];
    fifo fif, ff[Nodes], fd[Nodes,Nodes];
{
    One:
				x := ar[1];
        broadcast(cd[1,
				2
				], [ag \in 1..Nodes |-> x]);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-8e86bdbd8bac18c921c285f006ef64e4
VARIABLES ar, x, i, chan, cc, cd, fif, ff, fd, pc

vars == << ar, x, i, chan, cc, cd, fif, ff, fd, pc >>

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..2 ]
        /\ x = 1
        /\ i = 1
        /\ chan = {}
        /\ cc = [_n10 \in Nodes |-> {}]
        /\ cd = [_n20 \in Nodes, _n31 \in Nodes |-> {}]
        /\ fif = <<>>
        /\ ff = [_n40 \in Nodes |-> <<>>]
        /\ fd = [_n50 \in Nodes, _n61 \in Nodes |-> <<>>]
        /\ pc = "One"

One == /\ pc = "One"
       /\ x' = ar[1]
       /\ cc' = [ag \in 1 .. Nodes |-> cc[ag] \cup  {x'} ]
       /\ pc' = "Done"
       /\ UNCHANGED << ar, i, chan, cd, fif, ff, fd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-de4310659e4d2796f775dbd49e4ba9a6
=============================================================================

------------------------ MODULE NoProcessChannels -------------------------
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
        send(chan, x);
        send(cc[1], x);
        send(cd[2,1], x);
        send(fif, x);
        send(ff[1], x);
        send(fd[2,1], x);
				
		Two: 
        receive(chan, i);
        receive(fif, x);
		Three:
        receive(cc[1], i);
        receive(ff[1], x);
		Four:
        receive(cd[2,1], i);
        receive(fd[2,1], x);
        i := i + 1;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e4b0496e3847af6ac7acd741b46f9f31
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
       /\ chan' = (chan \cup {x'})
       /\ cc' = [cc EXCEPT ![1] = @ \cup {x'}]
       /\ cd' = [cd EXCEPT ![2,1] = @ \cup {x'}]
       /\ fif' =  Append(fif, x')
       /\ ff' = [ff EXCEPT ![1] =  Append(@, x')]
       /\ fd' = [fd EXCEPT ![2,1] =  Append(@, x')]
       /\ pc' = "Two"
       /\ UNCHANGED << ar, i >>

Two == /\ pc = "Two"
       /\ \E _c1513 \in chan:
            /\ chan' = chan \ {_c1513}
            /\ i' = _c1513
       /\ Len(fif) > 0 
       /\ x' = Head(fif)
       /\ fif' =  Tail(fif) 
       /\ pc' = "Three"
       /\ UNCHANGED << ar, cc, cd, ff, fd >>

Three == /\ pc = "Three"
         /\ \E _c1519 \in cc[1]:
              /\ cc' = [cc EXCEPT ![1] = @ \ {_c1519}]
              /\ i' = _c1519
         /\ Len(ff[1]) > 0 
         /\ x' = Head(ff[1])
         /\ ff' = [ff EXCEPT ![1] =  Tail(@) ]
         /\ pc' = "Four"
         /\ UNCHANGED << ar, chan, cd, fif, fd >>

Four == /\ pc = "Four"
        /\ \E _c1530 \in cd[2,1]:
             /\ cd' = [cd EXCEPT ![2,1] = @ \ {_c1530}]
             /\ i' = _c1530
        /\ Len(fd[2,1]) > 0 
        /\ x' = Head(fd[2,1])
        /\ fd' = [fd EXCEPT ![2,1] =  Tail(@) ]
        /\ pc' = "Lbl_1"
        /\ UNCHANGED << ar, chan, cc, fif, ff >>

Lbl_1 == /\ pc = "Lbl_1"
         /\ i' = i + 1
         /\ pc' = "Done"
         /\ UNCHANGED << ar, x, chan, cc, cd, fif, ff, fd >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One \/ Two \/ Three \/ Four \/ Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-bdc62c9dd644a0129b01983758e655eb
=============================================================================


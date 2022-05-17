------------------------ MODULE NoProcessOneLabelMC -------------------------
EXTENDS Naturals, TLC, Sequences

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT MAXINT      
MAXINT == 3

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

variables 
    \* ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    ar = [ 1..N -> 2 ],  (* Array of N integers *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1,
		r = 9;

channel chan[N], ch;

macro inc(i,inc) {
    ar[i] := inc;
    i := i+1;
}

macro sendC(j,n) {
    \* send(chan[j],n);
    \* send(ch,n);
		\* broadcast(chan,[ag \in 1..N |-> n]);
    \* multicast(chan,[ag \in 1..N |-> n]);
		\* receive(chan[j], r);
		receive(ch, r);
		clear(chan);
}


{
    One:
				found := TRUE;
        \* broadcast(chan,[ag \in 1..N |-> 0]);
        \* multicast(chan,[ag \in 1..N |-> 0]);
				\* receive(ch, r);
		    \* clear(chan);
				\* clear(ch);  \* BUG
				x := ar[1];
				i := i + 1;
				ar[i] := 0;
				\* inc(x,1);
				\* inc(i,1);
				sendC(1,2);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3b3705f72a56e0a2ced0d8f5a8d660b1
VARIABLES ar, x, found, i, r, chan, ch, pc

vars == << ar, x, found, i, r, chan, ch, pc >>

Init == (* Global variables *)
        /\ ar = [ 1..N -> 2 ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ r = 9
        /\ chan = [_n10 \in N |-> {}]
        /\ ch = {}
        /\ pc = "One"

One == /\ pc = "One"
       /\ found' = TRUE
       /\ x' = ar[1]
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ \E _c2118 \in ch:
            /\ ch' = ch \ {_c2118}
            /\ r' = _c2118
       /\ chan' = [_n0 \in N |-> {}]
       /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2f55fe2e0a9098a5b97d11367cc9ea33
=============================================================================


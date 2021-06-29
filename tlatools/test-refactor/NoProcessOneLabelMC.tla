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
    i = 1;

channel chan[N], ch;

macro inc(i,inc) {
    ar[i] := inc;
    i := i+1;
}

macro sendC(j,n) {
    send(chan[j],n);
    send(ch,n);
		broadcast(chan,[ag \in 1..N |-> n]);
    multicast(chan,[ag \in 1..N |-> n]);
}


{
    One:
				found := TRUE;
        broadcast(chan,[ag \in 1..N |-> 0]);
        multicast(chan,[ag \in 1..N |-> 0]);
		    x := ar[1];
				i := i + 1;
				ar[i] := 0;
				\* inc(x,1);
				\* inc(i,1);
				sendC(1,3);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ee608da0c8ddd91a9b065f6c0c165a31
VARIABLES ar, x, found, i, chan, ch, pc

vars == << ar, x, found, i, chan, ch, pc >>

Init == (* Global variables *)
        /\ ar = [ 1..N -> 2 ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ chan = [_n10 \in N |-> {}]
        /\ ch = {}
        /\ pc = "One"

One == /\ pc = "One"
       /\ found' = TRUE
       /\ chan' = [ag \in 1 .. N |-> chan[ag] \cup  {0} ]
       /\ pc' = "Lbl_1"
       /\ UNCHANGED << ar, x, i, ch >>

Lbl_1 == /\ pc = "Lbl_1"
         /\ chan' = [ag \in DOMAIN chan |->  IF ag \in 1 .. N THEN chan[ag] \cup  {0}  ELSE chan[ag]]
         /\ x' = ar[1]
         /\ i' = i + 1
         /\ ar' = [ar EXCEPT ![i'] = 0]
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << found, ch >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ chan' = [chan EXCEPT ![1] = chan[1] \cup {3}]
         /\ ch' = (ch \cup {3})
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << ar, x, found, i >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ chan' = [ag \in 1 .. N |-> chan[ag] \cup  {3} ]
         /\ pc' = "Lbl_4"
         /\ UNCHANGED << ar, x, found, i, ch >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ chan' = [ag \in DOMAIN chan |->  IF ag \in 1 .. N THEN chan[ag] \cup  {3}  ELSE chan[ag]]
         /\ pc' = "Done"
         /\ UNCHANGED << ar, x, found, i, ch >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One \/ Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0af2f5b09fd3cd2e62790264265881ad
=============================================================================

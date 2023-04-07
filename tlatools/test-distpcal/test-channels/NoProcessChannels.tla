------------------------ MODULE NoProcessChannels -------------------------
EXTENDS Naturals, Sequences, TLC

N == 3
Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy {
variables 
    ar = [ind \in 1..N |-> 0 ],  
    v \in [(Nodes \cup {Id}) \X Nodes  -> {}],
    x = 1,               
    i = 1;
    channel chan, chan1[Nodes \cup {Id}], chan2[Nodes][Nodes];
    fifo fif, fif1[Nodes], fif2[Nodes][Nodes];
{
        S:
		x := ar[1];
        SC:
        send(chan, x);
        send(chan, ar[2]);
        send(chan1[1], x);
        send(chan2[2,1], x);
        SF:
        send(fif, x);
        send(fif1[1], x);
        send(fif2[2,1], x);
				
		Rc: 
        receive(chan, i);
        \* receive(chan, ar[1]); (* BUG *)
		Rf: 
        receive(fif, x);
		R1c:
        receive(chan1[1], i);
		R1f:
        receive(fif1[1], x);
		R2c:
        receive(chan2[2,1], i);
		R2f:
        receive(fif2[2,1], x);
        F:
        i := i + 1;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e85a100c" /\ chksum(tla) = "e3cafa6f")
VARIABLES ar, v, x, i, chan, chan1, chan2, fif, fif1, fif2, pc

vars == << ar, v, x, i, chan, chan1, chan2, fif, fif1, fif2, pc >>

Init == (* Global variables *)
        /\ ar = [ind \in 1..N |-> 0 ]
        /\ v \in [(Nodes \cup {Id}) \X Nodes  -> {}]
        /\ x = 1
        /\ i = 1
        /\ chan = {}
        /\ chan1 = [_n10 \in  Nodes \cup { Id } |-> {}]
        /\ chan2 = [_n20 \in  Nodes, _n31 \in  Nodes |-> {}]
        /\ fif = <<>>
        /\ fif1 = [_n40 \in  Nodes |-> <<>>]
        /\ fif2 = [_n50 \in  Nodes, _n61 \in  Nodes |-> <<>>]
        /\ pc = "S"

S == /\ pc = "S"
     /\ x' = ar[1]
     /\ pc' = "SC"
     /\ UNCHANGED << ar, v, i, chan, chan1, chan2, fif, fif1, fif2 >>

SC == /\ pc = "SC"
      /\ chan' = (chan \cup {x})
      /\ pc' = "Lbl_1"
      /\ UNCHANGED << ar, v, x, i, chan1, chan2, fif, fif1, fif2 >>

Lbl_1 == /\ pc = "Lbl_1"
         /\ chan' = (chan \cup {ar[2]})
         /\ chan1' = [chan1 EXCEPT ![1] = @ \cup {x}]
         /\ chan2' = [chan2 EXCEPT ![2,1] = @ \cup {x}]
         /\ pc' = "SF"
         /\ UNCHANGED << ar, v, x, i, fif, fif1, fif2 >>

SF == /\ pc = "SF"
      /\ fif' =  Append(fif, x)
      /\ fif1' = [fif1 EXCEPT ![1] =  Append(@, x)]
      /\ fif2' = [fif2 EXCEPT ![2,1] =  Append(@, x)]
      /\ pc' = "Rc"
      /\ UNCHANGED << ar, v, x, i, chan, chan1, chan2 >>

Rc == /\ pc = "Rc"
      /\ \E _c1613 \in chan:
           /\ chan' = chan \ {_c1613}
           /\ i' = _c1613
      /\ pc' = "Rf"
      /\ UNCHANGED << ar, v, x, chan1, chan2, fif, fif1, fif2 >>

Rf == /\ pc = "Rf"
      /\ Len(fif) > 0 
      /\ x' = Head(fif)
      /\ fif' =  Tail(fif) 
      /\ pc' = "R1c"
      /\ UNCHANGED << ar, v, i, chan, chan1, chan2, fif1, fif2 >>

R1c == /\ pc = "R1c"
       /\ \E _c1619 \in chan1[1]:
            /\ chan1' = [chan1 EXCEPT ![1] = @ \ {_c1619}]
            /\ i' = _c1619
       /\ pc' = "R1f"
       /\ UNCHANGED << ar, v, x, chan, chan2, fif, fif1, fif2 >>

R1f == /\ pc = "R1f"
       /\ Len(fif1[1]) > 0 
       /\ x' = Head(fif1[1])
       /\ fif1' = [fif1 EXCEPT ![1] =  Tail(@) ]
       /\ pc' = "R2c"
       /\ UNCHANGED << ar, v, i, chan, chan1, chan2, fif, fif2 >>

R2c == /\ pc = "R2c"
       /\ \E _c1643 \in chan2[2,1]:
            /\ chan2' = [chan2 EXCEPT ![2,1] = @ \ {_c1643}]
            /\ i' = _c1643
       /\ pc' = "R2f"
       /\ UNCHANGED << ar, v, x, chan, chan1, fif, fif1, fif2 >>

R2f == /\ pc = "R2f"
       /\ Len(fif2[2,1]) > 0 
       /\ x' = Head(fif2[2,1])
       /\ fif2' = [fif2 EXCEPT ![2,1] =  Tail(@) ]
       /\ pc' = "F"
       /\ UNCHANGED << ar, v, i, chan, chan1, chan2, fif, fif1 >>

F == /\ pc = "F"
     /\ i' = i + 1
     /\ pc' = "Done"
     /\ UNCHANGED << ar, v, x, chan, chan1, chan2, fif, fif1, fif2 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == S \/ SC \/ Lbl_1 \/ SF \/ Rc \/ Rf \/ R1c \/ R1f \/ R2c \/ R2f \/ F
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}


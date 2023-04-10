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
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}


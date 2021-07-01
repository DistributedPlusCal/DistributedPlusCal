------------------------ MODULE OneProcessMultiThreadMC -------------------------
EXTENDS Naturals, TLC, Sequences

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT MAXINT      
MAXINT == 3

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

variables 
    ar = [ 1..N -> 2 ],  (* Array of N integers *)
    x,
		r;
		
channel chan[N], ch;

macro sendC(cc,j,n) {
    send(cc[j],n);
}

macro receiveC(cr,k,m) {
    receive(cr[k],x);
}

process ( pid2 = 1 )
variable c = 1;
{
    x := ar[1];
		sendC(chan,1,2);
}{
		receiveC(chan,3,2);
}

}
*)
=============================================================================


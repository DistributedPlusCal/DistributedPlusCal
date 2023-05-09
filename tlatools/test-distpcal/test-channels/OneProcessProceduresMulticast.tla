------------------------ MODULE OneProcessProceduresMulticast -------------------------
EXTENDS TLC, Integers, Sequences, Bags

N == 2
Nodes == 1..N

(* PlusCal options (-label -distpcal -setchannels) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch1[Nodes],ch2[Nodes \cup {N+1}][Nodes];

procedure multicastToChannel1(mes)
{
	S1:
    multicast(ch1,[ag \in DOMAIN ch1 |-> mes]);
	return;
}

procedure multicastToChannel2(from, mes)
{
	S2:
    multicast(ch2,[n = from, m \in Nodes |-> mes]);
	return;
}


process ( snd = N+1 )
variable cur = 1, loc = 0;
{
    Send1:
    call multicastToChannel1(c);
    Send2:
    call multicastToChannel2(N+1,N+1);
    After:
    cur := cur + 1;
}

process ( rcv \in Nodes )
variable cur = 1, loc = 0;
{
    R1:
    receive(ch1[self],cur);
}
{
    R2:
    receive(ch2[N+1,self],cur);
}
}
*)
================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    }
}

------------------------ MODULE MulticastMacros -------------------------
EXTENDS TLC, Integers, Sequences, Bags

N == 2
Nodes == 1..N

(* PlusCal options (-label -distpcal ) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch1[Nodes],ch2[Nodes \cup {N+1}][Nodes];

macro multicastMacro1(chanName, mes) {
	multicast(chanName, [ag \in DOMAIN chanName |-> mes]);
}

macro multicastMacro2(chanName, from, mes) {
    multicast(chanName,[n = from, m \in Nodes |-> mes]);
}

macro multicastMacro3(chanName, from, to) {
    multicast(chanName,[n = from, m \in to |-> from]);
}

process ( snd = N+1 )
variable cur = 1, loc = 0;
{
    Send1:
        multicastMacro1(ch1,c);
    Send2:
        multicastMacro2(ch2,N+1,N+1);
    Send3:
        multicastMacro3(ch2,N+1,Nodes);
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
    "model-checking-args": {}
}

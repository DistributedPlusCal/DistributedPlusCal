------------------------ MODULE OneProcessBroadcastFIFO -------------------------
EXTENDS TLC, Integers, Sequences

N == 3
Nodes == 1..N-1
NNodes == N..5

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2, r = 22, TO = {<<1,1>>, <<2,2>>};
fifos ch1[Nodes],ch2[Nodes][Nodes];

macro broadcast(chan,m)
{
    multicast(chan,[ag \in DOMAIN chan |-> m]);
}

process ( sid = 3 )
variable cur = 10, loc = 0;
{
    Send1:
    multicast(ch1,[ag \in DOMAIN ch1 |-> ag]);
    SendM1:
    broadcast(ch1,cur);
    Send2: 
    multicast(ch2,[ag \in DOMAIN ch2 |-> loc]);
    SendM2:
    broadcast(ch2,cur);
}

process ( w \in Nodes )
variable loc = 0;
{
    R1:
    receive(ch1[self],loc);
}
{
    \* force deadlock to look at the trace
    await loc > 4;
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

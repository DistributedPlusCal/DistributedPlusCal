------------------------ MODULE OneProcessMulticastChannel -------------------------
EXTENDS TLC, Integers, Sequences

N == 3
Nodes == 1..N-1
NNodes == N..5

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2, r = 22, TO = {<<1,1>>, <<2,2>>};
channels ch1[Nodes],ch2[Nodes][Nodes];

process ( sid = 3 )
variable cur = 1, loc = 0;
{
    SendM1:
    multicast(ch1,[ag \in DOMAIN ch1 |-> ag]);
    SendM2:
    multicast(ch2,[n = 1, m \in Nodes |-> n]);
    multicast(ch2,[n \in 
    Nodes, m \in Nodes |-> n 
     + 1]);
    multicast(ch2,[ag \in Nodes \X Nodes |-> 10]);
    multicast(ch2,[ag \in TO |-> 0]);
    After:
    cur := cur + 1;
}

process ( w \in Nodes )
variable loc = 0;
{
    R:
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

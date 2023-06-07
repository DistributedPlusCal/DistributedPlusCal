------------------------ MODULE SendReceive -------------------------
EXTENDS TLC, Integers, Sequences, Bags

N == 2
Nodes == 1..N

(* PlusCal options (-label -distpcal ) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch, ch1[Nodes],ch2[Nodes][Nodes];

process ( sid \in Nodes )
variable cur = 10, loc = 0;
{
    Send1:
    send(ch,cur);
    send(ch1[1],cur);
    send(ch2[2,2],cur);
}
{
    R1:
    receive(ch,loc);
    R1a:
    receive(ch1[1],loc);
    R1b:
    receive(ch2[2,2],loc);
}

process ( qid = N+1 )
variable cc = 10;
{
    cc := cc + 2;
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

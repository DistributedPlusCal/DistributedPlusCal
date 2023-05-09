------------------------ MODULE OneProcessSendReceive -------------------------
EXTENDS TLC, Integers, Sequences, Bags

Nodes == 1..2

(* PlusCal options (-label -distpcal ) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch, ch1[Nodes],ch2[Nodes][Nodes];

process ( sid = 3 )
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
}
*)
================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}

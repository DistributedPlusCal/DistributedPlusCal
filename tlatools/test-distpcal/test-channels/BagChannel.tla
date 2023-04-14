------------------------ MODULE BagChannel -------------------------
EXTENDS TLC, Integers, Sequences, Bags

Nodes == 1..2

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch
, ch1[Nodes]
, ch2[Nodes][Nodes]
;

process ( sid = 3 )
variable cur = 10, loc = 0;
{
    Send:
    send(ch,cur);
    send(ch,cur);
    send(ch1[1],cur);
    send(ch1[1],cur);
    send(ch2[2,2],cur);
    send(ch2[2,2],cur);
}
{
    R:
    receive(ch,loc);
    Rb:
    receive(ch,loc);
    R1:
    receive(ch1[1],loc);
    R1b:
    receive(ch1[1],loc);
    R2:
    receive(ch2[2,2],loc);
    R2b:
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

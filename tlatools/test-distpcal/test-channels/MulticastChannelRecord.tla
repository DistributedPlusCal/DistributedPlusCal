------------------------ MODULE MulticastChannelRecord -------------------------
EXTENDS TLC, Integers, Sequences, Bags

N == 3
Nodes == 1..N-1

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2;
fifo ch[Nodes];

process ( sid \in Nodes )
variable loc = 0;
{
    SendM:
    multicast(ch,[ag \in Nodes \ {self} |->     
                        [type |-> "1a", 
                        leader |-> self,
                        bal |-> loc] ]);
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

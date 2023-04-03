------------------------ MODULE TwoProcessesGlobalChannelBUG -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ (Nodes \cup {Id}) -> 0..2 ],  
          cur = "none";

channels ch[Nodes \cup {Id}], ch2[Nodes][Nodes];

process ( qid = Id )
variable d = 4;
{
    QL:
	receive(ch[Id], ar[1]); (* BUG: array destination)
}

}
*)
==========================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}


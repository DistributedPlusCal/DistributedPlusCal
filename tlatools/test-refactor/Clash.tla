------------------------ MODULE Clash -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. 3

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {
variable cur = "none";
         \* _c159 = 159;
         \* _n430 = 42;

\* fifo chan[Nodes];
channel chan[Nodes];

process ( w \in Nodes )
{
	Write:
    send(chan[self], "msg");
} {
	Read:
      receive(chan[self], cur);
} {
  Clear:
		clear(chan);
} {
  Clearness:
		clear(chan);
}
}
*)
==========================================================


------------------------ MODULE ReaderWriterC10 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {


fifo chan[Nodes];

macro send_to(i, msg) {
    print(msg);
    print(chan[i]);
		send(chan[i], "msg");
}


process ( w \in Nodes )
{
    Read:
      skip;
} {
   send_to(self, "abc");
}


}
*)


================================================

------------------------ MODULE SequentialAlgoP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm transfer

\* variable c = <<>>, x;
fifo c;

begin
	A: 
    send(c, 2);
    \* x := Append(c, 1);

end algorithm;
*)

==========================================================

------------------------ MODULE SequentialAlgoC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

variable c = {};
channel chan;

process ( rm = 1 ) {
    Star1:
    c := c \union {1};
    send(chan, 2);
}


}
*)

==========================================================

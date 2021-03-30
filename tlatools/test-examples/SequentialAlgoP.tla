------------------------ MODULE SequentialAlgoP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm transfer

variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
	A: alice_account := alice_account - money;
	B: bob_account := bob_account + money;
	C: assert alice_account >= 0;

end algorithm;
*)

==========================================================

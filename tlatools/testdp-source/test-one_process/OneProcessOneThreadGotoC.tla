----- MODULE OneProcessOneThreadGotoC----
EXTENDS Naturals, TLC

(* PlusCal options (-termination ) *)

(*--algorithm X {
variables 
    found = FALSE
process (x \in 1..2)
{
    a: goto a;
}
}
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "compare_to": ""
}

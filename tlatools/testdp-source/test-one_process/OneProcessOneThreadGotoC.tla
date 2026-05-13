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
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "compare_to": ""
}

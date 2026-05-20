----- MODULE OneProcessOneThreadGotoP----
EXTENDS Naturals, TLC

(* PlusCal options (-termination ) *)

(*--algorithm X 
variables 
    found = FALSE

process x \in 1..2
begin 
    a: goto a;
end thread

end algorithm
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessOneThreadGotoC.tla"
}

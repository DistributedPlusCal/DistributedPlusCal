----- MODULE OneProcessOneThreadGotoP----

(*--algorithm X 
variables 
    found = FALSE

process x \in {}
begin 
    a: goto a;
end thread

end algorithm
*)
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessOneThreadGotoC.tla"
}

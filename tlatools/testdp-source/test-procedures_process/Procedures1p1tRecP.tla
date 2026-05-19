------------------------ MODULE Procedures1p1tRecP -------------------------
EXTENDS TLC, Integers, Sequences

N == 5

(* PlusCal options (-label) *)
 
(*--algorithm Dummy 
variable c = 0,
         acc = [i \in 0 .. N |-> 0];

procedure fact(n,res)
begin
    Start:
        acc[n] := res;
        if  n = 0  then
            c := res;
            return;
        else 
            res := res * ( n-1 );
            call fact(n-1, res);
        end if;
    End:
        return;
end procedure

process id = 2
variable lp = 3;
begin
    Before:
        lp := lp + 1;
    Sdr:
        call fact(lp,1);
    After:
        skip;
end thread

end algorithm
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
    "compare_path": "compile",
	"compare_to": "test-procedures_process/Procedures1p1tRecC.tla"
}

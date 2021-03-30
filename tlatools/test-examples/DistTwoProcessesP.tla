------------------------ MODULE DistTwoProcessesP -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS MaxQueueSize

(* PlusCal options (-distpcal) *)

(*
--algorithm f_queue_algo

variable queue = <<>>;
fifo f_queue;

define
  BoundedQueue == Len(queue) <= MaxQueueSize 
end define;

process ( w = "writer" )
begin
	Write:
  	while ( TRUE ) do
    	queue := Append(queue, "msg");
      send(f_queue, "msg");
  	end while;
end process;

process ( r = "reader" )
variables current_message = "none";
begin
	Read:
  	while ( TRUE ) do
    	receive(f_queue, current_message);
  	end while;
end process;

end algorithm;
*)

==========================================================

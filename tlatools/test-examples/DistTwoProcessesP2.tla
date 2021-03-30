------------------------ MODULE DistTwoProcessesP2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS MaxQueueSize

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

variable queue = <<>>;
channel chan;

define
  BoundedQueue == Len(queue) <= MaxQueueSize 
end define;

process ( w = "writer" )
begin
	Write:
  	while ( TRUE ) do
    	queue := Append(queue, "msg");
      send(chan, "msg");
  	end while;
end process;

process ( r = "reader" )
variables current_message = "none";
begin
	Read:
  	while ( TRUE ) do
    	receive(chan, current_message);
  	end while;
end process;

end algorithm;
*)

==========================================================

All tests in this folder are uni-process specifications

* Channel declaration
** C_Channels1
- declaration of uni-dimensional unordered channels
- declaration of uni-dimensional fifo channels
- 

** C_Channels2
- declaration of one-dimensional unordered channels with constant parameter
- declaration of one-dimensional fifo channels with constant parameter
- 

** C_Channels3
- declaration of one-dimensional unordered channels without constant parameter
- declaration of one-dimensional fifo channels without constant parameter
- 

** C_Channels4
- declaration of two-dimensional unordered channels without constant parameter
- declaration of two-dimensional fifo channels without constant parameter
- 

** C_Channels5
- declaration of two-dimensional unordered channels with constant parameter
- declaration of two-dimensional fifo channels with constant parameter
- 



* SEND operation

** C_Send1
- uni-dimensional unoredered channel
- send operation
- parsed correctly

** C_Send2
- uni-dimensional fifo channel
- send operation
- 

** C_Send3
- one-dimensional unordered channel
- send operation
- 

** C_Send4
- one-dimensional fifo channel
- send operation
-

** C_Send5
- two-dimensional unordered channel
- send operation
- 

** C_Send6
- two-dimensional fifo channel
- send operation
- 


* RECEIVE operation

** C_Receive1
- uni-dimensional unodered channel
- receive operation
- 

** C_Receive2
- uni-dimensional fifo channel
- receive operation
- 

** C_Receive3
- one-dimensional unodered channel
- receive operation
-

** C_Receive4
- one-dimensional fifo channel
- receive operation
- 

** C_Receive5
- two-dimensional unodered channel
- receive operation
- 

** C_Receive6
- two-dimensional fifo channel
- receive operation
- 


* CLEAR operation
** C_Clear1
- uni-dimensional unodered channel
- clear operation
- 

** C_Clear2
- uni-dimensional fifo channel
- clear operation
- 

** C_Clear3
- one-dimensional unodered channel
- clear operation
-

** C_Clear4
- one-dimensional fifo channel
- clear operation
- 

** C_Clear5
- two-dimensional unodered channel
- clear operation
- 

** C_Clear6
- two-dimensional fifo channel
- clear operation
- 


* BROADCAST operation

** C_Broadcast1
- uni-dimensional unodered channel
- broadcast operation
- 

** C_Broadcast2
- uni-dimensional fifo channel
- broadcast operation
- 

** C_Broadcast3
- one-dimensional unodered channel
- broadcast operation
-

** C_Broadcast4
- one-dimensional fifo channel
- broadcast operation
- 

** C_Broadcast5
- two-dimensional unodered channel
- broadcast operation
- 

** C_Broadcast6
- two-dimensional fifo channel
- broadcast operation
- 


========================================================================================

* Channel operations inside Macro

** C_MacroSend1
- send operation inside macro
- uni-dimensional unordered channel
- macro with one parameter - msg
- 

** C_MacroSend2
- send operation inside macro
- uni-dimensional unordered channel
- macro without parameters
- 

** C_MacroSend3
- send operation inside macro
- one-dimensional unordered channel
- macro with two parameters - a channel identifier and a message
- 

** C_MacroSend4
- send operation inside macro
- one-dimensional unordered channel
- macro with two parameters - a channel identifier and a message (reverse order)
- 

** C_MacroSend5 (to test that channel operation gets only parameters it needs)
- macro with send operation and global variable incrementing statement
- one-dimensional unordered channel
- macro with three parameters - a channel identifier, a message and a value for other variable
- 


** C_MacroReceive1
- uni-dimensional unordered channel
- receive call inside macro
- macro with two parameters
- 

** C_MacroReceive2
- uni-dimensional unordered channel
- receive call inside macro
- macro without parameters
- 

** C_MacroReceive3
- one-dimensional unordered channel
- receive call inside macro
- macro with two parameters
- 

** C_MacroReceive4
- one-dimensional unordered channel
- receive call inside macro
- macro with three parameters - one parameter for global variable incrementing
- 

** C_MacroReceive5
- two-dimensional unordered channel
- receive call inside macro
- macro with three parameters
- 

** C_MacroReceive6
- two-dimensional unordered channel
- receive call inside macro
- macro with four parameters - one parameter for global variable incrementing
- 


** C_MacroClear1
- uni-dimensional unordered channel
- clear call inside macro
- macro without parameters
- 

** C_MacroClear2
- uni-dimensional unordered channel
- clear call inside macro
- macro with parameter - global variable(channel) is passed
- 

** C_MacroClear2
- uni-dimensional unordered channel
- clear call inside macro
- macro with parameter - global variable(channel) is passed
- 

** C_MacroClear3
- one-dimensional unordered channel
- clear call inside macro
- macro with a parameter- subchannel identifier passed 
- 

** C_MacroClear4
- two-dimensional unordered channel
- clear call inside macro
- macro with a parameter - subchannel identifier passed
- 



** C_MacroBroadcast1
- uni-dimensional unordered channel
- broadcast call inside macro
- macro without parameters
- 

** C_MacroBroadcast2
- one-dimensional unordered channel
- broadcast call inside macro
- macro with a parameter - a message
- 

** C_MacroBroadcast3
- one-dimensional unordered channel
- broadcast call inside macro
- macro with two parameters - a channel and a message
- 

** C_MacroBroadcast4
- two-dimensional unordered channel
- broadcast call inside macro
- macro with a parameter - a message
- 

** C_MacroBroadcast5
- two-dimensional unordered channel
- broadcast call inside macro
- macro with two parameters - a subchannel identifier and a message
- 

** C_MacroMulticast1
- one-dimensional unordered channel
- multicast call inside macro
- macro with a parameter - an expression
- 

** C_MacroMulticast2
- one-dimensional unordered channel
- multicast call inside macro
- macro with two parameters - an expression and value for incrementing global counter
- 

** C_MacroMulticast3
- two-dimensional unordered channel
- multicast call inside macro
- macro with a parameter - an expression
- 


========================================================================================
Procedure tests

** C_ProcedureSend1
- uni-dimensional unordered channel
- send call inside macro
- procedure with a parameter - a message
- 

** C_ProcedureSend2
- uni-dimensional unordered channel
- send call inside macro
- procedure with a parameter - a message(global variable)
- 

** C_ProcedureSend3
- one-dimensional unordered channel
- send call inside macro
- procedure with two parameters - a message and a channel identifier
- 

** C_ProcedureSend4
- one-dimensional unordered channel
- send call inside macro
- procedure with three parameters - a message, a channel identifier and a value to increment global counter
- 

** C_ProcedureSend5
- two-dimensional unordered channel
- send call inside macro
- procedure with three parameters - a message, a channel identifiers
- 

** C_ProcedureReceive1
- uni-dimensional unordered channel
- receive call inside macro
- procedure without parameters
- 

** C_ProcedureReceive2
- one-dimensional unordered channel
- receive call inside macro
- procedure with two parameters - a channel identifier and reference to global variable
- 

** C_ProcedureReceive3
- one-dimensional unordered channel
- receive call inside macro
- procedure with two parameters - channel identifiers
- 


** C_ProcedureClear1
- uni-dimensional unordered channel
- clear call inside macro
- procedure without parameters
- 

** C_ProcedureClear2
- one-dimensional unordered channel
- clear call inside macro
- procedure with a parameter - channel identifier
- 


** C_ProcedureBroadcast1
- uni-dimensional unordered channel
- clear call inside macro
- procedure with a parameter - a message
- 

** C_ProcedureBroadcast2
- one-dimensional unordered channel
- clear call inside macro
- procedure with a parameter - a message
- 

** C_ProcedureBroadcast3
- two-dimensional unordered channel
- clear call inside macro
- procedure with a parameter - a message and a channel identifier
- 


** C_ProcedureMulticast1
- two-dimensional unordered channel
- clear call inside macro
- procedure with a parameter - a message and a channel identifier
- 


	
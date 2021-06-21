
Broadcast1.tla
* Test new broadcast channel operation with two-dimensional fifo channel
* Parsed correctly
* no model checking errors.

Broadcast2.tla
* Test new broadcast channel operation with one-dimensional fifo channel
* Parsed correctly
* no model checking errors.

Broadcast3.tla
* Test new broadcast channel operation with two-dimensional unordered channel
* Parsed correctly
* no model checking errors.

Broadcast4.tla
* Test new broadcast channel operation with one-dimensional unordered channel
* Parsed correctly
* no model checking errors.

Clear1.tla
* Test new clear channel operation with two-dimensional fifo channel
* Parsed correctly
* no model checking errors.

Clear2.tla
* Test new clear channel operation with two-dimensional unordered channel
* Parsed correctly
* no model checking errors.


ChannelsAndFifo1.tla
* Test consecutive channel, fifo and lamportClock declarations.
* Parsed correctly
* no model checking errors.

ChannelsAndFifo2.tla
* Test consecutive channel declarations.
* Parsed correctly
* no model checking errors.

ChannelsAndFifo3.tla
* Consecutive fifo channels declarations local to a process.
* Wrong initialization of channels.
* Parsed correctly
* no model checking errors.

ChannelsAndFifo4.tla
* Unordered channels declarations local to a process.
* Wrong initialization of channels.
* Parsed correctly
* no model checking errors.

Procedures1.tla
* Test procedures translation. PlusCal specification
* Parsed correctly
* no model checking errors.

Procedures2.tla
* Test procedures translation uni-process algorithm. PlusCal specification
* Parsed correctly
* no model checking errors.


Procedures3.tla
* Test procedures translation uni-process algorithm. Unordered channels used
* Parsed correctly
* no model checking errors.

Procedures4.tla
* Test multiple procedures translation. Unordered channels used
* Parsed correctly
* no model checking errors.

ReaderWriterC1.tla
* Unordered channels. Two processes, send and receive actions
* Parsed correctly
* no model checking errors.

ReaderWriterC2.tla
* Unordered channels. Channel send operation inside procedure
* Parsed correctly
* no model checking errors.

ReaderWriterC3.tla
* Unordered channels. One label specification to test c-syntax optimization issue
* Parsed correctly
* no model checking errors.

ReaderWriterC3_1.tla
* One-dimensional Unordered channel. C-syntax two labels in one thread. 
* Parsed correctly
* no model checking errors.

ReaderWriterC4.tla
* One-dimensional FIFO channel. Three channel operations on three threads
* Parsed correctly
* no model checking errors.

ReaderWriterC5.tla
* One-dimensional unordered channel. The first process with one thread - three labels and three channel operations. The second process without subprocess - one label one channel operation.
* Parsed correctly
* no model checking errors.

ReaderWriterC6.tla
* Two-dimensional unordered channel. The first process with three threads - each thread with one label and one channel operation.
* Parsed correctly
* no model checking errors.

ReaderWriterC7.tla
* One-dimensional unordered channel. A process with two threads - each thread with one label and one channel operation.
* Parsed correctly
* no model checking errors.

ReaderWriterC8.tla
* FIFO channel. A process with three threads calling three macros with and without parameters. Macros have channel operations inside.
* Parsed correctly
* no model checking errors.

ReaderWriterC9.tla
* One-dimensional unordered channel. A process with two threads calling macros with and without parameters. Macros have channel operations inside.
* Parsed correctly
* no model checking errors.

ReaderWriterC10.tla
* One-dimensional FIFO channel. A process with two threads. The second thread only calls macros with parameters. Macros have channel operations inside.
* Parsed correctly
* no model checking errors.

ReaderWriterC11.tla
* One-dimensional FIFO channel. Macros parameter handling test. 
* Parsed correctly
* no model checking errors.

ReaderWriterC12.tla
* One-dimensional FIFO channel. Macros without parameter only.
* Parsed correctly
* no model checking errors.

ReaderWriterC13.tla
* One-dimensional FIFO channel. Multicast used inside macro
* Parsed correctly
* no model checking errors

ReaderWriterC14.tla
* FIFO channel and a global variable both modified in macro. Macros with parameter for both variables.
* Parsed correctly
* no model checking errors.

ReaderWriterC15.tla
* Two-dimensional FIFO channel . Macros with parameter.
* Parsed correctly
* no model checking errors.


ReaderWriterC16.tla
* Two-dimensional FIFO channel and one global variable, one process local variable. Macros with parameters.
* Parsed correctly
* no model checking errors.

ReaderWriterC17.tla
* FIFO channel and one process local variable. receive channel call without macro params.
* Parsed correctly
* no model checking errors.

ReaderWriterP1.tla
* FIFO channel and one global variable. P-syntax subprocess test
* Parsed correctly
* no model checking errors.

ReaderWriterP2.tla
* FIFO channel and one process local variable. P-syntax subprocess test
* Parsed correctly
* no model checking errors.

ReaderWriterP3.tla
* One-dimensional Unordered channel and one process local variable. P-syntax subprocess test
* Parsed correctly
* no model checking errors.

ReaderWriterP4.tla
* One-dimensional FIFO channel and one global variable. Two processes - one with subprocess and one without.
* Parsed correctly
* no model checking errors.

ReaderWriterP5.tla
* One-dimensional Unordered channel and one global variable. Two processes - one with one label, another with two labels.
* Parsed correctly
* no model checking errors.

ReaderWriterP6.tla
* One-dimensional Unordered channel and two process local variable. One process with three subprocesses. 
* Parsed correctly
* no model checking errors.

ReaderWriterP7.tla
* Two-dimensional Unordered channel and one global variable. One process with two subprocesses. 
* Parsed correctly
* no model checking errors.

ReaderWriterP8.tla
* One-dimensional Unordered channel. Macro with a single parameter.
* Parsed correctly
* no model checking errors.


RecursiveProcedure1.tla
* Process local vars inside procedures. Two process-local vars
* Parsed correctly
* no model checking errors.

RecursiveProcedure2.tla
* Process local vars inside procedures. Three process-local vars
* Parsed correctly
* no model checking errors.


SequentialClearC.tla
* Sequential algorithm.  unordered channels.
* Parsed correctly
* no model checking errors.

SequentialClearC2.tla
* Sequential algorithm. fifo channels.
* Parsed correctly
* no model checking errors.

SequentialClearP.tla
* Sequential algorithm. unordered channels.
* Parsed correctly
* no model checking errors.

SequentialClearP2.tla
* Sequential algorithm. fifo channels.
* Parsed correctly
* no model checking errors.

SequentialSendC.tla
* Sequential algorithm. one-dimensional channel channels.
* Parsed correctly
* no model checking errors

SequentialSendP.tla
* Sequential algorithm. one-dimensional channel channels. Several operations under a single label
* Parsed correctly
* no model checking errors.


SingleProcessSendC.tla
* Single process (c = 1) without subprocesses. unordered channels
* Parsed correctly
* no model checking errors.


SingleProcessSendP.tla
* Single process (c = 1) without subprocesses. fifo channels
* Parsed correctly
* no model checking errors.

logicalClock1.tla
* Unordered channels. lamport timestamps sendWithClock and receiveWithClock
* Parsed correctly
* no model checking errors.

LogicalClock.tla
* Lamport mutex with built-in lamport clocks feature
* Parsed correctly
* no model checking errors.




=========================================================================================================

Clash.tla
* Parsed
* no model checking errors.

FreshVars.tla
* Parsed
* no model checking errors.

NoProcessEmptyBodyP.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

NoProcessNoLabelC.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

 NoProcessNoLabelP.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

 NoProcessOneLabelC.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

 NoProcessOneLabelP.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

 NoProcessTwoLabelsC.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

 NoProcessTwoLabelsP.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

 OneProcessEmptyThreadP.tla
* NOT PARSED

OneProcessMultiThread1C.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

OneProcessMultiThread1P.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

OneProcessMultiThread1aC.tla
* Parsed
* no model checking errors.

OneProcessMultiThread2C.tla
* Parsed
* no model checking errors.


OneProcessOneThread1C.tla
* Parsed
* no model checking errors.

OneProcessOneThread1P.tla
* Parsed
* no model checking errors.


OneProcessOneThread1sC.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

OneProcessOneThread2C.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(Next). The toolbox does not generate this

OneProcessOneThread2nC.tla
* Parsed
* no model checking errors.
* generated extra /\ WF_vars(pid(self)). The toolbox does not generate this

Procedures1p1t.tla
* Parsed
* no model checking errors.

Procedures1p2t.tla
* Parsed
* no model checking errors.

ProceduresRec.tla
* Parsed
* MODEL CHECKING ERROR. RELATED TO PROCESS LOCAL VARIABLES.

TwoProcessesOneThread2C.tla
* Parsed
* generated extra /\ WF_vars(pid2). The toolbox does not generate this

TwoProcessesOneThread2sC.tla
* NOT PARSED. SubProcSet shows an error
	DM comment: I think this is because there are different process instantions such as 
						pid3 = 2 and pid2 = "IDone".
				Having integer and string - different types contradicts to PlusCal theory.
* generated extra WF_vars(pid1(self)), /\ WF_vars(pid2) and /\ WF_vars(pid3). The toolbox does not generate this

VarAndChannelDecls1C.tla
* NOT Parsed correctly
	DM comment: Due to fifs[self][1] must be fifs[1]


Question:
/\ network = [n0 \in Nodes, n1 \in Nodes |-> {}]
or
/\ /\ network = [n0 \in Nodes |-> [n1 \in Nodes |-> {}]]


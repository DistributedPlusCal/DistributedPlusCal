

To compile the example to TLA+ execute

```
java -cp ../dist/tla2tools.jar pcal.trans [-label] <path to algo>/<algo>
```

## Simple examples with threads
- [ ]
  [ThreadsC.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsC.tla):
  simple example with single- and multi-threaded processes 

To compile the example to TLA+ execute
```
java -cp ../dist/tla2tools.jar pcal.trans ThreadsC.tla
```

- [ ]
  [ThreadsP.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsP.tla):
  same as ThreadsC.tla but with P-syntax

- [ ]
  [ThreadsMacro.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsMacro.tla):
  simple example with threads using a macro 

- [ ]
  [ThreadsProcedure.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsProcedure.tla):
  simple example with threads using a procedure 

- [ ]
  [ThreadsFairness.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ThreadsFairness.tla):
  simple example with threads using various fairness conditions


## Channels

- [ ]
  [ChannelsC.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ChannelsC.tla):
  a process with two threads, each of them sending a message on (one
  of the channels of) a 1-dimensional channel; messages are received
  by another process.
	
- [ ]
  [ChannelsMulticast.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ChannelsMulticast.tla):
  a process which multicasts messages on (the channels of) a
  1-dimensional channel; messages are received by another process.
	
- [ ]
  [ChannelsBroadcast.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/ChannelsBroadcast.tla):
  a process broadcasts a message (the channels of) a 1-dimensional
  channel; messages are received by another process.

## Mutual exclusion algorithm
- [ ]
  [LamportMutex.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/LamportMutex.tla):
  Lamport's distributed mutual-exclusion algorithm. To model-check use
  [MCLamportMutex.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/MCLamportMutex.tla)
	after setting up the configuration in 
  [MCLamportMutex.cfg](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/MCLamportMutex.cfg)

## Paxos consensus algorithm
- [ ]
  [Paxos.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/Paxos.tla):
	The Paxos consensus algorithm. To model-check use
  [MCPaxos.tla](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/MCPaxos.tla)
	after setting up the configuration in 
  [MCPaxos.cfg](https://github.com/DistributedPlusCal/DistributedPlusCal/blob/master/tlatools/examples-distpcal/MCPaxos.cfg)
